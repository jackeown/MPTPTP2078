%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:03 EST 2020

% Result     : Theorem 7.44s
% Output     : CNFRefutation 7.44s
% Verified   : 
% Statistics : Number of formulae       :  359 (32513 expanded)
%              Number of clauses        :  266 (9200 expanded)
%              Number of leaves         :   27 (6866 expanded)
%              Depth                    :   44
%              Number of atoms          : 1329 (226224 expanded)
%              Number of equality atoms :  650 (46676 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

fof(f54,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f66,plain,(
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
    inference(nnf_transformation,[],[f55])).

fof(f67,plain,(
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
    inference(flattening,[],[f66])).

fof(f69,plain,(
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
     => ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,sK3)
          | ~ m1_pre_topc(sK3,X0)
          | ~ v1_tsep_1(sK3,X0) )
        & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,sK3)
          | ( m1_pre_topc(sK3,X0)
            & v1_tsep_1(sK3,X0) ) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,
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
          ( ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,X1)
            | ~ m1_pre_topc(X1,sK2)
            | ~ v1_tsep_1(X1,sK2) )
          & ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,X1)
            | ( m1_pre_topc(X1,sK2)
              & v1_tsep_1(X1,sK2) ) )
          & m1_pre_topc(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,
    ( ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
      | ~ m1_pre_topc(sK3,sK2)
      | ~ v1_tsep_1(sK3,sK2) )
    & ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
      | ( m1_pre_topc(sK3,sK2)
        & v1_tsep_1(sK3,sK2) ) )
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f67,f69,f68])).

fof(f107,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f70])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f102,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f100,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f75,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f72,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f99,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f109,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f70])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f52])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f106,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f70])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f76,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f101,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f97,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & v1_pre_topc(X2) )
             => ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => k6_tmap_1(X0,X3) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( k6_tmap_1(X0,X3) = X2
                      | u1_struct_0(X1) != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f57])).

fof(f59,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK0(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK0(X0,X1,X2)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ( k6_tmap_1(X0,sK0(X0,X1,X2)) != X2
                    & u1_struct_0(X1) = sK0(X0,X1,X2)
                    & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f58,f59])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( k6_tmap_1(X0,X4) = X2
      | u1_struct_0(X1) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( k6_tmap_1(X0,u1_struct_0(X1)) = X2
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f82])).

fof(f114,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f113])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f93,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f105,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f70])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f90,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f98,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f62,plain,(
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
    inference(rectify,[],[f61])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK1(X0,X1),X0)
        & u1_struct_0(X1) = sK1(X0,X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ( ~ v3_pre_topc(sK1(X0,X1),X0)
                & u1_struct_0(X1) = sK1(X0,X1)
                & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f62,f63])).

fof(f86,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f115,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f86])).

fof(f110,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
    | v1_tsep_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f70])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X1,u1_pre_topc(X0))
              | u1_pre_topc(X0) != k5_tmap_1(X0,X1) )
            & ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f95,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | u1_pre_topc(X0) != k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(sK1(X0,X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f112,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ v1_tsep_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f70])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | u1_struct_0(X1) = sK1(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_39,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_6260,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_31,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_6264,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_28,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_6267,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_6286,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7410,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6267,c_6286])).

cnf(c_7508,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6264,c_7410])).

cnf(c_1,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_6289,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_10728,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7508,c_6289])).

cnf(c_6691,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_6692,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6691])).

cnf(c_29,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_6266,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_7242,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6264,c_6266])).

cnf(c_29031,plain,
    ( l1_pre_topc(X0) != iProver_top
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10728,c_6692,c_7242,c_7508])).

cnf(c_29032,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_29031])).

cnf(c_29040,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(superposition,[status(thm)],[c_6260,c_29032])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X0
    | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_6282,plain,
    ( X0 = X1
    | g1_pre_topc(X2,X0) != g1_pre_topc(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_29343,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_29040,c_6282])).

cnf(c_44,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_54,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_56,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_54])).

cnf(c_63,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_65,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_63])).

cnf(c_7286,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_7287,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7286])).

cnf(c_7289,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7287])).

cnf(c_10,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_6280,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_7434,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6264,c_6280])).

cnf(c_12536,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7434,c_7508])).

cnf(c_12537,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_12536])).

cnf(c_37,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_6262,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_33,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_6263,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X2,X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_8782,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6262,c_6263])).

cnf(c_40,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_43,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_9048,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8782,c_43,c_44])).

cnf(c_12565,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK2) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_12537,c_9048])).

cnf(c_6777,plain,
    ( l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6262,c_6286])).

cnf(c_13072,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12565,c_44,c_6777])).

cnf(c_7509,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6262,c_7410])).

cnf(c_7642,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7509,c_44])).

cnf(c_7647,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7642,c_6289])).

cnf(c_7243,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6262,c_6266])).

cnf(c_7650,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7647,c_44,c_7243])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_6281,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_7659,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = X0
    | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7650,c_6281])).

cnf(c_8112,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(sK3)
    | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_7659])).

cnf(c_5,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_6285,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7658,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7650,c_6281])).

cnf(c_7820,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(sK3)
    | m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_7658])).

cnf(c_8186,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(sK3)
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6285,c_7820])).

cnf(c_8283,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8112,c_44,c_6777,c_8186])).

cnf(c_30,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_6265,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_8315,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8283,c_6265])).

cnf(c_13085,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_13072,c_8315])).

cnf(c_46,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_7025,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_7026,plain,
    ( m1_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7025])).

cnf(c_13124,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13085,c_44,c_46,c_7026])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_6268,plain,
    ( u1_struct_0(k6_tmap_1(X0,X1)) = u1_struct_0(X0)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_13132,plain,
    ( u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))) = u1_struct_0(sK2)
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_13124,c_6268])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v1_pre_topc(k8_tmap_1(X1,X0))
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_22,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_20,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_270,plain,
    ( ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_30,c_22,c_21,c_20])).

cnf(c_271,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(renaming,[status(thm)],[c_270])).

cnf(c_6257,plain,
    ( k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_271])).

cnf(c_9555,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3)
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6262,c_6257])).

cnf(c_41,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_7971,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_271])).

cnf(c_9936,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9555,c_41,c_40,c_39,c_37,c_7971])).

cnf(c_13160,plain,
    ( u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2)
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13132,c_9936])).

cnf(c_42,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_13303,plain,
    ( u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13160,c_42,c_43,c_44])).

cnf(c_13354,plain,
    ( m1_pre_topc(X0,k8_tmap_1(sK2,sK3)) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13303,c_6265])).

cnf(c_9252,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | l1_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_9253,plain,
    ( m1_pre_topc(sK3,sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9252])).

cnf(c_14555,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_pre_topc(X0,k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13354,c_42,c_43,c_44,c_46,c_9253])).

cnf(c_14556,plain,
    ( m1_pre_topc(X0,k8_tmap_1(sK2,sK3)) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_14555])).

cnf(c_14564,plain,
    ( m1_pre_topc(k8_tmap_1(sK2,sK3),k8_tmap_1(sK2,sK3)) != iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_13303,c_14556])).

cnf(c_57,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_59,plain,
    ( m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_57])).

cnf(c_14845,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14564,c_44,c_56,c_59])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X0)) = k6_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_6276,plain,
    ( g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_14851,plain,
    ( g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,u1_struct_0(sK2))) = k6_tmap_1(sK2,u1_struct_0(sK2))
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_14845,c_6276])).

cnf(c_6259,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_9554,plain,
    ( k6_tmap_1(X0,u1_struct_0(X0)) = k8_tmap_1(X0,X0)
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6264,c_6257])).

cnf(c_12807,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK2)) = k8_tmap_1(sK2,sK2)
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6259,c_9554])).

cnf(c_55,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_58,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_82,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | v1_pre_topc(k8_tmap_1(sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_85,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | v2_pre_topc(k8_tmap_1(sK2,sK2))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_88,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | l1_pre_topc(k8_tmap_1(sK2,sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_106,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(k8_tmap_1(sK2,sK2))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(k8_tmap_1(sK2,sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v1_pre_topc(k8_tmap_1(sK2,sK2))
    | k6_tmap_1(sK2,u1_struct_0(sK2)) = k8_tmap_1(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_12975,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK2)) = k8_tmap_1(sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12807,c_41,c_40,c_39,c_55,c_58,c_82,c_85,c_88,c_106])).

cnf(c_14899,plain,
    ( g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,u1_struct_0(sK2))) = k8_tmap_1(sK2,sK2)
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14851,c_12975])).

cnf(c_15379,plain,
    ( g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,u1_struct_0(sK2))) = k8_tmap_1(sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14899,c_42,c_43,c_44])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_6269,plain,
    ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_14852,plain,
    ( u1_pre_topc(k6_tmap_1(sK2,u1_struct_0(sK2))) = k5_tmap_1(sK2,u1_struct_0(sK2))
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_14845,c_6269])).

cnf(c_14890,plain,
    ( k5_tmap_1(sK2,u1_struct_0(sK2)) = u1_pre_topc(k8_tmap_1(sK2,sK2))
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14852,c_12975])).

cnf(c_15316,plain,
    ( k5_tmap_1(sK2,u1_struct_0(sK2)) = u1_pre_topc(k8_tmap_1(sK2,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14890,c_42,c_43,c_44])).

cnf(c_15381,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(k8_tmap_1(sK2,sK2))) = k8_tmap_1(sK2,sK2) ),
    inference(light_normalisation,[status(thm)],[c_15379,c_15316])).

cnf(c_15387,plain,
    ( g1_pre_topc(X0,X1) != k8_tmap_1(sK2,sK2)
    | u1_struct_0(sK2) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_15381,c_6281])).

cnf(c_87,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(k8_tmap_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_89,plain,
    ( m1_pre_topc(sK2,sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK2)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_87])).

cnf(c_14853,plain,
    ( u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))) = u1_struct_0(sK2)
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_14845,c_6268])).

cnf(c_14881,plain,
    ( u1_struct_0(k8_tmap_1(sK2,sK2)) = u1_struct_0(sK2)
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14853,c_12975])).

cnf(c_14998,plain,
    ( u1_struct_0(k8_tmap_1(sK2,sK2)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14881,c_42,c_43,c_44])).

cnf(c_15029,plain,
    ( m1_subset_1(u1_pre_topc(k8_tmap_1(sK2,sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14998,c_6285])).

cnf(c_15388,plain,
    ( g1_pre_topc(X0,X1) != k8_tmap_1(sK2,sK2)
    | u1_struct_0(sK2) = X0
    | m1_subset_1(u1_pre_topc(k8_tmap_1(sK2,sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_15381,c_6281])).

cnf(c_15805,plain,
    ( u1_struct_0(sK2) = X0
    | g1_pre_topc(X0,X1) != k8_tmap_1(sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15387,c_42,c_43,c_44,c_56,c_89,c_15029,c_15388])).

cnf(c_15806,plain,
    ( g1_pre_topc(X0,X1) != k8_tmap_1(sK2,sK2)
    | u1_struct_0(sK2) = X0 ),
    inference(renaming,[status(thm)],[c_15805])).

cnf(c_29333,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK2)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_29040,c_15806])).

cnf(c_61,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_64,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_129,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_6693,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_6691])).

cnf(c_7288,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2)
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_7286])).

cnf(c_6969,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | X2 = u1_struct_0(X1)
    | g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(X1),X0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_7229,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | X1 = u1_struct_0(X0)
    | g1_pre_topc(X1,X2) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(instantiation,[status(thm)],[c_6969])).

cnf(c_8575,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_7229])).

cnf(c_8577,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_8575])).

cnf(c_29746,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_29333,c_39,c_55,c_61,c_64,c_129,c_6693,c_7288,c_8577])).

cnf(c_29804,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_29746,c_6285])).

cnf(c_29750,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(demodulation,[status(thm)],[c_29746,c_29040])).

cnf(c_30228,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = X1
    | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_29750,c_6282])).

cnf(c_31026,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = X1
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_29343,c_44,c_56,c_65,c_7289,c_29804,c_30228])).

cnf(c_31027,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = X1 ),
    inference(renaming,[status(thm)],[c_31026])).

cnf(c_9056,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6267,c_9048])).

cnf(c_9068,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9056,c_44,c_6777])).

cnf(c_9069,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_9068])).

cnf(c_9556,plain,
    ( k6_tmap_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = k8_tmap_1(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | m1_pre_topc(X0,sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9069,c_6257])).

cnf(c_10021,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | k6_tmap_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = k8_tmap_1(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9556,c_42,c_43,c_44])).

cnf(c_10022,plain,
    ( k6_tmap_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = k8_tmap_1(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | m1_pre_topc(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_10021])).

cnf(c_10030,plain,
    ( k6_tmap_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = k8_tmap_1(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6264,c_10022])).

cnf(c_10033,plain,
    ( k8_tmap_1(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k8_tmap_1(sK2,sK3)
    | l1_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10030,c_8283,c_9936])).

cnf(c_10047,plain,
    ( k8_tmap_1(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10033,c_44,c_6777])).

cnf(c_6275,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(k8_tmap_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_10050,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_10047,c_6275])).

cnf(c_10173,plain,
    ( l1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10050,c_42,c_43,c_44,c_46,c_9253])).

cnf(c_10178,plain,
    ( g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3)
    | v1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10173,c_6289])).

cnf(c_6703,plain,
    ( ~ l1_pre_topc(k8_tmap_1(X0,X1))
    | ~ v1_pre_topc(k8_tmap_1(X0,X1))
    | g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X1)),u1_pre_topc(k8_tmap_1(X0,X1))) = k8_tmap_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_7981,plain,
    ( ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ v1_pre_topc(k8_tmap_1(sK2,sK3))
    | g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_6703])).

cnf(c_7982,plain,
    ( g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3)
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
    | v1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7981])).

cnf(c_6273,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_pre_topc(k8_tmap_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_10052,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10047,c_6273])).

cnf(c_10240,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK2) != iProver_top
    | v1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10052,c_42,c_43,c_44])).

cnf(c_10246,plain,
    ( m1_pre_topc(sK3,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6267,c_10240])).

cnf(c_11441,plain,
    ( g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10178,c_42,c_43,c_44,c_46,c_7982,c_9253,c_10246])).

cnf(c_13307,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_13303,c_11441])).

cnf(c_13749,plain,
    ( g1_pre_topc(X0,X1) != k8_tmap_1(sK2,sK3)
    | u1_pre_topc(k8_tmap_1(sK2,sK3)) = X1
    | m1_subset_1(u1_pre_topc(k8_tmap_1(sK2,sK3)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_13307,c_6282])).

cnf(c_13344,plain,
    ( m1_subset_1(u1_pre_topc(k8_tmap_1(sK2,sK3)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13303,c_6285])).

cnf(c_16518,plain,
    ( u1_pre_topc(k8_tmap_1(sK2,sK3)) = X1
    | g1_pre_topc(X0,X1) != k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13749,c_42,c_43,c_44,c_46,c_9253,c_13344])).

cnf(c_16519,plain,
    ( g1_pre_topc(X0,X1) != k8_tmap_1(sK2,sK3)
    | u1_pre_topc(k8_tmap_1(sK2,sK3)) = X1 ),
    inference(renaming,[status(thm)],[c_16518])).

cnf(c_29331,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
    | u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_pre_topc(k8_tmap_1(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_29040,c_16519])).

cnf(c_5561,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_5576,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_5561])).

cnf(c_5562,plain,
    ( X0 != X1
    | u1_pre_topc(X0) = u1_pre_topc(X1) ),
    theory(equality)).

cnf(c_5577,plain,
    ( u1_pre_topc(sK2) = u1_pre_topc(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_5562])).

cnf(c_5557,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_5590,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_5557])).

cnf(c_7559,plain,
    ( k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_5557])).

cnf(c_5558,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_7041,plain,
    ( X0 != X1
    | k8_tmap_1(sK2,sK3) != X1
    | k8_tmap_1(sK2,sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_5558])).

cnf(c_7558,plain,
    ( X0 != k8_tmap_1(sK2,sK3)
    | k8_tmap_1(sK2,sK3) = X0
    | k8_tmap_1(sK2,sK3) != k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_7041])).

cnf(c_7980,plain,
    ( k8_tmap_1(sK2,sK3) != k8_tmap_1(sK2,sK3)
    | k8_tmap_1(sK2,sK3) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3)))
    | g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) != k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_7558])).

cnf(c_5563,plain,
    ( X0 != X1
    | X2 != X3
    | g1_pre_topc(X0,X2) = g1_pre_topc(X1,X3) ),
    theory(equality)).

cnf(c_6864,plain,
    ( X0 != u1_pre_topc(X1)
    | X2 != u1_struct_0(X1)
    | g1_pre_topc(X2,X0) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ),
    inference(instantiation,[status(thm)],[c_5563])).

cnf(c_7137,plain,
    ( X0 != u1_struct_0(X1)
    | g1_pre_topc(X0,u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | u1_pre_topc(X2) != u1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_6864])).

cnf(c_8429,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | u1_pre_topc(X1) != u1_pre_topc(X2)
    | u1_struct_0(X0) != u1_struct_0(X2) ),
    inference(instantiation,[status(thm)],[c_7137])).

cnf(c_8430,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | u1_pre_topc(sK2) != u1_pre_topc(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_8429])).

cnf(c_6839,plain,
    ( k8_tmap_1(sK2,sK3) != X0
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != X0
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_5558])).

cnf(c_10909,plain,
    ( k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(instantiation,[status(thm)],[c_6839])).

cnf(c_10914,plain,
    ( k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_10909])).

cnf(c_10978,plain,
    ( X0 != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | k8_tmap_1(sK2,sK3) = X0
    | k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ),
    inference(instantiation,[status(thm)],[c_7041])).

cnf(c_16866,plain,
    ( X0 != g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3)))
    | k8_tmap_1(sK2,sK3) = X0
    | k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_10978])).

cnf(c_18517,plain,
    ( k8_tmap_1(sK2,sK3) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X1))
    | k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3)))
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_16866])).

cnf(c_18519,plain,
    ( k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3)))
    | k8_tmap_1(sK2,sK3) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_18517])).

cnf(c_18518,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3)))
    | u1_pre_topc(X1) != u1_pre_topc(k8_tmap_1(sK2,sK3))
    | u1_struct_0(X0) != u1_struct_0(k8_tmap_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_8429])).

cnf(c_18520,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3)))
    | u1_pre_topc(sK2) != u1_pre_topc(k8_tmap_1(sK2,sK3))
    | u1_struct_0(sK2) != u1_struct_0(k8_tmap_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_18518])).

cnf(c_18,plain,
    ( ~ v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_260,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_30])).

cnf(c_261,plain,
    ( ~ v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_260])).

cnf(c_36,negated_conjecture,
    ( v1_tsep_1(sK3,sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_338,plain,
    ( v1_tsep_1(sK3,sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
    inference(prop_impl,[status(thm)],[c_36])).

cnf(c_726,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_261,c_338])).

cnf(c_727,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | v3_pre_topc(u1_struct_0(sK3),sK2)
    | ~ l1_pre_topc(sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_726])).

cnf(c_729,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_727,c_39,c_37])).

cnf(c_6251,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
    | v3_pre_topc(u1_struct_0(sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_729])).

cnf(c_3,plain,
    ( r2_hidden(X0,u1_pre_topc(X1))
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_6287,plain,
    ( r2_hidden(X0,u1_pre_topc(X1)) = iProver_top
    | v3_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_13135,plain,
    ( r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) = iProver_top
    | v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_13124,c_6287])).

cnf(c_6734,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_6894,plain,
    ( r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2))
    | ~ v3_pre_topc(u1_struct_0(sK3),sK2)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_6734])).

cnf(c_6895,plain,
    ( r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) = iProver_top
    | v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6894])).

cnf(c_14115,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top
    | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13135,c_44,c_46,c_6895,c_7026])).

cnf(c_14116,plain,
    ( r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) = iProver_top
    | v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_14115])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) = u1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_6270,plain,
    ( k5_tmap_1(X0,X1) = u1_pre_topc(X0)
    | r2_hidden(X1,u1_pre_topc(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_13129,plain,
    ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(sK2)
    | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_13124,c_6270])).

cnf(c_7090,plain,
    ( ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_10286,plain,
    ( ~ r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_7090])).

cnf(c_10287,plain,
    ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(sK2)
    | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10286])).

cnf(c_23812,plain,
    ( r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top
    | k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13129,c_42,c_43,c_44,c_46,c_7026,c_10287])).

cnf(c_23813,plain,
    ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(sK2)
    | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_23812])).

cnf(c_13131,plain,
    ( u1_pre_topc(k6_tmap_1(sK2,u1_struct_0(sK3))) = k5_tmap_1(sK2,u1_struct_0(sK3))
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_13124,c_6269])).

cnf(c_13169,plain,
    ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK2,sK3))
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13131,c_9936])).

cnf(c_13625,plain,
    ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13169,c_42,c_43,c_44])).

cnf(c_23816,plain,
    ( u1_pre_topc(k8_tmap_1(sK2,sK3)) = u1_pre_topc(sK2)
    | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_23813,c_13625])).

cnf(c_23821,plain,
    ( u1_pre_topc(k8_tmap_1(sK2,sK3)) = u1_pre_topc(sK2)
    | v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_14116,c_23816])).

cnf(c_24549,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
    | u1_pre_topc(k8_tmap_1(sK2,sK3)) = u1_pre_topc(sK2) ),
    inference(superposition,[status(thm)],[c_6251,c_23821])).

cnf(c_6964,plain,
    ( X0 != X1
    | X0 = u1_pre_topc(X2)
    | u1_pre_topc(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_5558])).

cnf(c_7071,plain,
    ( X0 != u1_pre_topc(X1)
    | X0 = u1_pre_topc(X2)
    | u1_pre_topc(X2) != u1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_6964])).

cnf(c_7639,plain,
    ( u1_pre_topc(X0) != u1_pre_topc(X1)
    | u1_pre_topc(X2) != u1_pre_topc(X1)
    | u1_pre_topc(X0) = u1_pre_topc(X2) ),
    inference(instantiation,[status(thm)],[c_7071])).

cnf(c_29180,plain,
    ( u1_pre_topc(X0) != u1_pre_topc(X1)
    | u1_pre_topc(X0) = u1_pre_topc(k8_tmap_1(sK2,sK3))
    | u1_pre_topc(k8_tmap_1(sK2,sK3)) != u1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_7639])).

cnf(c_29181,plain,
    ( u1_pre_topc(k8_tmap_1(sK2,sK3)) != u1_pre_topc(sK2)
    | u1_pre_topc(sK2) = u1_pre_topc(k8_tmap_1(sK2,sK3))
    | u1_pre_topc(sK2) != u1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_29180])).

cnf(c_6991,plain,
    ( X0 != X1
    | X0 = u1_struct_0(X2)
    | u1_struct_0(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_5558])).

cnf(c_7087,plain,
    ( X0 != u1_struct_0(X1)
    | X0 = u1_struct_0(X2)
    | u1_struct_0(X2) != u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_6991])).

cnf(c_7713,plain,
    ( u1_struct_0(X0) != u1_struct_0(X1)
    | u1_struct_0(X2) != u1_struct_0(X1)
    | u1_struct_0(X0) = u1_struct_0(X2) ),
    inference(instantiation,[status(thm)],[c_7087])).

cnf(c_30290,plain,
    ( u1_struct_0(X0) != u1_struct_0(X1)
    | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(sK2,sK3))
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_7713])).

cnf(c_30291,plain,
    ( u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(sK2)
    | u1_struct_0(sK2) = u1_struct_0(k8_tmap_1(sK2,sK3))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_30290])).

cnf(c_30469,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_pre_topc(k8_tmap_1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_29331,c_42,c_43,c_44,c_46,c_5576,c_5577,c_5590,c_7559,c_7980,c_7982,c_8430,c_9253,c_10246,c_10914,c_13160,c_18519,c_18520,c_24549,c_29181,c_30291])).

cnf(c_31029,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(k8_tmap_1(sK2,sK3)) = X1 ),
    inference(demodulation,[status(thm)],[c_31027,c_30469])).

cnf(c_31035,plain,
    ( u1_pre_topc(k8_tmap_1(sK2,sK3)) = u1_pre_topc(sK2) ),
    inference(equality_resolution,[status(thm)],[c_31029])).

cnf(c_30472,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(k8_tmap_1(sK2,sK3))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(demodulation,[status(thm)],[c_30469,c_29750])).

cnf(c_30473,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
    inference(light_normalisation,[status(thm)],[c_30472,c_13307])).

cnf(c_24,plain,
    ( r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) != u1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_6271,plain,
    ( k5_tmap_1(X0,X1) != u1_pre_topc(X0)
    | r2_hidden(X1,u1_pre_topc(X0)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_13628,plain,
    ( u1_pre_topc(k8_tmap_1(sK2,sK3)) != u1_pre_topc(sK2)
    | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_13625,c_6271])).

cnf(c_19375,plain,
    ( u1_pre_topc(k8_tmap_1(sK2,sK3)) != u1_pre_topc(sK2)
    | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13628,c_42,c_43,c_44,c_46,c_7026])).

cnf(c_19377,plain,
    ( r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2))
    | u1_pre_topc(k8_tmap_1(sK2,sK3)) != u1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_19375])).

cnf(c_5566,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_6756,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X2),X3)
    | X1 != X3
    | X0 != u1_struct_0(X2) ),
    inference(instantiation,[status(thm)],[c_5566])).

cnf(c_7107,plain,
    ( v3_pre_topc(sK1(X0,X1),X2)
    | ~ v3_pre_topc(u1_struct_0(X1),X3)
    | X2 != X3
    | sK1(X0,X1) != u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_6756])).

cnf(c_10708,plain,
    ( v3_pre_topc(sK1(X0,sK3),X1)
    | ~ v3_pre_topc(u1_struct_0(sK3),sK2)
    | X1 != sK2
    | sK1(X0,sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_7107])).

cnf(c_10710,plain,
    ( v3_pre_topc(sK1(sK2,sK3),sK2)
    | ~ v3_pre_topc(u1_struct_0(sK3),sK2)
    | sK1(sK2,sK3) != u1_struct_0(sK3)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_10708])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_7091,plain,
    ( ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_7807,plain,
    ( ~ r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2))
    | v3_pre_topc(u1_struct_0(sK3),sK2)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_7091])).

cnf(c_15,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v3_pre_topc(sK1(X1,X0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_34,negated_conjecture,
    ( ~ v1_tsep_1(sK3,sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_336,plain,
    ( ~ v1_tsep_1(sK3,sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
    inference(prop_impl,[status(thm)],[c_37,c_34])).

cnf(c_712,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v3_pre_topc(sK1(X1,X0),X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_336])).

cnf(c_713,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ v3_pre_topc(sK1(sK2,sK3),sK2)
    | ~ l1_pre_topc(sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_712])).

cnf(c_715,plain,
    ( ~ v3_pre_topc(sK1(sK2,sK3),sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_713,c_39,c_37])).

cnf(c_16,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_701,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X0) = u1_struct_0(X0)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_336])).

cnf(c_702,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | sK1(sK2,sK3) = u1_struct_0(sK3)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_701])).

cnf(c_704,plain,
    ( sK1(sK2,sK3) = u1_struct_0(sK3)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_702,c_39,c_37])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_31035,c_30473,c_19377,c_10710,c_7807,c_7025,c_5590,c_715,c_704,c_37,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:34:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.44/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.44/1.50  
% 7.44/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.44/1.50  
% 7.44/1.50  ------  iProver source info
% 7.44/1.50  
% 7.44/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.44/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.44/1.50  git: non_committed_changes: false
% 7.44/1.50  git: last_make_outside_of_git: false
% 7.44/1.50  
% 7.44/1.50  ------ 
% 7.44/1.50  
% 7.44/1.50  ------ Input Options
% 7.44/1.50  
% 7.44/1.50  --out_options                           all
% 7.44/1.50  --tptp_safe_out                         true
% 7.44/1.50  --problem_path                          ""
% 7.44/1.50  --include_path                          ""
% 7.44/1.50  --clausifier                            res/vclausify_rel
% 7.44/1.50  --clausifier_options                    --mode clausify
% 7.44/1.50  --stdin                                 false
% 7.44/1.50  --stats_out                             all
% 7.44/1.50  
% 7.44/1.50  ------ General Options
% 7.44/1.50  
% 7.44/1.50  --fof                                   false
% 7.44/1.50  --time_out_real                         305.
% 7.44/1.50  --time_out_virtual                      -1.
% 7.44/1.50  --symbol_type_check                     false
% 7.44/1.50  --clausify_out                          false
% 7.44/1.50  --sig_cnt_out                           false
% 7.44/1.50  --trig_cnt_out                          false
% 7.44/1.50  --trig_cnt_out_tolerance                1.
% 7.44/1.50  --trig_cnt_out_sk_spl                   false
% 7.44/1.50  --abstr_cl_out                          false
% 7.44/1.50  
% 7.44/1.50  ------ Global Options
% 7.44/1.50  
% 7.44/1.50  --schedule                              default
% 7.44/1.50  --add_important_lit                     false
% 7.44/1.50  --prop_solver_per_cl                    1000
% 7.44/1.50  --min_unsat_core                        false
% 7.44/1.50  --soft_assumptions                      false
% 7.44/1.50  --soft_lemma_size                       3
% 7.44/1.50  --prop_impl_unit_size                   0
% 7.44/1.50  --prop_impl_unit                        []
% 7.44/1.50  --share_sel_clauses                     true
% 7.44/1.50  --reset_solvers                         false
% 7.44/1.50  --bc_imp_inh                            [conj_cone]
% 7.44/1.50  --conj_cone_tolerance                   3.
% 7.44/1.50  --extra_neg_conj                        none
% 7.44/1.50  --large_theory_mode                     true
% 7.44/1.50  --prolific_symb_bound                   200
% 7.44/1.50  --lt_threshold                          2000
% 7.44/1.50  --clause_weak_htbl                      true
% 7.44/1.50  --gc_record_bc_elim                     false
% 7.44/1.50  
% 7.44/1.50  ------ Preprocessing Options
% 7.44/1.50  
% 7.44/1.50  --preprocessing_flag                    true
% 7.44/1.50  --time_out_prep_mult                    0.1
% 7.44/1.50  --splitting_mode                        input
% 7.44/1.50  --splitting_grd                         true
% 7.44/1.50  --splitting_cvd                         false
% 7.44/1.50  --splitting_cvd_svl                     false
% 7.44/1.50  --splitting_nvd                         32
% 7.44/1.50  --sub_typing                            true
% 7.44/1.50  --prep_gs_sim                           true
% 7.44/1.50  --prep_unflatten                        true
% 7.44/1.50  --prep_res_sim                          true
% 7.44/1.50  --prep_upred                            true
% 7.44/1.50  --prep_sem_filter                       exhaustive
% 7.44/1.50  --prep_sem_filter_out                   false
% 7.44/1.50  --pred_elim                             true
% 7.44/1.50  --res_sim_input                         true
% 7.44/1.50  --eq_ax_congr_red                       true
% 7.44/1.50  --pure_diseq_elim                       true
% 7.44/1.50  --brand_transform                       false
% 7.44/1.50  --non_eq_to_eq                          false
% 7.44/1.50  --prep_def_merge                        true
% 7.44/1.50  --prep_def_merge_prop_impl              false
% 7.44/1.50  --prep_def_merge_mbd                    true
% 7.44/1.50  --prep_def_merge_tr_red                 false
% 7.44/1.50  --prep_def_merge_tr_cl                  false
% 7.44/1.50  --smt_preprocessing                     true
% 7.44/1.50  --smt_ac_axioms                         fast
% 7.44/1.50  --preprocessed_out                      false
% 7.44/1.50  --preprocessed_stats                    false
% 7.44/1.50  
% 7.44/1.50  ------ Abstraction refinement Options
% 7.44/1.50  
% 7.44/1.50  --abstr_ref                             []
% 7.44/1.50  --abstr_ref_prep                        false
% 7.44/1.50  --abstr_ref_until_sat                   false
% 7.44/1.50  --abstr_ref_sig_restrict                funpre
% 7.44/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.44/1.50  --abstr_ref_under                       []
% 7.44/1.50  
% 7.44/1.50  ------ SAT Options
% 7.44/1.50  
% 7.44/1.50  --sat_mode                              false
% 7.44/1.50  --sat_fm_restart_options                ""
% 7.44/1.50  --sat_gr_def                            false
% 7.44/1.50  --sat_epr_types                         true
% 7.44/1.50  --sat_non_cyclic_types                  false
% 7.44/1.50  --sat_finite_models                     false
% 7.44/1.50  --sat_fm_lemmas                         false
% 7.44/1.50  --sat_fm_prep                           false
% 7.44/1.50  --sat_fm_uc_incr                        true
% 7.44/1.50  --sat_out_model                         small
% 7.44/1.50  --sat_out_clauses                       false
% 7.44/1.50  
% 7.44/1.50  ------ QBF Options
% 7.44/1.50  
% 7.44/1.50  --qbf_mode                              false
% 7.44/1.50  --qbf_elim_univ                         false
% 7.44/1.50  --qbf_dom_inst                          none
% 7.44/1.50  --qbf_dom_pre_inst                      false
% 7.44/1.50  --qbf_sk_in                             false
% 7.44/1.50  --qbf_pred_elim                         true
% 7.44/1.50  --qbf_split                             512
% 7.44/1.50  
% 7.44/1.50  ------ BMC1 Options
% 7.44/1.50  
% 7.44/1.50  --bmc1_incremental                      false
% 7.44/1.50  --bmc1_axioms                           reachable_all
% 7.44/1.50  --bmc1_min_bound                        0
% 7.44/1.50  --bmc1_max_bound                        -1
% 7.44/1.50  --bmc1_max_bound_default                -1
% 7.44/1.50  --bmc1_symbol_reachability              true
% 7.44/1.50  --bmc1_property_lemmas                  false
% 7.44/1.50  --bmc1_k_induction                      false
% 7.44/1.50  --bmc1_non_equiv_states                 false
% 7.44/1.50  --bmc1_deadlock                         false
% 7.44/1.50  --bmc1_ucm                              false
% 7.44/1.50  --bmc1_add_unsat_core                   none
% 7.44/1.50  --bmc1_unsat_core_children              false
% 7.44/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.44/1.50  --bmc1_out_stat                         full
% 7.44/1.50  --bmc1_ground_init                      false
% 7.44/1.50  --bmc1_pre_inst_next_state              false
% 7.44/1.50  --bmc1_pre_inst_state                   false
% 7.44/1.50  --bmc1_pre_inst_reach_state             false
% 7.44/1.50  --bmc1_out_unsat_core                   false
% 7.44/1.50  --bmc1_aig_witness_out                  false
% 7.44/1.50  --bmc1_verbose                          false
% 7.44/1.50  --bmc1_dump_clauses_tptp                false
% 7.44/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.44/1.50  --bmc1_dump_file                        -
% 7.44/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.44/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.44/1.50  --bmc1_ucm_extend_mode                  1
% 7.44/1.50  --bmc1_ucm_init_mode                    2
% 7.44/1.50  --bmc1_ucm_cone_mode                    none
% 7.44/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.44/1.50  --bmc1_ucm_relax_model                  4
% 7.44/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.44/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.44/1.50  --bmc1_ucm_layered_model                none
% 7.44/1.50  --bmc1_ucm_max_lemma_size               10
% 7.44/1.50  
% 7.44/1.50  ------ AIG Options
% 7.44/1.50  
% 7.44/1.50  --aig_mode                              false
% 7.44/1.50  
% 7.44/1.50  ------ Instantiation Options
% 7.44/1.50  
% 7.44/1.50  --instantiation_flag                    true
% 7.44/1.50  --inst_sos_flag                         false
% 7.44/1.50  --inst_sos_phase                        true
% 7.44/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.44/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.44/1.50  --inst_lit_sel_side                     num_symb
% 7.44/1.50  --inst_solver_per_active                1400
% 7.44/1.50  --inst_solver_calls_frac                1.
% 7.44/1.50  --inst_passive_queue_type               priority_queues
% 7.44/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.44/1.50  --inst_passive_queues_freq              [25;2]
% 7.44/1.50  --inst_dismatching                      true
% 7.44/1.50  --inst_eager_unprocessed_to_passive     true
% 7.44/1.50  --inst_prop_sim_given                   true
% 7.44/1.50  --inst_prop_sim_new                     false
% 7.44/1.50  --inst_subs_new                         false
% 7.44/1.50  --inst_eq_res_simp                      false
% 7.44/1.50  --inst_subs_given                       false
% 7.44/1.50  --inst_orphan_elimination               true
% 7.44/1.50  --inst_learning_loop_flag               true
% 7.44/1.50  --inst_learning_start                   3000
% 7.44/1.50  --inst_learning_factor                  2
% 7.44/1.50  --inst_start_prop_sim_after_learn       3
% 7.44/1.50  --inst_sel_renew                        solver
% 7.44/1.50  --inst_lit_activity_flag                true
% 7.44/1.50  --inst_restr_to_given                   false
% 7.44/1.50  --inst_activity_threshold               500
% 7.44/1.50  --inst_out_proof                        true
% 7.44/1.50  
% 7.44/1.50  ------ Resolution Options
% 7.44/1.50  
% 7.44/1.50  --resolution_flag                       true
% 7.44/1.50  --res_lit_sel                           adaptive
% 7.44/1.50  --res_lit_sel_side                      none
% 7.44/1.50  --res_ordering                          kbo
% 7.44/1.50  --res_to_prop_solver                    active
% 7.44/1.50  --res_prop_simpl_new                    false
% 7.44/1.50  --res_prop_simpl_given                  true
% 7.44/1.50  --res_passive_queue_type                priority_queues
% 7.44/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.44/1.50  --res_passive_queues_freq               [15;5]
% 7.44/1.50  --res_forward_subs                      full
% 7.44/1.50  --res_backward_subs                     full
% 7.44/1.50  --res_forward_subs_resolution           true
% 7.44/1.50  --res_backward_subs_resolution          true
% 7.44/1.50  --res_orphan_elimination                true
% 7.44/1.50  --res_time_limit                        2.
% 7.44/1.50  --res_out_proof                         true
% 7.44/1.50  
% 7.44/1.50  ------ Superposition Options
% 7.44/1.50  
% 7.44/1.50  --superposition_flag                    true
% 7.44/1.50  --sup_passive_queue_type                priority_queues
% 7.44/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.44/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.44/1.50  --demod_completeness_check              fast
% 7.44/1.50  --demod_use_ground                      true
% 7.44/1.50  --sup_to_prop_solver                    passive
% 7.44/1.50  --sup_prop_simpl_new                    true
% 7.44/1.50  --sup_prop_simpl_given                  true
% 7.44/1.50  --sup_fun_splitting                     false
% 7.44/1.50  --sup_smt_interval                      50000
% 7.44/1.50  
% 7.44/1.50  ------ Superposition Simplification Setup
% 7.44/1.50  
% 7.44/1.50  --sup_indices_passive                   []
% 7.44/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.44/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.44/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.44/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.44/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.44/1.50  --sup_full_bw                           [BwDemod]
% 7.44/1.50  --sup_immed_triv                        [TrivRules]
% 7.44/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.44/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.44/1.50  --sup_immed_bw_main                     []
% 7.44/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.44/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.44/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.44/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.44/1.50  
% 7.44/1.50  ------ Combination Options
% 7.44/1.50  
% 7.44/1.50  --comb_res_mult                         3
% 7.44/1.50  --comb_sup_mult                         2
% 7.44/1.50  --comb_inst_mult                        10
% 7.44/1.50  
% 7.44/1.50  ------ Debug Options
% 7.44/1.50  
% 7.44/1.50  --dbg_backtrace                         false
% 7.44/1.50  --dbg_dump_prop_clauses                 false
% 7.44/1.50  --dbg_dump_prop_clauses_file            -
% 7.44/1.50  --dbg_out_stat                          false
% 7.44/1.50  ------ Parsing...
% 7.44/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.44/1.50  
% 7.44/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.44/1.50  
% 7.44/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.44/1.50  
% 7.44/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.44/1.50  ------ Proving...
% 7.44/1.50  ------ Problem Properties 
% 7.44/1.50  
% 7.44/1.50  
% 7.44/1.50  clauses                                 40
% 7.44/1.50  conjectures                             5
% 7.44/1.50  EPR                                     8
% 7.44/1.50  Horn                                    23
% 7.44/1.50  unary                                   5
% 7.44/1.50  binary                                  6
% 7.44/1.50  lits                                    151
% 7.44/1.50  lits eq                                 22
% 7.44/1.50  fd_pure                                 0
% 7.44/1.50  fd_pseudo                               0
% 7.44/1.50  fd_cond                                 0
% 7.44/1.50  fd_pseudo_cond                          5
% 7.44/1.50  AC symbols                              0
% 7.44/1.50  
% 7.44/1.50  ------ Schedule dynamic 5 is on 
% 7.44/1.50  
% 7.44/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.44/1.50  
% 7.44/1.50  
% 7.44/1.50  ------ 
% 7.44/1.50  Current options:
% 7.44/1.50  ------ 
% 7.44/1.50  
% 7.44/1.50  ------ Input Options
% 7.44/1.50  
% 7.44/1.50  --out_options                           all
% 7.44/1.50  --tptp_safe_out                         true
% 7.44/1.50  --problem_path                          ""
% 7.44/1.50  --include_path                          ""
% 7.44/1.50  --clausifier                            res/vclausify_rel
% 7.44/1.50  --clausifier_options                    --mode clausify
% 7.44/1.50  --stdin                                 false
% 7.44/1.50  --stats_out                             all
% 7.44/1.50  
% 7.44/1.50  ------ General Options
% 7.44/1.50  
% 7.44/1.50  --fof                                   false
% 7.44/1.50  --time_out_real                         305.
% 7.44/1.50  --time_out_virtual                      -1.
% 7.44/1.50  --symbol_type_check                     false
% 7.44/1.50  --clausify_out                          false
% 7.44/1.50  --sig_cnt_out                           false
% 7.44/1.50  --trig_cnt_out                          false
% 7.44/1.50  --trig_cnt_out_tolerance                1.
% 7.44/1.50  --trig_cnt_out_sk_spl                   false
% 7.44/1.50  --abstr_cl_out                          false
% 7.44/1.50  
% 7.44/1.50  ------ Global Options
% 7.44/1.50  
% 7.44/1.50  --schedule                              default
% 7.44/1.50  --add_important_lit                     false
% 7.44/1.50  --prop_solver_per_cl                    1000
% 7.44/1.50  --min_unsat_core                        false
% 7.44/1.50  --soft_assumptions                      false
% 7.44/1.50  --soft_lemma_size                       3
% 7.44/1.50  --prop_impl_unit_size                   0
% 7.44/1.50  --prop_impl_unit                        []
% 7.44/1.50  --share_sel_clauses                     true
% 7.44/1.50  --reset_solvers                         false
% 7.44/1.50  --bc_imp_inh                            [conj_cone]
% 7.44/1.50  --conj_cone_tolerance                   3.
% 7.44/1.50  --extra_neg_conj                        none
% 7.44/1.50  --large_theory_mode                     true
% 7.44/1.50  --prolific_symb_bound                   200
% 7.44/1.50  --lt_threshold                          2000
% 7.44/1.50  --clause_weak_htbl                      true
% 7.44/1.50  --gc_record_bc_elim                     false
% 7.44/1.50  
% 7.44/1.50  ------ Preprocessing Options
% 7.44/1.50  
% 7.44/1.50  --preprocessing_flag                    true
% 7.44/1.50  --time_out_prep_mult                    0.1
% 7.44/1.50  --splitting_mode                        input
% 7.44/1.50  --splitting_grd                         true
% 7.44/1.50  --splitting_cvd                         false
% 7.44/1.50  --splitting_cvd_svl                     false
% 7.44/1.50  --splitting_nvd                         32
% 7.44/1.50  --sub_typing                            true
% 7.44/1.50  --prep_gs_sim                           true
% 7.44/1.50  --prep_unflatten                        true
% 7.44/1.50  --prep_res_sim                          true
% 7.44/1.50  --prep_upred                            true
% 7.44/1.50  --prep_sem_filter                       exhaustive
% 7.44/1.50  --prep_sem_filter_out                   false
% 7.44/1.50  --pred_elim                             true
% 7.44/1.50  --res_sim_input                         true
% 7.44/1.50  --eq_ax_congr_red                       true
% 7.44/1.50  --pure_diseq_elim                       true
% 7.44/1.50  --brand_transform                       false
% 7.44/1.50  --non_eq_to_eq                          false
% 7.44/1.50  --prep_def_merge                        true
% 7.44/1.50  --prep_def_merge_prop_impl              false
% 7.44/1.50  --prep_def_merge_mbd                    true
% 7.44/1.50  --prep_def_merge_tr_red                 false
% 7.44/1.50  --prep_def_merge_tr_cl                  false
% 7.44/1.50  --smt_preprocessing                     true
% 7.44/1.50  --smt_ac_axioms                         fast
% 7.44/1.50  --preprocessed_out                      false
% 7.44/1.50  --preprocessed_stats                    false
% 7.44/1.50  
% 7.44/1.50  ------ Abstraction refinement Options
% 7.44/1.50  
% 7.44/1.50  --abstr_ref                             []
% 7.44/1.50  --abstr_ref_prep                        false
% 7.44/1.50  --abstr_ref_until_sat                   false
% 7.44/1.50  --abstr_ref_sig_restrict                funpre
% 7.44/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.44/1.50  --abstr_ref_under                       []
% 7.44/1.50  
% 7.44/1.50  ------ SAT Options
% 7.44/1.50  
% 7.44/1.50  --sat_mode                              false
% 7.44/1.50  --sat_fm_restart_options                ""
% 7.44/1.50  --sat_gr_def                            false
% 7.44/1.50  --sat_epr_types                         true
% 7.44/1.50  --sat_non_cyclic_types                  false
% 7.44/1.50  --sat_finite_models                     false
% 7.44/1.50  --sat_fm_lemmas                         false
% 7.44/1.50  --sat_fm_prep                           false
% 7.44/1.50  --sat_fm_uc_incr                        true
% 7.44/1.50  --sat_out_model                         small
% 7.44/1.50  --sat_out_clauses                       false
% 7.44/1.50  
% 7.44/1.50  ------ QBF Options
% 7.44/1.50  
% 7.44/1.50  --qbf_mode                              false
% 7.44/1.50  --qbf_elim_univ                         false
% 7.44/1.50  --qbf_dom_inst                          none
% 7.44/1.50  --qbf_dom_pre_inst                      false
% 7.44/1.50  --qbf_sk_in                             false
% 7.44/1.50  --qbf_pred_elim                         true
% 7.44/1.50  --qbf_split                             512
% 7.44/1.50  
% 7.44/1.50  ------ BMC1 Options
% 7.44/1.50  
% 7.44/1.50  --bmc1_incremental                      false
% 7.44/1.50  --bmc1_axioms                           reachable_all
% 7.44/1.50  --bmc1_min_bound                        0
% 7.44/1.50  --bmc1_max_bound                        -1
% 7.44/1.50  --bmc1_max_bound_default                -1
% 7.44/1.50  --bmc1_symbol_reachability              true
% 7.44/1.50  --bmc1_property_lemmas                  false
% 7.44/1.50  --bmc1_k_induction                      false
% 7.44/1.50  --bmc1_non_equiv_states                 false
% 7.44/1.50  --bmc1_deadlock                         false
% 7.44/1.50  --bmc1_ucm                              false
% 7.44/1.50  --bmc1_add_unsat_core                   none
% 7.44/1.50  --bmc1_unsat_core_children              false
% 7.44/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.44/1.50  --bmc1_out_stat                         full
% 7.44/1.50  --bmc1_ground_init                      false
% 7.44/1.50  --bmc1_pre_inst_next_state              false
% 7.44/1.50  --bmc1_pre_inst_state                   false
% 7.44/1.50  --bmc1_pre_inst_reach_state             false
% 7.44/1.50  --bmc1_out_unsat_core                   false
% 7.44/1.50  --bmc1_aig_witness_out                  false
% 7.44/1.50  --bmc1_verbose                          false
% 7.44/1.50  --bmc1_dump_clauses_tptp                false
% 7.44/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.44/1.50  --bmc1_dump_file                        -
% 7.44/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.44/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.44/1.50  --bmc1_ucm_extend_mode                  1
% 7.44/1.50  --bmc1_ucm_init_mode                    2
% 7.44/1.50  --bmc1_ucm_cone_mode                    none
% 7.44/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.44/1.50  --bmc1_ucm_relax_model                  4
% 7.44/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.44/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.44/1.50  --bmc1_ucm_layered_model                none
% 7.44/1.50  --bmc1_ucm_max_lemma_size               10
% 7.44/1.50  
% 7.44/1.50  ------ AIG Options
% 7.44/1.50  
% 7.44/1.50  --aig_mode                              false
% 7.44/1.50  
% 7.44/1.50  ------ Instantiation Options
% 7.44/1.50  
% 7.44/1.50  --instantiation_flag                    true
% 7.44/1.50  --inst_sos_flag                         false
% 7.44/1.50  --inst_sos_phase                        true
% 7.44/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.44/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.44/1.50  --inst_lit_sel_side                     none
% 7.44/1.50  --inst_solver_per_active                1400
% 7.44/1.50  --inst_solver_calls_frac                1.
% 7.44/1.50  --inst_passive_queue_type               priority_queues
% 7.44/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.44/1.50  --inst_passive_queues_freq              [25;2]
% 7.44/1.50  --inst_dismatching                      true
% 7.44/1.50  --inst_eager_unprocessed_to_passive     true
% 7.44/1.50  --inst_prop_sim_given                   true
% 7.44/1.50  --inst_prop_sim_new                     false
% 7.44/1.50  --inst_subs_new                         false
% 7.44/1.50  --inst_eq_res_simp                      false
% 7.44/1.50  --inst_subs_given                       false
% 7.44/1.50  --inst_orphan_elimination               true
% 7.44/1.50  --inst_learning_loop_flag               true
% 7.44/1.50  --inst_learning_start                   3000
% 7.44/1.50  --inst_learning_factor                  2
% 7.44/1.50  --inst_start_prop_sim_after_learn       3
% 7.44/1.50  --inst_sel_renew                        solver
% 7.44/1.50  --inst_lit_activity_flag                true
% 7.44/1.50  --inst_restr_to_given                   false
% 7.44/1.50  --inst_activity_threshold               500
% 7.44/1.50  --inst_out_proof                        true
% 7.44/1.50  
% 7.44/1.50  ------ Resolution Options
% 7.44/1.50  
% 7.44/1.50  --resolution_flag                       false
% 7.44/1.50  --res_lit_sel                           adaptive
% 7.44/1.50  --res_lit_sel_side                      none
% 7.44/1.50  --res_ordering                          kbo
% 7.44/1.50  --res_to_prop_solver                    active
% 7.44/1.50  --res_prop_simpl_new                    false
% 7.44/1.50  --res_prop_simpl_given                  true
% 7.44/1.50  --res_passive_queue_type                priority_queues
% 7.44/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.44/1.50  --res_passive_queues_freq               [15;5]
% 7.44/1.50  --res_forward_subs                      full
% 7.44/1.50  --res_backward_subs                     full
% 7.44/1.50  --res_forward_subs_resolution           true
% 7.44/1.50  --res_backward_subs_resolution          true
% 7.44/1.50  --res_orphan_elimination                true
% 7.44/1.50  --res_time_limit                        2.
% 7.44/1.50  --res_out_proof                         true
% 7.44/1.50  
% 7.44/1.50  ------ Superposition Options
% 7.44/1.50  
% 7.44/1.50  --superposition_flag                    true
% 7.44/1.50  --sup_passive_queue_type                priority_queues
% 7.44/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.44/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.44/1.50  --demod_completeness_check              fast
% 7.44/1.50  --demod_use_ground                      true
% 7.44/1.50  --sup_to_prop_solver                    passive
% 7.44/1.50  --sup_prop_simpl_new                    true
% 7.44/1.50  --sup_prop_simpl_given                  true
% 7.44/1.50  --sup_fun_splitting                     false
% 7.44/1.50  --sup_smt_interval                      50000
% 7.44/1.50  
% 7.44/1.50  ------ Superposition Simplification Setup
% 7.44/1.50  
% 7.44/1.50  --sup_indices_passive                   []
% 7.44/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.44/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.44/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.44/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.44/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.44/1.50  --sup_full_bw                           [BwDemod]
% 7.44/1.50  --sup_immed_triv                        [TrivRules]
% 7.44/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.44/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.44/1.50  --sup_immed_bw_main                     []
% 7.44/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.44/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.44/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.44/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.44/1.50  
% 7.44/1.50  ------ Combination Options
% 7.44/1.50  
% 7.44/1.50  --comb_res_mult                         3
% 7.44/1.50  --comb_sup_mult                         2
% 7.44/1.50  --comb_inst_mult                        10
% 7.44/1.50  
% 7.44/1.50  ------ Debug Options
% 7.44/1.50  
% 7.44/1.50  --dbg_backtrace                         false
% 7.44/1.50  --dbg_dump_prop_clauses                 false
% 7.44/1.50  --dbg_dump_prop_clauses_file            -
% 7.44/1.50  --dbg_out_stat                          false
% 7.44/1.50  
% 7.44/1.50  
% 7.44/1.50  
% 7.44/1.50  
% 7.44/1.50  ------ Proving...
% 7.44/1.50  
% 7.44/1.50  
% 7.44/1.50  % SZS status Theorem for theBenchmark.p
% 7.44/1.50  
% 7.44/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.44/1.50  
% 7.44/1.50  fof(f21,conjecture,(
% 7.44/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1))))),
% 7.44/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.50  
% 7.44/1.50  fof(f22,negated_conjecture,(
% 7.44/1.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1))))),
% 7.44/1.50    inference(negated_conjecture,[],[f21])).
% 7.44/1.50  
% 7.44/1.50  fof(f54,plain,(
% 7.44/1.50    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.44/1.50    inference(ennf_transformation,[],[f22])).
% 7.44/1.50  
% 7.44/1.50  fof(f55,plain,(
% 7.44/1.50    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.44/1.50    inference(flattening,[],[f54])).
% 7.44/1.50  
% 7.44/1.50  fof(f66,plain,(
% 7.44/1.50    ? [X0] : (? [X1] : (((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.44/1.50    inference(nnf_transformation,[],[f55])).
% 7.44/1.50  
% 7.44/1.50  fof(f67,plain,(
% 7.44/1.50    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.44/1.50    inference(flattening,[],[f66])).
% 7.44/1.50  
% 7.44/1.50  fof(f69,plain,(
% 7.44/1.50    ( ! [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,sK3) | ~m1_pre_topc(sK3,X0) | ~v1_tsep_1(sK3,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,sK3) | (m1_pre_topc(sK3,X0) & v1_tsep_1(sK3,X0))) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 7.44/1.50    introduced(choice_axiom,[])).
% 7.44/1.50  
% 7.44/1.50  fof(f68,plain,(
% 7.44/1.50    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,X1) | ~m1_pre_topc(X1,sK2) | ~v1_tsep_1(X1,sK2)) & (g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,X1) | (m1_pre_topc(X1,sK2) & v1_tsep_1(X1,sK2))) & m1_pre_topc(X1,sK2) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 7.44/1.50    introduced(choice_axiom,[])).
% 7.44/1.50  
% 7.44/1.50  fof(f70,plain,(
% 7.44/1.50    ((g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) | ~m1_pre_topc(sK3,sK2) | ~v1_tsep_1(sK3,sK2)) & (g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) | (m1_pre_topc(sK3,sK2) & v1_tsep_1(sK3,sK2))) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 7.44/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f67,f69,f68])).
% 7.44/1.50  
% 7.44/1.50  fof(f107,plain,(
% 7.44/1.50    l1_pre_topc(sK2)),
% 7.44/1.50    inference(cnf_transformation,[],[f70])).
% 7.44/1.50  
% 7.44/1.50  fof(f18,axiom,(
% 7.44/1.50    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 7.44/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.50  
% 7.44/1.50  fof(f50,plain,(
% 7.44/1.50    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 7.44/1.50    inference(ennf_transformation,[],[f18])).
% 7.44/1.50  
% 7.44/1.50  fof(f102,plain,(
% 7.44/1.50    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 7.44/1.50    inference(cnf_transformation,[],[f50])).
% 7.44/1.50  
% 7.44/1.50  fof(f16,axiom,(
% 7.44/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 7.44/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.50  
% 7.44/1.50  fof(f48,plain,(
% 7.44/1.50    ! [X0] : (! [X1] : ((m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.44/1.50    inference(ennf_transformation,[],[f16])).
% 7.44/1.50  
% 7.44/1.50  fof(f100,plain,(
% 7.44/1.50    ( ! [X0,X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.44/1.50    inference(cnf_transformation,[],[f48])).
% 7.44/1.50  
% 7.44/1.50  fof(f4,axiom,(
% 7.44/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.44/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.50  
% 7.44/1.50  fof(f28,plain,(
% 7.44/1.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.44/1.50    inference(ennf_transformation,[],[f4])).
% 7.44/1.50  
% 7.44/1.50  fof(f75,plain,(
% 7.44/1.50    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.44/1.50    inference(cnf_transformation,[],[f28])).
% 7.44/1.50  
% 7.44/1.50  fof(f2,axiom,(
% 7.44/1.50    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 7.44/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.50  
% 7.44/1.50  fof(f25,plain,(
% 7.44/1.50    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 7.44/1.50    inference(ennf_transformation,[],[f2])).
% 7.44/1.50  
% 7.44/1.50  fof(f26,plain,(
% 7.44/1.50    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 7.44/1.50    inference(flattening,[],[f25])).
% 7.44/1.50  
% 7.44/1.50  fof(f72,plain,(
% 7.44/1.50    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 7.44/1.50    inference(cnf_transformation,[],[f26])).
% 7.44/1.50  
% 7.44/1.50  fof(f99,plain,(
% 7.44/1.50    ( ! [X0,X1] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.44/1.50    inference(cnf_transformation,[],[f48])).
% 7.44/1.50  
% 7.44/1.50  fof(f7,axiom,(
% 7.44/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 7.44/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.50  
% 7.44/1.50  fof(f32,plain,(
% 7.44/1.50    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.44/1.50    inference(ennf_transformation,[],[f7])).
% 7.44/1.50  
% 7.44/1.50  fof(f80,plain,(
% 7.44/1.50    ( ! [X2,X0,X3,X1] : (X1 = X3 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.44/1.50    inference(cnf_transformation,[],[f32])).
% 7.44/1.50  
% 7.44/1.50  fof(f8,axiom,(
% 7.44/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 7.44/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.50  
% 7.44/1.50  fof(f33,plain,(
% 7.44/1.50    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 7.44/1.50    inference(ennf_transformation,[],[f8])).
% 7.44/1.50  
% 7.44/1.50  fof(f81,plain,(
% 7.44/1.50    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 7.44/1.50    inference(cnf_transformation,[],[f33])).
% 7.44/1.50  
% 7.44/1.50  fof(f109,plain,(
% 7.44/1.50    m1_pre_topc(sK3,sK2)),
% 7.44/1.50    inference(cnf_transformation,[],[f70])).
% 7.44/1.50  
% 7.44/1.50  fof(f20,axiom,(
% 7.44/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 7.44/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.50  
% 7.44/1.50  fof(f52,plain,(
% 7.44/1.50    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.44/1.50    inference(ennf_transformation,[],[f20])).
% 7.44/1.50  
% 7.44/1.50  fof(f53,plain,(
% 7.44/1.50    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.44/1.50    inference(flattening,[],[f52])).
% 7.44/1.50  
% 7.44/1.50  fof(f104,plain,(
% 7.44/1.50    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.44/1.50    inference(cnf_transformation,[],[f53])).
% 7.44/1.50  
% 7.44/1.50  fof(f106,plain,(
% 7.44/1.50    v2_pre_topc(sK2)),
% 7.44/1.50    inference(cnf_transformation,[],[f70])).
% 7.44/1.50  
% 7.44/1.50  fof(f79,plain,(
% 7.44/1.50    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.44/1.50    inference(cnf_transformation,[],[f32])).
% 7.44/1.50  
% 7.44/1.50  fof(f5,axiom,(
% 7.44/1.50    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.44/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.50  
% 7.44/1.50  fof(f29,plain,(
% 7.44/1.50    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.44/1.50    inference(ennf_transformation,[],[f5])).
% 7.44/1.50  
% 7.44/1.50  fof(f76,plain,(
% 7.44/1.50    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 7.44/1.50    inference(cnf_transformation,[],[f29])).
% 7.44/1.50  
% 7.44/1.50  fof(f17,axiom,(
% 7.44/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.44/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.50  
% 7.44/1.50  fof(f49,plain,(
% 7.44/1.50    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.44/1.50    inference(ennf_transformation,[],[f17])).
% 7.44/1.50  
% 7.44/1.50  fof(f101,plain,(
% 7.44/1.50    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.44/1.50    inference(cnf_transformation,[],[f49])).
% 7.44/1.50  
% 7.44/1.50  fof(f15,axiom,(
% 7.44/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 7.44/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.50  
% 7.44/1.50  fof(f46,plain,(
% 7.44/1.50    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.44/1.50    inference(ennf_transformation,[],[f15])).
% 7.44/1.50  
% 7.44/1.50  fof(f47,plain,(
% 7.44/1.50    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.44/1.50    inference(flattening,[],[f46])).
% 7.44/1.50  
% 7.44/1.50  fof(f97,plain,(
% 7.44/1.50    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.44/1.50    inference(cnf_transformation,[],[f47])).
% 7.44/1.50  
% 7.44/1.50  fof(f9,axiom,(
% 7.44/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 7.44/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.50  
% 7.44/1.50  fof(f34,plain,(
% 7.44/1.50    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.44/1.50    inference(ennf_transformation,[],[f9])).
% 7.44/1.50  
% 7.44/1.50  fof(f35,plain,(
% 7.44/1.50    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.44/1.50    inference(flattening,[],[f34])).
% 7.44/1.50  
% 7.44/1.50  fof(f57,plain,(
% 7.44/1.50    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.44/1.50    inference(nnf_transformation,[],[f35])).
% 7.44/1.50  
% 7.44/1.50  fof(f58,plain,(
% 7.44/1.50    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.44/1.50    inference(rectify,[],[f57])).
% 7.44/1.50  
% 7.44/1.50  fof(f59,plain,(
% 7.44/1.50    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.44/1.50    introduced(choice_axiom,[])).
% 7.44/1.50  
% 7.44/1.50  fof(f60,plain,(
% 7.44/1.50    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.44/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f58,f59])).
% 7.44/1.50  
% 7.44/1.50  fof(f82,plain,(
% 7.44/1.50    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.44/1.50    inference(cnf_transformation,[],[f60])).
% 7.44/1.50  
% 7.44/1.50  fof(f113,plain,(
% 7.44/1.50    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.44/1.50    inference(equality_resolution,[],[f82])).
% 7.44/1.50  
% 7.44/1.50  fof(f114,plain,(
% 7.44/1.50    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.44/1.50    inference(equality_resolution,[],[f113])).
% 7.44/1.50  
% 7.44/1.50  fof(f12,axiom,(
% 7.44/1.50    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 7.44/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.50  
% 7.44/1.50  fof(f40,plain,(
% 7.44/1.50    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.44/1.50    inference(ennf_transformation,[],[f12])).
% 7.44/1.50  
% 7.44/1.50  fof(f41,plain,(
% 7.44/1.50    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.44/1.50    inference(flattening,[],[f40])).
% 7.44/1.50  
% 7.44/1.50  fof(f91,plain,(
% 7.44/1.50    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.44/1.50    inference(cnf_transformation,[],[f41])).
% 7.44/1.50  
% 7.44/1.50  fof(f92,plain,(
% 7.44/1.50    ( ! [X0,X1] : (v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.44/1.50    inference(cnf_transformation,[],[f41])).
% 7.44/1.50  
% 7.44/1.50  fof(f93,plain,(
% 7.44/1.50    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.44/1.50    inference(cnf_transformation,[],[f41])).
% 7.44/1.50  
% 7.44/1.50  fof(f105,plain,(
% 7.44/1.50    ~v2_struct_0(sK2)),
% 7.44/1.50    inference(cnf_transformation,[],[f70])).
% 7.44/1.50  
% 7.44/1.50  fof(f11,axiom,(
% 7.44/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)))),
% 7.44/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.50  
% 7.44/1.50  fof(f38,plain,(
% 7.44/1.50    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.44/1.50    inference(ennf_transformation,[],[f11])).
% 7.44/1.50  
% 7.44/1.50  fof(f39,plain,(
% 7.44/1.50    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.44/1.50    inference(flattening,[],[f38])).
% 7.44/1.50  
% 7.44/1.50  fof(f90,plain,(
% 7.44/1.50    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.44/1.50    inference(cnf_transformation,[],[f39])).
% 7.44/1.50  
% 7.44/1.50  fof(f98,plain,(
% 7.44/1.50    ( ! [X0,X1] : (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.44/1.50    inference(cnf_transformation,[],[f47])).
% 7.44/1.50  
% 7.44/1.50  fof(f10,axiom,(
% 7.44/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tsep_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_pre_topc(X2,X0))))))),
% 7.44/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.50  
% 7.44/1.50  fof(f36,plain,(
% 7.44/1.50    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.44/1.50    inference(ennf_transformation,[],[f10])).
% 7.44/1.50  
% 7.44/1.50  fof(f37,plain,(
% 7.44/1.50    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.44/1.50    inference(flattening,[],[f36])).
% 7.44/1.50  
% 7.44/1.50  fof(f61,plain,(
% 7.44/1.50    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.44/1.50    inference(nnf_transformation,[],[f37])).
% 7.44/1.50  
% 7.44/1.50  fof(f62,plain,(
% 7.44/1.50    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.44/1.50    inference(rectify,[],[f61])).
% 7.44/1.50  
% 7.44/1.50  fof(f63,plain,(
% 7.44/1.50    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK1(X0,X1),X0) & u1_struct_0(X1) = sK1(X0,X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.44/1.50    introduced(choice_axiom,[])).
% 7.44/1.50  
% 7.44/1.50  fof(f64,plain,(
% 7.44/1.50    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | (~v3_pre_topc(sK1(X0,X1),X0) & u1_struct_0(X1) = sK1(X0,X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.44/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f62,f63])).
% 7.44/1.50  
% 7.44/1.50  fof(f86,plain,(
% 7.44/1.50    ( ! [X0,X3,X1] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.44/1.50    inference(cnf_transformation,[],[f64])).
% 7.44/1.50  
% 7.44/1.50  fof(f115,plain,(
% 7.44/1.50    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.44/1.50    inference(equality_resolution,[],[f86])).
% 7.44/1.50  
% 7.44/1.50  fof(f110,plain,(
% 7.44/1.50    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) | v1_tsep_1(sK3,sK2)),
% 7.44/1.50    inference(cnf_transformation,[],[f70])).
% 7.44/1.50  
% 7.44/1.50  fof(f3,axiom,(
% 7.44/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 7.44/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.50  
% 7.44/1.50  fof(f27,plain,(
% 7.44/1.50    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.44/1.50    inference(ennf_transformation,[],[f3])).
% 7.44/1.50  
% 7.44/1.50  fof(f56,plain,(
% 7.44/1.50    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.44/1.50    inference(nnf_transformation,[],[f27])).
% 7.44/1.50  
% 7.44/1.50  fof(f73,plain,(
% 7.44/1.50    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.44/1.50    inference(cnf_transformation,[],[f56])).
% 7.44/1.50  
% 7.44/1.50  fof(f14,axiom,(
% 7.44/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 7.44/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.50  
% 7.44/1.50  fof(f44,plain,(
% 7.44/1.50    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.44/1.50    inference(ennf_transformation,[],[f14])).
% 7.44/1.50  
% 7.44/1.50  fof(f45,plain,(
% 7.44/1.50    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.44/1.50    inference(flattening,[],[f44])).
% 7.44/1.50  
% 7.44/1.50  fof(f65,plain,(
% 7.44/1.50    ! [X0] : (! [X1] : (((r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1)) & (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.44/1.50    inference(nnf_transformation,[],[f45])).
% 7.44/1.50  
% 7.44/1.50  fof(f95,plain,(
% 7.44/1.50    ( ! [X0,X1] : (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.44/1.50    inference(cnf_transformation,[],[f65])).
% 7.44/1.50  
% 7.44/1.50  fof(f96,plain,(
% 7.44/1.50    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.44/1.50    inference(cnf_transformation,[],[f65])).
% 7.44/1.50  
% 7.44/1.50  fof(f74,plain,(
% 7.44/1.50    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.44/1.50    inference(cnf_transformation,[],[f56])).
% 7.44/1.50  
% 7.44/1.50  fof(f89,plain,(
% 7.44/1.50    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(sK1(X0,X1),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.44/1.50    inference(cnf_transformation,[],[f64])).
% 7.44/1.50  
% 7.44/1.50  fof(f112,plain,(
% 7.44/1.50    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) | ~m1_pre_topc(sK3,sK2) | ~v1_tsep_1(sK3,sK2)),
% 7.44/1.50    inference(cnf_transformation,[],[f70])).
% 7.44/1.50  
% 7.44/1.50  fof(f88,plain,(
% 7.44/1.50    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | u1_struct_0(X1) = sK1(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.44/1.50    inference(cnf_transformation,[],[f64])).
% 7.44/1.50  
% 7.44/1.50  cnf(c_39,negated_conjecture,
% 7.44/1.50      ( l1_pre_topc(sK2) ),
% 7.44/1.50      inference(cnf_transformation,[],[f107]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_6260,plain,
% 7.44/1.50      ( l1_pre_topc(sK2) = iProver_top ),
% 7.44/1.50      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_31,plain,
% 7.44/1.50      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 7.44/1.50      inference(cnf_transformation,[],[f102]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_6264,plain,
% 7.44/1.50      ( m1_pre_topc(X0,X0) = iProver_top
% 7.44/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.44/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_28,plain,
% 7.44/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.44/1.50      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 7.44/1.50      | ~ l1_pre_topc(X1) ),
% 7.44/1.50      inference(cnf_transformation,[],[f100]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_6267,plain,
% 7.44/1.50      ( m1_pre_topc(X0,X1) != iProver_top
% 7.44/1.50      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
% 7.44/1.50      | l1_pre_topc(X1) != iProver_top ),
% 7.44/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_4,plain,
% 7.44/1.50      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.44/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_6286,plain,
% 7.44/1.50      ( m1_pre_topc(X0,X1) != iProver_top
% 7.44/1.50      | l1_pre_topc(X1) != iProver_top
% 7.44/1.50      | l1_pre_topc(X0) = iProver_top ),
% 7.44/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_7410,plain,
% 7.44/1.50      ( m1_pre_topc(X0,X1) != iProver_top
% 7.44/1.50      | l1_pre_topc(X1) != iProver_top
% 7.44/1.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 7.44/1.50      inference(superposition,[status(thm)],[c_6267,c_6286]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_7508,plain,
% 7.44/1.50      ( l1_pre_topc(X0) != iProver_top
% 7.44/1.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 7.44/1.50      inference(superposition,[status(thm)],[c_6264,c_7410]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_1,plain,
% 7.44/1.50      ( ~ l1_pre_topc(X0)
% 7.44/1.50      | ~ v1_pre_topc(X0)
% 7.44/1.50      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 7.44/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_6289,plain,
% 7.44/1.50      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
% 7.44/1.50      | l1_pre_topc(X0) != iProver_top
% 7.44/1.50      | v1_pre_topc(X0) != iProver_top ),
% 7.44/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_10728,plain,
% 7.44/1.50      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 7.44/1.50      | l1_pre_topc(X0) != iProver_top
% 7.44/1.50      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 7.44/1.50      inference(superposition,[status(thm)],[c_7508,c_6289]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_6691,plain,
% 7.44/1.50      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 7.44/1.50      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 7.44/1.50      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 7.44/1.50      inference(instantiation,[status(thm)],[c_1]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_6692,plain,
% 7.44/1.50      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 7.44/1.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 7.44/1.50      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 7.44/1.50      inference(predicate_to_equality,[status(thm)],[c_6691]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_29,plain,
% 7.44/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.44/1.50      | ~ l1_pre_topc(X1)
% 7.44/1.50      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 7.44/1.50      inference(cnf_transformation,[],[f99]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_6266,plain,
% 7.44/1.50      ( m1_pre_topc(X0,X1) != iProver_top
% 7.44/1.50      | l1_pre_topc(X1) != iProver_top
% 7.44/1.50      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 7.44/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_7242,plain,
% 7.44/1.50      ( l1_pre_topc(X0) != iProver_top
% 7.44/1.50      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 7.44/1.50      inference(superposition,[status(thm)],[c_6264,c_6266]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_29031,plain,
% 7.44/1.50      ( l1_pre_topc(X0) != iProver_top
% 7.44/1.50      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 7.44/1.50      inference(global_propositional_subsumption,
% 7.44/1.50                [status(thm)],
% 7.44/1.50                [c_10728,c_6692,c_7242,c_7508]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_29032,plain,
% 7.44/1.50      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 7.44/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.44/1.50      inference(renaming,[status(thm)],[c_29031]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_29040,plain,
% 7.44/1.50      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 7.44/1.50      inference(superposition,[status(thm)],[c_6260,c_29032]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_8,plain,
% 7.44/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.44/1.50      | X2 = X0
% 7.44/1.50      | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
% 7.44/1.50      inference(cnf_transformation,[],[f80]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_6282,plain,
% 7.44/1.50      ( X0 = X1
% 7.44/1.50      | g1_pre_topc(X2,X0) != g1_pre_topc(X3,X1)
% 7.44/1.50      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) != iProver_top ),
% 7.44/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_29343,plain,
% 7.44/1.50      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1)
% 7.44/1.50      | u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = X1
% 7.44/1.50      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 7.44/1.50      inference(superposition,[status(thm)],[c_29040,c_6282]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_44,plain,
% 7.44/1.50      ( l1_pre_topc(sK2) = iProver_top ),
% 7.44/1.50      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_54,plain,
% 7.44/1.50      ( m1_pre_topc(X0,X0) = iProver_top
% 7.44/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.44/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_56,plain,
% 7.44/1.50      ( m1_pre_topc(sK2,sK2) = iProver_top
% 7.44/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.44/1.50      inference(instantiation,[status(thm)],[c_54]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_63,plain,
% 7.44/1.50      ( m1_pre_topc(X0,X1) != iProver_top
% 7.44/1.50      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
% 7.44/1.50      | l1_pre_topc(X1) != iProver_top ),
% 7.44/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_65,plain,
% 7.44/1.50      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2) = iProver_top
% 7.44/1.50      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.44/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.44/1.50      inference(instantiation,[status(thm)],[c_63]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_7286,plain,
% 7.44/1.50      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 7.44/1.50      | ~ l1_pre_topc(X1)
% 7.44/1.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 7.44/1.50      inference(instantiation,[status(thm)],[c_4]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_7287,plain,
% 7.44/1.50      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
% 7.44/1.50      | l1_pre_topc(X1) != iProver_top
% 7.44/1.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 7.44/1.50      inference(predicate_to_equality,[status(thm)],[c_7286]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_7289,plain,
% 7.44/1.50      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2) != iProver_top
% 7.44/1.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 7.44/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.44/1.50      inference(instantiation,[status(thm)],[c_7287]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_10,plain,
% 7.44/1.50      ( m1_pre_topc(X0,X1)
% 7.44/1.50      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.44/1.50      | ~ l1_pre_topc(X1) ),
% 7.44/1.50      inference(cnf_transformation,[],[f81]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_6280,plain,
% 7.44/1.50      ( m1_pre_topc(X0,X1) = iProver_top
% 7.44/1.50      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 7.44/1.50      | l1_pre_topc(X1) != iProver_top ),
% 7.44/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_7434,plain,
% 7.44/1.50      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X0) = iProver_top
% 7.44/1.50      | l1_pre_topc(X0) != iProver_top
% 7.44/1.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 7.44/1.50      inference(superposition,[status(thm)],[c_6264,c_6280]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_12536,plain,
% 7.44/1.50      ( l1_pre_topc(X0) != iProver_top
% 7.44/1.50      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X0) = iProver_top ),
% 7.44/1.50      inference(global_propositional_subsumption,
% 7.44/1.50                [status(thm)],
% 7.44/1.50                [c_7434,c_7508]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_12537,plain,
% 7.44/1.50      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X0) = iProver_top
% 7.44/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.44/1.50      inference(renaming,[status(thm)],[c_12536]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_37,negated_conjecture,
% 7.44/1.50      ( m1_pre_topc(sK3,sK2) ),
% 7.44/1.50      inference(cnf_transformation,[],[f109]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_6262,plain,
% 7.44/1.50      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 7.44/1.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_33,plain,
% 7.44/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.44/1.50      | ~ m1_pre_topc(X2,X0)
% 7.44/1.50      | m1_pre_topc(X2,X1)
% 7.44/1.50      | ~ v2_pre_topc(X1)
% 7.44/1.50      | ~ l1_pre_topc(X1) ),
% 7.44/1.50      inference(cnf_transformation,[],[f104]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_6263,plain,
% 7.44/1.50      ( m1_pre_topc(X0,X1) != iProver_top
% 7.44/1.50      | m1_pre_topc(X2,X0) != iProver_top
% 7.44/1.50      | m1_pre_topc(X2,X1) = iProver_top
% 7.44/1.50      | v2_pre_topc(X1) != iProver_top
% 7.44/1.50      | l1_pre_topc(X1) != iProver_top ),
% 7.44/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_8782,plain,
% 7.44/1.50      ( m1_pre_topc(X0,sK3) != iProver_top
% 7.44/1.50      | m1_pre_topc(X0,sK2) = iProver_top
% 7.44/1.50      | v2_pre_topc(sK2) != iProver_top
% 7.44/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.44/1.50      inference(superposition,[status(thm)],[c_6262,c_6263]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_40,negated_conjecture,
% 7.44/1.50      ( v2_pre_topc(sK2) ),
% 7.44/1.50      inference(cnf_transformation,[],[f106]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_43,plain,
% 7.44/1.50      ( v2_pre_topc(sK2) = iProver_top ),
% 7.44/1.50      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_9048,plain,
% 7.44/1.50      ( m1_pre_topc(X0,sK3) != iProver_top
% 7.44/1.50      | m1_pre_topc(X0,sK2) = iProver_top ),
% 7.44/1.50      inference(global_propositional_subsumption,
% 7.44/1.50                [status(thm)],
% 7.44/1.50                [c_8782,c_43,c_44]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_12565,plain,
% 7.44/1.50      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK2) = iProver_top
% 7.44/1.50      | l1_pre_topc(sK3) != iProver_top ),
% 7.44/1.50      inference(superposition,[status(thm)],[c_12537,c_9048]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_6777,plain,
% 7.44/1.50      ( l1_pre_topc(sK3) = iProver_top
% 7.44/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.44/1.50      inference(superposition,[status(thm)],[c_6262,c_6286]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_13072,plain,
% 7.44/1.50      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK2) = iProver_top ),
% 7.44/1.50      inference(global_propositional_subsumption,
% 7.44/1.50                [status(thm)],
% 7.44/1.50                [c_12565,c_44,c_6777]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_7509,plain,
% 7.44/1.50      ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 7.44/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.44/1.50      inference(superposition,[status(thm)],[c_6262,c_7410]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_7642,plain,
% 7.44/1.50      ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
% 7.44/1.50      inference(global_propositional_subsumption,
% 7.44/1.50                [status(thm)],
% 7.44/1.50                [c_7509,c_44]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_7647,plain,
% 7.44/1.50      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
% 7.44/1.50      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
% 7.44/1.50      inference(superposition,[status(thm)],[c_7642,c_6289]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_7243,plain,
% 7.44/1.50      ( l1_pre_topc(sK2) != iProver_top
% 7.44/1.50      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
% 7.44/1.50      inference(superposition,[status(thm)],[c_6262,c_6266]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_7650,plain,
% 7.44/1.50      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
% 7.44/1.50      inference(global_propositional_subsumption,
% 7.44/1.50                [status(thm)],
% 7.44/1.50                [c_7647,c_44,c_7243]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_9,plain,
% 7.44/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.44/1.50      | X2 = X1
% 7.44/1.50      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 7.44/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_6281,plain,
% 7.44/1.50      ( X0 = X1
% 7.44/1.50      | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
% 7.44/1.50      | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 7.44/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_7659,plain,
% 7.44/1.50      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1)
% 7.44/1.50      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = X0
% 7.44/1.50      | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
% 7.44/1.50      inference(superposition,[status(thm)],[c_7650,c_6281]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_8112,plain,
% 7.44/1.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(sK3)
% 7.44/1.50      | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) != iProver_top ),
% 7.44/1.50      inference(equality_resolution,[status(thm)],[c_7659]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_5,plain,
% 7.44/1.50      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.44/1.50      | ~ l1_pre_topc(X0) ),
% 7.44/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_6285,plain,
% 7.44/1.50      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 7.44/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.44/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_7658,plain,
% 7.44/1.50      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1)
% 7.44/1.50      | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = X0
% 7.44/1.50      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 7.44/1.50      inference(superposition,[status(thm)],[c_7650,c_6281]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_7820,plain,
% 7.44/1.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(sK3)
% 7.44/1.50      | m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top ),
% 7.44/1.50      inference(equality_resolution,[status(thm)],[c_7658]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_8186,plain,
% 7.44/1.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(sK3)
% 7.44/1.50      | l1_pre_topc(sK3) != iProver_top ),
% 7.44/1.50      inference(superposition,[status(thm)],[c_6285,c_7820]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_8283,plain,
% 7.44/1.50      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(sK3) ),
% 7.44/1.50      inference(global_propositional_subsumption,
% 7.44/1.50                [status(thm)],
% 7.44/1.50                [c_8112,c_44,c_6777,c_8186]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_30,plain,
% 7.44/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.44/1.50      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.44/1.50      | ~ l1_pre_topc(X1) ),
% 7.44/1.50      inference(cnf_transformation,[],[f101]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_6265,plain,
% 7.44/1.50      ( m1_pre_topc(X0,X1) != iProver_top
% 7.44/1.50      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.44/1.50      | l1_pre_topc(X1) != iProver_top ),
% 7.44/1.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_8315,plain,
% 7.44/1.50      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0) != iProver_top
% 7.44/1.50      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.44/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.44/1.50      inference(superposition,[status(thm)],[c_8283,c_6265]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_13085,plain,
% 7.44/1.50      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 7.44/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.44/1.50      inference(superposition,[status(thm)],[c_13072,c_8315]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_46,plain,
% 7.44/1.50      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 7.44/1.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_7025,plain,
% 7.44/1.50      ( ~ m1_pre_topc(sK3,sK2)
% 7.44/1.50      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.44/1.50      | ~ l1_pre_topc(sK2) ),
% 7.44/1.50      inference(instantiation,[status(thm)],[c_30]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_7026,plain,
% 7.44/1.50      ( m1_pre_topc(sK3,sK2) != iProver_top
% 7.44/1.50      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 7.44/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.44/1.50      inference(predicate_to_equality,[status(thm)],[c_7025]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_13124,plain,
% 7.44/1.50      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 7.44/1.50      inference(global_propositional_subsumption,
% 7.44/1.50                [status(thm)],
% 7.44/1.50                [c_13085,c_44,c_46,c_7026]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_27,plain,
% 7.44/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.44/1.50      | ~ v2_pre_topc(X1)
% 7.44/1.50      | v2_struct_0(X1)
% 7.44/1.50      | ~ l1_pre_topc(X1)
% 7.44/1.50      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 7.44/1.50      inference(cnf_transformation,[],[f97]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_6268,plain,
% 7.44/1.50      ( u1_struct_0(k6_tmap_1(X0,X1)) = u1_struct_0(X0)
% 7.44/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.44/1.50      | v2_pre_topc(X0) != iProver_top
% 7.44/1.50      | v2_struct_0(X0) = iProver_top
% 7.44/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.44/1.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_13132,plain,
% 7.44/1.50      ( u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3))) = u1_struct_0(sK2)
% 7.44/1.50      | v2_pre_topc(sK2) != iProver_top
% 7.44/1.50      | v2_struct_0(sK2) = iProver_top
% 7.44/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.44/1.50      inference(superposition,[status(thm)],[c_13124,c_6268]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_14,plain,
% 7.44/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.44/1.50      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.44/1.50      | ~ v2_pre_topc(X1)
% 7.44/1.50      | ~ v2_pre_topc(k8_tmap_1(X1,X0))
% 7.44/1.50      | v2_struct_0(X1)
% 7.44/1.50      | ~ l1_pre_topc(X1)
% 7.44/1.50      | ~ l1_pre_topc(k8_tmap_1(X1,X0))
% 7.44/1.50      | ~ v1_pre_topc(k8_tmap_1(X1,X0))
% 7.44/1.50      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 7.44/1.50      inference(cnf_transformation,[],[f114]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_22,plain,
% 7.44/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.44/1.50      | ~ v2_pre_topc(X1)
% 7.44/1.50      | v2_struct_0(X1)
% 7.44/1.50      | ~ l1_pre_topc(X1)
% 7.44/1.50      | v1_pre_topc(k8_tmap_1(X1,X0)) ),
% 7.44/1.50      inference(cnf_transformation,[],[f91]) ).
% 7.44/1.50  
% 7.44/1.50  cnf(c_21,plain,
% 7.44/1.51      ( ~ m1_pre_topc(X0,X1)
% 7.44/1.51      | ~ v2_pre_topc(X1)
% 7.44/1.51      | v2_pre_topc(k8_tmap_1(X1,X0))
% 7.44/1.51      | v2_struct_0(X1)
% 7.44/1.51      | ~ l1_pre_topc(X1) ),
% 7.44/1.51      inference(cnf_transformation,[],[f92]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_20,plain,
% 7.44/1.51      ( ~ m1_pre_topc(X0,X1)
% 7.44/1.51      | ~ v2_pre_topc(X1)
% 7.44/1.51      | v2_struct_0(X1)
% 7.44/1.51      | ~ l1_pre_topc(X1)
% 7.44/1.51      | l1_pre_topc(k8_tmap_1(X1,X0)) ),
% 7.44/1.51      inference(cnf_transformation,[],[f93]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_270,plain,
% 7.44/1.51      ( ~ v2_pre_topc(X1)
% 7.44/1.51      | ~ m1_pre_topc(X0,X1)
% 7.44/1.51      | v2_struct_0(X1)
% 7.44/1.51      | ~ l1_pre_topc(X1)
% 7.44/1.51      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 7.44/1.51      inference(global_propositional_subsumption,
% 7.44/1.51                [status(thm)],
% 7.44/1.51                [c_14,c_30,c_22,c_21,c_20]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_271,plain,
% 7.44/1.51      ( ~ m1_pre_topc(X0,X1)
% 7.44/1.51      | ~ v2_pre_topc(X1)
% 7.44/1.51      | v2_struct_0(X1)
% 7.44/1.51      | ~ l1_pre_topc(X1)
% 7.44/1.51      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 7.44/1.51      inference(renaming,[status(thm)],[c_270]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_6257,plain,
% 7.44/1.51      ( k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
% 7.44/1.51      | m1_pre_topc(X1,X0) != iProver_top
% 7.44/1.51      | v2_pre_topc(X0) != iProver_top
% 7.44/1.51      | v2_struct_0(X0) = iProver_top
% 7.44/1.51      | l1_pre_topc(X0) != iProver_top ),
% 7.44/1.51      inference(predicate_to_equality,[status(thm)],[c_271]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_9555,plain,
% 7.44/1.51      ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3)
% 7.44/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.44/1.51      | v2_struct_0(sK2) = iProver_top
% 7.44/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.44/1.51      inference(superposition,[status(thm)],[c_6262,c_6257]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_41,negated_conjecture,
% 7.44/1.51      ( ~ v2_struct_0(sK2) ),
% 7.44/1.51      inference(cnf_transformation,[],[f105]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_7971,plain,
% 7.44/1.51      ( ~ m1_pre_topc(sK3,sK2)
% 7.44/1.51      | ~ v2_pre_topc(sK2)
% 7.44/1.51      | v2_struct_0(sK2)
% 7.44/1.51      | ~ l1_pre_topc(sK2)
% 7.44/1.51      | k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_271]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_9936,plain,
% 7.44/1.51      ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
% 7.44/1.51      inference(global_propositional_subsumption,
% 7.44/1.51                [status(thm)],
% 7.44/1.51                [c_9555,c_41,c_40,c_39,c_37,c_7971]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_13160,plain,
% 7.44/1.51      ( u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2)
% 7.44/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.44/1.51      | v2_struct_0(sK2) = iProver_top
% 7.44/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.44/1.51      inference(light_normalisation,[status(thm)],[c_13132,c_9936]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_42,plain,
% 7.44/1.51      ( v2_struct_0(sK2) != iProver_top ),
% 7.44/1.51      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_13303,plain,
% 7.44/1.51      ( u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
% 7.44/1.51      inference(global_propositional_subsumption,
% 7.44/1.51                [status(thm)],
% 7.44/1.51                [c_13160,c_42,c_43,c_44]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_13354,plain,
% 7.44/1.51      ( m1_pre_topc(X0,k8_tmap_1(sK2,sK3)) != iProver_top
% 7.44/1.51      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 7.44/1.51      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 7.44/1.51      inference(superposition,[status(thm)],[c_13303,c_6265]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_9252,plain,
% 7.44/1.51      ( ~ m1_pre_topc(sK3,sK2)
% 7.44/1.51      | ~ v2_pre_topc(sK2)
% 7.44/1.51      | v2_struct_0(sK2)
% 7.44/1.51      | l1_pre_topc(k8_tmap_1(sK2,sK3))
% 7.44/1.51      | ~ l1_pre_topc(sK2) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_20]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_9253,plain,
% 7.44/1.51      ( m1_pre_topc(sK3,sK2) != iProver_top
% 7.44/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.44/1.51      | v2_struct_0(sK2) = iProver_top
% 7.44/1.51      | l1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top
% 7.44/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.44/1.51      inference(predicate_to_equality,[status(thm)],[c_9252]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_14555,plain,
% 7.44/1.51      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 7.44/1.51      | m1_pre_topc(X0,k8_tmap_1(sK2,sK3)) != iProver_top ),
% 7.44/1.51      inference(global_propositional_subsumption,
% 7.44/1.51                [status(thm)],
% 7.44/1.51                [c_13354,c_42,c_43,c_44,c_46,c_9253]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_14556,plain,
% 7.44/1.51      ( m1_pre_topc(X0,k8_tmap_1(sK2,sK3)) != iProver_top
% 7.44/1.51      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 7.44/1.51      inference(renaming,[status(thm)],[c_14555]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_14564,plain,
% 7.44/1.51      ( m1_pre_topc(k8_tmap_1(sK2,sK3),k8_tmap_1(sK2,sK3)) != iProver_top
% 7.44/1.51      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 7.44/1.51      inference(superposition,[status(thm)],[c_13303,c_14556]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_57,plain,
% 7.44/1.51      ( m1_pre_topc(X0,X1) != iProver_top
% 7.44/1.51      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.44/1.51      | l1_pre_topc(X1) != iProver_top ),
% 7.44/1.51      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_59,plain,
% 7.44/1.51      ( m1_pre_topc(sK2,sK2) != iProver_top
% 7.44/1.51      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 7.44/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_57]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_14845,plain,
% 7.44/1.51      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 7.44/1.51      inference(global_propositional_subsumption,
% 7.44/1.51                [status(thm)],
% 7.44/1.51                [c_14564,c_44,c_56,c_59]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_19,plain,
% 7.44/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.44/1.51      | ~ v2_pre_topc(X1)
% 7.44/1.51      | v2_struct_0(X1)
% 7.44/1.51      | ~ l1_pre_topc(X1)
% 7.44/1.51      | g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X0)) = k6_tmap_1(X1,X0) ),
% 7.44/1.51      inference(cnf_transformation,[],[f90]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_6276,plain,
% 7.44/1.51      ( g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)
% 7.44/1.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.44/1.51      | v2_pre_topc(X0) != iProver_top
% 7.44/1.51      | v2_struct_0(X0) = iProver_top
% 7.44/1.51      | l1_pre_topc(X0) != iProver_top ),
% 7.44/1.51      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_14851,plain,
% 7.44/1.51      ( g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,u1_struct_0(sK2))) = k6_tmap_1(sK2,u1_struct_0(sK2))
% 7.44/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.44/1.51      | v2_struct_0(sK2) = iProver_top
% 7.44/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.44/1.51      inference(superposition,[status(thm)],[c_14845,c_6276]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_6259,plain,
% 7.44/1.51      ( v2_pre_topc(sK2) = iProver_top ),
% 7.44/1.51      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_9554,plain,
% 7.44/1.51      ( k6_tmap_1(X0,u1_struct_0(X0)) = k8_tmap_1(X0,X0)
% 7.44/1.51      | v2_pre_topc(X0) != iProver_top
% 7.44/1.51      | v2_struct_0(X0) = iProver_top
% 7.44/1.51      | l1_pre_topc(X0) != iProver_top ),
% 7.44/1.51      inference(superposition,[status(thm)],[c_6264,c_6257]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_12807,plain,
% 7.44/1.51      ( k6_tmap_1(sK2,u1_struct_0(sK2)) = k8_tmap_1(sK2,sK2)
% 7.44/1.51      | v2_struct_0(sK2) = iProver_top
% 7.44/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.44/1.51      inference(superposition,[status(thm)],[c_6259,c_9554]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_55,plain,
% 7.44/1.51      ( m1_pre_topc(sK2,sK2) | ~ l1_pre_topc(sK2) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_31]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_58,plain,
% 7.44/1.51      ( ~ m1_pre_topc(sK2,sK2)
% 7.44/1.51      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.44/1.51      | ~ l1_pre_topc(sK2) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_30]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_82,plain,
% 7.44/1.51      ( ~ m1_pre_topc(sK2,sK2)
% 7.44/1.51      | ~ v2_pre_topc(sK2)
% 7.44/1.51      | v2_struct_0(sK2)
% 7.44/1.51      | ~ l1_pre_topc(sK2)
% 7.44/1.51      | v1_pre_topc(k8_tmap_1(sK2,sK2)) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_22]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_85,plain,
% 7.44/1.51      ( ~ m1_pre_topc(sK2,sK2)
% 7.44/1.51      | v2_pre_topc(k8_tmap_1(sK2,sK2))
% 7.44/1.51      | ~ v2_pre_topc(sK2)
% 7.44/1.51      | v2_struct_0(sK2)
% 7.44/1.51      | ~ l1_pre_topc(sK2) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_21]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_88,plain,
% 7.44/1.51      ( ~ m1_pre_topc(sK2,sK2)
% 7.44/1.51      | ~ v2_pre_topc(sK2)
% 7.44/1.51      | v2_struct_0(sK2)
% 7.44/1.51      | l1_pre_topc(k8_tmap_1(sK2,sK2))
% 7.44/1.51      | ~ l1_pre_topc(sK2) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_20]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_106,plain,
% 7.44/1.51      ( ~ m1_pre_topc(sK2,sK2)
% 7.44/1.51      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.44/1.51      | ~ v2_pre_topc(k8_tmap_1(sK2,sK2))
% 7.44/1.51      | ~ v2_pre_topc(sK2)
% 7.44/1.51      | v2_struct_0(sK2)
% 7.44/1.51      | ~ l1_pre_topc(k8_tmap_1(sK2,sK2))
% 7.44/1.51      | ~ l1_pre_topc(sK2)
% 7.44/1.51      | ~ v1_pre_topc(k8_tmap_1(sK2,sK2))
% 7.44/1.51      | k6_tmap_1(sK2,u1_struct_0(sK2)) = k8_tmap_1(sK2,sK2) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_14]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_12975,plain,
% 7.44/1.51      ( k6_tmap_1(sK2,u1_struct_0(sK2)) = k8_tmap_1(sK2,sK2) ),
% 7.44/1.51      inference(global_propositional_subsumption,
% 7.44/1.51                [status(thm)],
% 7.44/1.51                [c_12807,c_41,c_40,c_39,c_55,c_58,c_82,c_85,c_88,c_106]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_14899,plain,
% 7.44/1.51      ( g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,u1_struct_0(sK2))) = k8_tmap_1(sK2,sK2)
% 7.44/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.44/1.51      | v2_struct_0(sK2) = iProver_top
% 7.44/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.44/1.51      inference(light_normalisation,[status(thm)],[c_14851,c_12975]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_15379,plain,
% 7.44/1.51      ( g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,u1_struct_0(sK2))) = k8_tmap_1(sK2,sK2) ),
% 7.44/1.51      inference(global_propositional_subsumption,
% 7.44/1.51                [status(thm)],
% 7.44/1.51                [c_14899,c_42,c_43,c_44]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_26,plain,
% 7.44/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.44/1.51      | ~ v2_pre_topc(X1)
% 7.44/1.51      | v2_struct_0(X1)
% 7.44/1.51      | ~ l1_pre_topc(X1)
% 7.44/1.51      | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
% 7.44/1.51      inference(cnf_transformation,[],[f98]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_6269,plain,
% 7.44/1.51      ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
% 7.44/1.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.44/1.51      | v2_pre_topc(X0) != iProver_top
% 7.44/1.51      | v2_struct_0(X0) = iProver_top
% 7.44/1.51      | l1_pre_topc(X0) != iProver_top ),
% 7.44/1.51      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_14852,plain,
% 7.44/1.51      ( u1_pre_topc(k6_tmap_1(sK2,u1_struct_0(sK2))) = k5_tmap_1(sK2,u1_struct_0(sK2))
% 7.44/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.44/1.51      | v2_struct_0(sK2) = iProver_top
% 7.44/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.44/1.51      inference(superposition,[status(thm)],[c_14845,c_6269]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_14890,plain,
% 7.44/1.51      ( k5_tmap_1(sK2,u1_struct_0(sK2)) = u1_pre_topc(k8_tmap_1(sK2,sK2))
% 7.44/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.44/1.51      | v2_struct_0(sK2) = iProver_top
% 7.44/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.44/1.51      inference(light_normalisation,[status(thm)],[c_14852,c_12975]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_15316,plain,
% 7.44/1.51      ( k5_tmap_1(sK2,u1_struct_0(sK2)) = u1_pre_topc(k8_tmap_1(sK2,sK2)) ),
% 7.44/1.51      inference(global_propositional_subsumption,
% 7.44/1.51                [status(thm)],
% 7.44/1.51                [c_14890,c_42,c_43,c_44]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_15381,plain,
% 7.44/1.51      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(k8_tmap_1(sK2,sK2))) = k8_tmap_1(sK2,sK2) ),
% 7.44/1.51      inference(light_normalisation,[status(thm)],[c_15379,c_15316]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_15387,plain,
% 7.44/1.51      ( g1_pre_topc(X0,X1) != k8_tmap_1(sK2,sK2)
% 7.44/1.51      | u1_struct_0(sK2) = X0
% 7.44/1.51      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 7.44/1.51      inference(superposition,[status(thm)],[c_15381,c_6281]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_87,plain,
% 7.44/1.51      ( m1_pre_topc(X0,X1) != iProver_top
% 7.44/1.51      | v2_pre_topc(X1) != iProver_top
% 7.44/1.51      | v2_struct_0(X1) = iProver_top
% 7.44/1.51      | l1_pre_topc(X1) != iProver_top
% 7.44/1.51      | l1_pre_topc(k8_tmap_1(X1,X0)) = iProver_top ),
% 7.44/1.51      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_89,plain,
% 7.44/1.51      ( m1_pre_topc(sK2,sK2) != iProver_top
% 7.44/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.44/1.51      | v2_struct_0(sK2) = iProver_top
% 7.44/1.51      | l1_pre_topc(k8_tmap_1(sK2,sK2)) = iProver_top
% 7.44/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_87]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_14853,plain,
% 7.44/1.51      ( u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK2))) = u1_struct_0(sK2)
% 7.44/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.44/1.51      | v2_struct_0(sK2) = iProver_top
% 7.44/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.44/1.51      inference(superposition,[status(thm)],[c_14845,c_6268]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_14881,plain,
% 7.44/1.51      ( u1_struct_0(k8_tmap_1(sK2,sK2)) = u1_struct_0(sK2)
% 7.44/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.44/1.51      | v2_struct_0(sK2) = iProver_top
% 7.44/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.44/1.51      inference(light_normalisation,[status(thm)],[c_14853,c_12975]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_14998,plain,
% 7.44/1.51      ( u1_struct_0(k8_tmap_1(sK2,sK2)) = u1_struct_0(sK2) ),
% 7.44/1.51      inference(global_propositional_subsumption,
% 7.44/1.51                [status(thm)],
% 7.44/1.51                [c_14881,c_42,c_43,c_44]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_15029,plain,
% 7.44/1.51      ( m1_subset_1(u1_pre_topc(k8_tmap_1(sK2,sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
% 7.44/1.51      | l1_pre_topc(k8_tmap_1(sK2,sK2)) != iProver_top ),
% 7.44/1.51      inference(superposition,[status(thm)],[c_14998,c_6285]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_15388,plain,
% 7.44/1.51      ( g1_pre_topc(X0,X1) != k8_tmap_1(sK2,sK2)
% 7.44/1.51      | u1_struct_0(sK2) = X0
% 7.44/1.51      | m1_subset_1(u1_pre_topc(k8_tmap_1(sK2,sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
% 7.44/1.51      inference(superposition,[status(thm)],[c_15381,c_6281]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_15805,plain,
% 7.44/1.51      ( u1_struct_0(sK2) = X0
% 7.44/1.51      | g1_pre_topc(X0,X1) != k8_tmap_1(sK2,sK2) ),
% 7.44/1.51      inference(global_propositional_subsumption,
% 7.44/1.51                [status(thm)],
% 7.44/1.51                [c_15387,c_42,c_43,c_44,c_56,c_89,c_15029,c_15388]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_15806,plain,
% 7.44/1.51      ( g1_pre_topc(X0,X1) != k8_tmap_1(sK2,sK2)
% 7.44/1.51      | u1_struct_0(sK2) = X0 ),
% 7.44/1.51      inference(renaming,[status(thm)],[c_15805]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_29333,plain,
% 7.44/1.51      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK2)
% 7.44/1.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2) ),
% 7.44/1.51      inference(superposition,[status(thm)],[c_29040,c_15806]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_61,plain,
% 7.44/1.51      ( ~ m1_pre_topc(sK2,sK2)
% 7.44/1.51      | ~ l1_pre_topc(sK2)
% 7.44/1.51      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_29]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_64,plain,
% 7.44/1.51      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2)
% 7.44/1.51      | ~ m1_pre_topc(sK2,sK2)
% 7.44/1.51      | ~ l1_pre_topc(sK2) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_28]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_129,plain,
% 7.44/1.51      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 7.44/1.51      | ~ l1_pre_topc(sK2) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_5]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_6693,plain,
% 7.44/1.51      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 7.44/1.51      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 7.44/1.51      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_6691]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_7288,plain,
% 7.44/1.51      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2)
% 7.44/1.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 7.44/1.51      | ~ l1_pre_topc(sK2) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_7286]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_6969,plain,
% 7.44/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 7.44/1.51      | X2 = u1_struct_0(X1)
% 7.44/1.51      | g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(X1),X0) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_9]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_7229,plain,
% 7.44/1.51      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.44/1.51      | X1 = u1_struct_0(X0)
% 7.44/1.51      | g1_pre_topc(X1,X2) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_6969]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_8575,plain,
% 7.44/1.51      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.44/1.51      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 7.44/1.51      | u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(X0) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_7229]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_8577,plain,
% 7.44/1.51      ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 7.44/1.51      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 7.44/1.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_8575]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_29746,plain,
% 7.44/1.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2) ),
% 7.44/1.51      inference(global_propositional_subsumption,
% 7.44/1.51                [status(thm)],
% 7.44/1.51                [c_29333,c_39,c_55,c_61,c_64,c_129,c_6693,c_7288,c_8577]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_29804,plain,
% 7.44/1.51      ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
% 7.44/1.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
% 7.44/1.51      inference(superposition,[status(thm)],[c_29746,c_6285]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_29750,plain,
% 7.44/1.51      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 7.44/1.51      inference(demodulation,[status(thm)],[c_29746,c_29040]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_30228,plain,
% 7.44/1.51      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1)
% 7.44/1.51      | u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = X1
% 7.44/1.51      | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
% 7.44/1.51      inference(superposition,[status(thm)],[c_29750,c_6282]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_31026,plain,
% 7.44/1.51      ( u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = X1
% 7.44/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1) ),
% 7.44/1.51      inference(global_propositional_subsumption,
% 7.44/1.51                [status(thm)],
% 7.44/1.51                [c_29343,c_44,c_56,c_65,c_7289,c_29804,c_30228]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_31027,plain,
% 7.44/1.51      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1)
% 7.44/1.51      | u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = X1 ),
% 7.44/1.51      inference(renaming,[status(thm)],[c_31026]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_9056,plain,
% 7.44/1.51      ( m1_pre_topc(X0,sK3) != iProver_top
% 7.44/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2) = iProver_top
% 7.44/1.51      | l1_pre_topc(sK3) != iProver_top ),
% 7.44/1.51      inference(superposition,[status(thm)],[c_6267,c_9048]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_9068,plain,
% 7.44/1.51      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2) = iProver_top
% 7.44/1.51      | m1_pre_topc(X0,sK3) != iProver_top ),
% 7.44/1.51      inference(global_propositional_subsumption,
% 7.44/1.51                [status(thm)],
% 7.44/1.51                [c_9056,c_44,c_6777]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_9069,plain,
% 7.44/1.51      ( m1_pre_topc(X0,sK3) != iProver_top
% 7.44/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2) = iProver_top ),
% 7.44/1.51      inference(renaming,[status(thm)],[c_9068]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_9556,plain,
% 7.44/1.51      ( k6_tmap_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = k8_tmap_1(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 7.44/1.51      | m1_pre_topc(X0,sK3) != iProver_top
% 7.44/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.44/1.51      | v2_struct_0(sK2) = iProver_top
% 7.44/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.44/1.51      inference(superposition,[status(thm)],[c_9069,c_6257]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_10021,plain,
% 7.44/1.51      ( m1_pre_topc(X0,sK3) != iProver_top
% 7.44/1.51      | k6_tmap_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = k8_tmap_1(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 7.44/1.51      inference(global_propositional_subsumption,
% 7.44/1.51                [status(thm)],
% 7.44/1.51                [c_9556,c_42,c_43,c_44]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_10022,plain,
% 7.44/1.51      ( k6_tmap_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = k8_tmap_1(sK2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 7.44/1.51      | m1_pre_topc(X0,sK3) != iProver_top ),
% 7.44/1.51      inference(renaming,[status(thm)],[c_10021]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_10030,plain,
% 7.44/1.51      ( k6_tmap_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = k8_tmap_1(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
% 7.44/1.51      | l1_pre_topc(sK3) != iProver_top ),
% 7.44/1.51      inference(superposition,[status(thm)],[c_6264,c_10022]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_10033,plain,
% 7.44/1.51      ( k8_tmap_1(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k8_tmap_1(sK2,sK3)
% 7.44/1.51      | l1_pre_topc(sK3) != iProver_top ),
% 7.44/1.51      inference(light_normalisation,
% 7.44/1.51                [status(thm)],
% 7.44/1.51                [c_10030,c_8283,c_9936]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_10047,plain,
% 7.44/1.51      ( k8_tmap_1(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = k8_tmap_1(sK2,sK3) ),
% 7.44/1.51      inference(global_propositional_subsumption,
% 7.44/1.51                [status(thm)],
% 7.44/1.51                [c_10033,c_44,c_6777]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_6275,plain,
% 7.44/1.51      ( m1_pre_topc(X0,X1) != iProver_top
% 7.44/1.51      | v2_pre_topc(X1) != iProver_top
% 7.44/1.51      | v2_struct_0(X1) = iProver_top
% 7.44/1.51      | l1_pre_topc(X1) != iProver_top
% 7.44/1.51      | l1_pre_topc(k8_tmap_1(X1,X0)) = iProver_top ),
% 7.44/1.51      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_10050,plain,
% 7.44/1.51      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK2) != iProver_top
% 7.44/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.44/1.51      | v2_struct_0(sK2) = iProver_top
% 7.44/1.51      | l1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top
% 7.44/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.44/1.51      inference(superposition,[status(thm)],[c_10047,c_6275]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_10173,plain,
% 7.44/1.51      ( l1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top ),
% 7.44/1.51      inference(global_propositional_subsumption,
% 7.44/1.51                [status(thm)],
% 7.44/1.51                [c_10050,c_42,c_43,c_44,c_46,c_9253]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_10178,plain,
% 7.44/1.51      ( g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3)
% 7.44/1.51      | v1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 7.44/1.51      inference(superposition,[status(thm)],[c_10173,c_6289]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_6703,plain,
% 7.44/1.51      ( ~ l1_pre_topc(k8_tmap_1(X0,X1))
% 7.44/1.51      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
% 7.44/1.51      | g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X1)),u1_pre_topc(k8_tmap_1(X0,X1))) = k8_tmap_1(X0,X1) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_1]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_7981,plain,
% 7.44/1.51      ( ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
% 7.44/1.51      | ~ v1_pre_topc(k8_tmap_1(sK2,sK3))
% 7.44/1.51      | g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_6703]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_7982,plain,
% 7.44/1.51      ( g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3)
% 7.44/1.51      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
% 7.44/1.51      | v1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 7.44/1.51      inference(predicate_to_equality,[status(thm)],[c_7981]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_6273,plain,
% 7.44/1.51      ( m1_pre_topc(X0,X1) != iProver_top
% 7.44/1.51      | v2_pre_topc(X1) != iProver_top
% 7.44/1.51      | v2_struct_0(X1) = iProver_top
% 7.44/1.51      | l1_pre_topc(X1) != iProver_top
% 7.44/1.51      | v1_pre_topc(k8_tmap_1(X1,X0)) = iProver_top ),
% 7.44/1.51      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_10052,plain,
% 7.44/1.51      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK2) != iProver_top
% 7.44/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.44/1.51      | v2_struct_0(sK2) = iProver_top
% 7.44/1.51      | l1_pre_topc(sK2) != iProver_top
% 7.44/1.51      | v1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top ),
% 7.44/1.51      inference(superposition,[status(thm)],[c_10047,c_6273]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_10240,plain,
% 7.44/1.51      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK2) != iProver_top
% 7.44/1.51      | v1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top ),
% 7.44/1.51      inference(global_propositional_subsumption,
% 7.44/1.51                [status(thm)],
% 7.44/1.51                [c_10052,c_42,c_43,c_44]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_10246,plain,
% 7.44/1.51      ( m1_pre_topc(sK3,sK2) != iProver_top
% 7.44/1.51      | l1_pre_topc(sK2) != iProver_top
% 7.44/1.51      | v1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top ),
% 7.44/1.51      inference(superposition,[status(thm)],[c_6267,c_10240]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_11441,plain,
% 7.44/1.51      ( g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3) ),
% 7.44/1.51      inference(global_propositional_subsumption,
% 7.44/1.51                [status(thm)],
% 7.44/1.51                [c_10178,c_42,c_43,c_44,c_46,c_7982,c_9253,c_10246]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_13307,plain,
% 7.44/1.51      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3) ),
% 7.44/1.51      inference(demodulation,[status(thm)],[c_13303,c_11441]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_13749,plain,
% 7.44/1.51      ( g1_pre_topc(X0,X1) != k8_tmap_1(sK2,sK3)
% 7.44/1.51      | u1_pre_topc(k8_tmap_1(sK2,sK3)) = X1
% 7.44/1.51      | m1_subset_1(u1_pre_topc(k8_tmap_1(sK2,sK3)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
% 7.44/1.51      inference(superposition,[status(thm)],[c_13307,c_6282]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_13344,plain,
% 7.44/1.51      ( m1_subset_1(u1_pre_topc(k8_tmap_1(sK2,sK3)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
% 7.44/1.51      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 7.44/1.51      inference(superposition,[status(thm)],[c_13303,c_6285]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_16518,plain,
% 7.44/1.51      ( u1_pre_topc(k8_tmap_1(sK2,sK3)) = X1
% 7.44/1.51      | g1_pre_topc(X0,X1) != k8_tmap_1(sK2,sK3) ),
% 7.44/1.51      inference(global_propositional_subsumption,
% 7.44/1.51                [status(thm)],
% 7.44/1.51                [c_13749,c_42,c_43,c_44,c_46,c_9253,c_13344]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_16519,plain,
% 7.44/1.51      ( g1_pre_topc(X0,X1) != k8_tmap_1(sK2,sK3)
% 7.44/1.51      | u1_pre_topc(k8_tmap_1(sK2,sK3)) = X1 ),
% 7.44/1.51      inference(renaming,[status(thm)],[c_16518]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_29331,plain,
% 7.44/1.51      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
% 7.44/1.51      | u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_pre_topc(k8_tmap_1(sK2,sK3)) ),
% 7.44/1.51      inference(superposition,[status(thm)],[c_29040,c_16519]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_5561,plain,
% 7.44/1.51      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 7.44/1.51      theory(equality) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_5576,plain,
% 7.44/1.51      ( u1_struct_0(sK2) = u1_struct_0(sK2) | sK2 != sK2 ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_5561]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_5562,plain,
% 7.44/1.51      ( X0 != X1 | u1_pre_topc(X0) = u1_pre_topc(X1) ),
% 7.44/1.51      theory(equality) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_5577,plain,
% 7.44/1.51      ( u1_pre_topc(sK2) = u1_pre_topc(sK2) | sK2 != sK2 ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_5562]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_5557,plain,( X0 = X0 ),theory(equality) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_5590,plain,
% 7.44/1.51      ( sK2 = sK2 ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_5557]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_7559,plain,
% 7.44/1.51      ( k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK3) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_5557]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_5558,plain,( X0 != X1 | X2 != X1 | X0 = X2 ),theory(equality) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_7041,plain,
% 7.44/1.51      ( X0 != X1 | k8_tmap_1(sK2,sK3) != X1 | k8_tmap_1(sK2,sK3) = X0 ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_5558]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_7558,plain,
% 7.44/1.51      ( X0 != k8_tmap_1(sK2,sK3)
% 7.44/1.51      | k8_tmap_1(sK2,sK3) = X0
% 7.44/1.51      | k8_tmap_1(sK2,sK3) != k8_tmap_1(sK2,sK3) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_7041]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_7980,plain,
% 7.44/1.51      ( k8_tmap_1(sK2,sK3) != k8_tmap_1(sK2,sK3)
% 7.44/1.51      | k8_tmap_1(sK2,sK3) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3)))
% 7.44/1.51      | g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) != k8_tmap_1(sK2,sK3) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_7558]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_5563,plain,
% 7.44/1.51      ( X0 != X1 | X2 != X3 | g1_pre_topc(X0,X2) = g1_pre_topc(X1,X3) ),
% 7.44/1.51      theory(equality) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_6864,plain,
% 7.44/1.51      ( X0 != u1_pre_topc(X1)
% 7.44/1.51      | X2 != u1_struct_0(X1)
% 7.44/1.51      | g1_pre_topc(X2,X0) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_5563]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_7137,plain,
% 7.44/1.51      ( X0 != u1_struct_0(X1)
% 7.44/1.51      | g1_pre_topc(X0,u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
% 7.44/1.51      | u1_pre_topc(X2) != u1_pre_topc(X1) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_6864]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_8429,plain,
% 7.44/1.51      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
% 7.44/1.51      | u1_pre_topc(X1) != u1_pre_topc(X2)
% 7.44/1.51      | u1_struct_0(X0) != u1_struct_0(X2) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_7137]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_8430,plain,
% 7.44/1.51      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 7.44/1.51      | u1_pre_topc(sK2) != u1_pre_topc(sK2)
% 7.44/1.51      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_8429]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_6839,plain,
% 7.44/1.51      ( k8_tmap_1(sK2,sK3) != X0
% 7.44/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != X0
% 7.44/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_5558]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_10909,plain,
% 7.44/1.51      ( k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 7.44/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
% 7.44/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_6839]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_10914,plain,
% 7.44/1.51      ( k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 7.44/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
% 7.44/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_10909]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_10978,plain,
% 7.44/1.51      ( X0 != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
% 7.44/1.51      | k8_tmap_1(sK2,sK3) = X0
% 7.44/1.51      | k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_7041]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_16866,plain,
% 7.44/1.51      ( X0 != g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3)))
% 7.44/1.51      | k8_tmap_1(sK2,sK3) = X0
% 7.44/1.51      | k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_10978]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_18517,plain,
% 7.44/1.51      ( k8_tmap_1(sK2,sK3) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X1))
% 7.44/1.51      | k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3)))
% 7.44/1.51      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_16866]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_18519,plain,
% 7.44/1.51      ( k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3)))
% 7.44/1.51      | k8_tmap_1(sK2,sK3) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 7.44/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_18517]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_18518,plain,
% 7.44/1.51      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3)))
% 7.44/1.51      | u1_pre_topc(X1) != u1_pre_topc(k8_tmap_1(sK2,sK3))
% 7.44/1.51      | u1_struct_0(X0) != u1_struct_0(k8_tmap_1(sK2,sK3)) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_8429]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_18520,plain,
% 7.44/1.51      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3)))
% 7.44/1.51      | u1_pre_topc(sK2) != u1_pre_topc(k8_tmap_1(sK2,sK3))
% 7.44/1.51      | u1_struct_0(sK2) != u1_struct_0(k8_tmap_1(sK2,sK3)) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_18518]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_18,plain,
% 7.44/1.51      ( ~ v1_tsep_1(X0,X1)
% 7.44/1.51      | ~ m1_pre_topc(X0,X1)
% 7.44/1.51      | v3_pre_topc(u1_struct_0(X0),X1)
% 7.44/1.51      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.44/1.51      | ~ l1_pre_topc(X1) ),
% 7.44/1.51      inference(cnf_transformation,[],[f115]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_260,plain,
% 7.44/1.51      ( v3_pre_topc(u1_struct_0(X0),X1)
% 7.44/1.51      | ~ m1_pre_topc(X0,X1)
% 7.44/1.51      | ~ v1_tsep_1(X0,X1)
% 7.44/1.51      | ~ l1_pre_topc(X1) ),
% 7.44/1.51      inference(global_propositional_subsumption,
% 7.44/1.51                [status(thm)],
% 7.44/1.51                [c_18,c_30]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_261,plain,
% 7.44/1.51      ( ~ v1_tsep_1(X0,X1)
% 7.44/1.51      | ~ m1_pre_topc(X0,X1)
% 7.44/1.51      | v3_pre_topc(u1_struct_0(X0),X1)
% 7.44/1.51      | ~ l1_pre_topc(X1) ),
% 7.44/1.51      inference(renaming,[status(thm)],[c_260]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_36,negated_conjecture,
% 7.44/1.51      ( v1_tsep_1(sK3,sK2)
% 7.44/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
% 7.44/1.51      inference(cnf_transformation,[],[f110]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_338,plain,
% 7.44/1.51      ( v1_tsep_1(sK3,sK2)
% 7.44/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
% 7.44/1.51      inference(prop_impl,[status(thm)],[c_36]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_726,plain,
% 7.44/1.51      ( ~ m1_pre_topc(X0,X1)
% 7.44/1.51      | v3_pre_topc(u1_struct_0(X0),X1)
% 7.44/1.51      | ~ l1_pre_topc(X1)
% 7.44/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
% 7.44/1.51      | sK3 != X0
% 7.44/1.51      | sK2 != X1 ),
% 7.44/1.51      inference(resolution_lifted,[status(thm)],[c_261,c_338]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_727,plain,
% 7.44/1.51      ( ~ m1_pre_topc(sK3,sK2)
% 7.44/1.51      | v3_pre_topc(u1_struct_0(sK3),sK2)
% 7.44/1.51      | ~ l1_pre_topc(sK2)
% 7.44/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
% 7.44/1.51      inference(unflattening,[status(thm)],[c_726]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_729,plain,
% 7.44/1.51      ( v3_pre_topc(u1_struct_0(sK3),sK2)
% 7.44/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
% 7.44/1.51      inference(global_propositional_subsumption,
% 7.44/1.51                [status(thm)],
% 7.44/1.51                [c_727,c_39,c_37]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_6251,plain,
% 7.44/1.51      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
% 7.44/1.51      | v3_pre_topc(u1_struct_0(sK3),sK2) = iProver_top ),
% 7.44/1.51      inference(predicate_to_equality,[status(thm)],[c_729]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_3,plain,
% 7.44/1.51      ( r2_hidden(X0,u1_pre_topc(X1))
% 7.44/1.51      | ~ v3_pre_topc(X0,X1)
% 7.44/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.44/1.51      | ~ l1_pre_topc(X1) ),
% 7.44/1.51      inference(cnf_transformation,[],[f73]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_6287,plain,
% 7.44/1.51      ( r2_hidden(X0,u1_pre_topc(X1)) = iProver_top
% 7.44/1.51      | v3_pre_topc(X0,X1) != iProver_top
% 7.44/1.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.44/1.51      | l1_pre_topc(X1) != iProver_top ),
% 7.44/1.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_13135,plain,
% 7.44/1.51      ( r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) = iProver_top
% 7.44/1.51      | v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top
% 7.44/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.44/1.51      inference(superposition,[status(thm)],[c_13124,c_6287]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_6734,plain,
% 7.44/1.51      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
% 7.44/1.51      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 7.44/1.51      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.44/1.51      | ~ l1_pre_topc(X1) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_3]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_6894,plain,
% 7.44/1.51      ( r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2))
% 7.44/1.51      | ~ v3_pre_topc(u1_struct_0(sK3),sK2)
% 7.44/1.51      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.44/1.51      | ~ l1_pre_topc(sK2) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_6734]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_6895,plain,
% 7.44/1.51      ( r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) = iProver_top
% 7.44/1.51      | v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top
% 7.44/1.51      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.44/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.44/1.51      inference(predicate_to_equality,[status(thm)],[c_6894]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_14115,plain,
% 7.44/1.51      ( v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top
% 7.44/1.51      | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) = iProver_top ),
% 7.44/1.51      inference(global_propositional_subsumption,
% 7.44/1.51                [status(thm)],
% 7.44/1.51                [c_13135,c_44,c_46,c_6895,c_7026]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_14116,plain,
% 7.44/1.51      ( r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) = iProver_top
% 7.44/1.51      | v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top ),
% 7.44/1.51      inference(renaming,[status(thm)],[c_14115]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_25,plain,
% 7.44/1.51      ( ~ r2_hidden(X0,u1_pre_topc(X1))
% 7.44/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.44/1.51      | ~ v2_pre_topc(X1)
% 7.44/1.51      | v2_struct_0(X1)
% 7.44/1.51      | ~ l1_pre_topc(X1)
% 7.44/1.51      | k5_tmap_1(X1,X0) = u1_pre_topc(X1) ),
% 7.44/1.51      inference(cnf_transformation,[],[f95]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_6270,plain,
% 7.44/1.51      ( k5_tmap_1(X0,X1) = u1_pre_topc(X0)
% 7.44/1.51      | r2_hidden(X1,u1_pre_topc(X0)) != iProver_top
% 7.44/1.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.44/1.51      | v2_pre_topc(X0) != iProver_top
% 7.44/1.51      | v2_struct_0(X0) = iProver_top
% 7.44/1.51      | l1_pre_topc(X0) != iProver_top ),
% 7.44/1.51      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_13129,plain,
% 7.44/1.51      ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(sK2)
% 7.44/1.51      | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top
% 7.44/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.44/1.51      | v2_struct_0(sK2) = iProver_top
% 7.44/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.44/1.51      inference(superposition,[status(thm)],[c_13124,c_6270]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_7090,plain,
% 7.44/1.51      ( ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
% 7.44/1.51      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.44/1.51      | ~ v2_pre_topc(X1)
% 7.44/1.51      | v2_struct_0(X1)
% 7.44/1.51      | ~ l1_pre_topc(X1)
% 7.44/1.51      | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(X1) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_25]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_10286,plain,
% 7.44/1.51      ( ~ r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2))
% 7.44/1.51      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.44/1.51      | ~ v2_pre_topc(sK2)
% 7.44/1.51      | v2_struct_0(sK2)
% 7.44/1.51      | ~ l1_pre_topc(sK2)
% 7.44/1.51      | k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(sK2) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_7090]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_10287,plain,
% 7.44/1.51      ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(sK2)
% 7.44/1.51      | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top
% 7.44/1.51      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.44/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.44/1.51      | v2_struct_0(sK2) = iProver_top
% 7.44/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.44/1.51      inference(predicate_to_equality,[status(thm)],[c_10286]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_23812,plain,
% 7.44/1.51      ( r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top
% 7.44/1.51      | k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(sK2) ),
% 7.44/1.51      inference(global_propositional_subsumption,
% 7.44/1.51                [status(thm)],
% 7.44/1.51                [c_13129,c_42,c_43,c_44,c_46,c_7026,c_10287]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_23813,plain,
% 7.44/1.51      ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(sK2)
% 7.44/1.51      | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top ),
% 7.44/1.51      inference(renaming,[status(thm)],[c_23812]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_13131,plain,
% 7.44/1.51      ( u1_pre_topc(k6_tmap_1(sK2,u1_struct_0(sK3))) = k5_tmap_1(sK2,u1_struct_0(sK3))
% 7.44/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.44/1.51      | v2_struct_0(sK2) = iProver_top
% 7.44/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.44/1.51      inference(superposition,[status(thm)],[c_13124,c_6269]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_13169,plain,
% 7.44/1.51      ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK2,sK3))
% 7.44/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.44/1.51      | v2_struct_0(sK2) = iProver_top
% 7.44/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.44/1.51      inference(light_normalisation,[status(thm)],[c_13131,c_9936]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_13625,plain,
% 7.44/1.51      ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK2,sK3)) ),
% 7.44/1.51      inference(global_propositional_subsumption,
% 7.44/1.51                [status(thm)],
% 7.44/1.51                [c_13169,c_42,c_43,c_44]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_23816,plain,
% 7.44/1.51      ( u1_pre_topc(k8_tmap_1(sK2,sK3)) = u1_pre_topc(sK2)
% 7.44/1.51      | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) != iProver_top ),
% 7.44/1.51      inference(demodulation,[status(thm)],[c_23813,c_13625]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_23821,plain,
% 7.44/1.51      ( u1_pre_topc(k8_tmap_1(sK2,sK3)) = u1_pre_topc(sK2)
% 7.44/1.51      | v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top ),
% 7.44/1.51      inference(superposition,[status(thm)],[c_14116,c_23816]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_24549,plain,
% 7.44/1.51      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
% 7.44/1.51      | u1_pre_topc(k8_tmap_1(sK2,sK3)) = u1_pre_topc(sK2) ),
% 7.44/1.51      inference(superposition,[status(thm)],[c_6251,c_23821]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_6964,plain,
% 7.44/1.51      ( X0 != X1 | X0 = u1_pre_topc(X2) | u1_pre_topc(X2) != X1 ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_5558]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_7071,plain,
% 7.44/1.51      ( X0 != u1_pre_topc(X1)
% 7.44/1.51      | X0 = u1_pre_topc(X2)
% 7.44/1.51      | u1_pre_topc(X2) != u1_pre_topc(X1) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_6964]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_7639,plain,
% 7.44/1.51      ( u1_pre_topc(X0) != u1_pre_topc(X1)
% 7.44/1.51      | u1_pre_topc(X2) != u1_pre_topc(X1)
% 7.44/1.51      | u1_pre_topc(X0) = u1_pre_topc(X2) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_7071]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_29180,plain,
% 7.44/1.51      ( u1_pre_topc(X0) != u1_pre_topc(X1)
% 7.44/1.51      | u1_pre_topc(X0) = u1_pre_topc(k8_tmap_1(sK2,sK3))
% 7.44/1.51      | u1_pre_topc(k8_tmap_1(sK2,sK3)) != u1_pre_topc(X1) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_7639]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_29181,plain,
% 7.44/1.51      ( u1_pre_topc(k8_tmap_1(sK2,sK3)) != u1_pre_topc(sK2)
% 7.44/1.51      | u1_pre_topc(sK2) = u1_pre_topc(k8_tmap_1(sK2,sK3))
% 7.44/1.51      | u1_pre_topc(sK2) != u1_pre_topc(sK2) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_29180]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_6991,plain,
% 7.44/1.51      ( X0 != X1 | X0 = u1_struct_0(X2) | u1_struct_0(X2) != X1 ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_5558]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_7087,plain,
% 7.44/1.51      ( X0 != u1_struct_0(X1)
% 7.44/1.51      | X0 = u1_struct_0(X2)
% 7.44/1.51      | u1_struct_0(X2) != u1_struct_0(X1) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_6991]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_7713,plain,
% 7.44/1.51      ( u1_struct_0(X0) != u1_struct_0(X1)
% 7.44/1.51      | u1_struct_0(X2) != u1_struct_0(X1)
% 7.44/1.51      | u1_struct_0(X0) = u1_struct_0(X2) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_7087]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_30290,plain,
% 7.44/1.51      ( u1_struct_0(X0) != u1_struct_0(X1)
% 7.44/1.51      | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(sK2,sK3))
% 7.44/1.51      | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(X1) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_7713]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_30291,plain,
% 7.44/1.51      ( u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(sK2)
% 7.44/1.51      | u1_struct_0(sK2) = u1_struct_0(k8_tmap_1(sK2,sK3))
% 7.44/1.51      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_30290]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_30469,plain,
% 7.44/1.51      ( u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_pre_topc(k8_tmap_1(sK2,sK3)) ),
% 7.44/1.51      inference(global_propositional_subsumption,
% 7.44/1.51                [status(thm)],
% 7.44/1.51                [c_29331,c_42,c_43,c_44,c_46,c_5576,c_5577,c_5590,c_7559,
% 7.44/1.51                 c_7980,c_7982,c_8430,c_9253,c_10246,c_10914,c_13160,
% 7.44/1.51                 c_18519,c_18520,c_24549,c_29181,c_30291]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_31029,plain,
% 7.44/1.51      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1)
% 7.44/1.51      | u1_pre_topc(k8_tmap_1(sK2,sK3)) = X1 ),
% 7.44/1.51      inference(demodulation,[status(thm)],[c_31027,c_30469]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_31035,plain,
% 7.44/1.51      ( u1_pre_topc(k8_tmap_1(sK2,sK3)) = u1_pre_topc(sK2) ),
% 7.44/1.51      inference(equality_resolution,[status(thm)],[c_31029]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_30472,plain,
% 7.44/1.51      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(k8_tmap_1(sK2,sK3))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 7.44/1.51      inference(demodulation,[status(thm)],[c_30469,c_29750]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_30473,plain,
% 7.44/1.51      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
% 7.44/1.51      inference(light_normalisation,[status(thm)],[c_30472,c_13307]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_24,plain,
% 7.44/1.51      ( r2_hidden(X0,u1_pre_topc(X1))
% 7.44/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.44/1.51      | ~ v2_pre_topc(X1)
% 7.44/1.51      | v2_struct_0(X1)
% 7.44/1.51      | ~ l1_pre_topc(X1)
% 7.44/1.51      | k5_tmap_1(X1,X0) != u1_pre_topc(X1) ),
% 7.44/1.51      inference(cnf_transformation,[],[f96]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_6271,plain,
% 7.44/1.51      ( k5_tmap_1(X0,X1) != u1_pre_topc(X0)
% 7.44/1.51      | r2_hidden(X1,u1_pre_topc(X0)) = iProver_top
% 7.44/1.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.44/1.51      | v2_pre_topc(X0) != iProver_top
% 7.44/1.51      | v2_struct_0(X0) = iProver_top
% 7.44/1.51      | l1_pre_topc(X0) != iProver_top ),
% 7.44/1.51      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_13628,plain,
% 7.44/1.51      ( u1_pre_topc(k8_tmap_1(sK2,sK3)) != u1_pre_topc(sK2)
% 7.44/1.51      | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) = iProver_top
% 7.44/1.51      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.44/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.44/1.51      | v2_struct_0(sK2) = iProver_top
% 7.44/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.44/1.51      inference(superposition,[status(thm)],[c_13625,c_6271]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_19375,plain,
% 7.44/1.51      ( u1_pre_topc(k8_tmap_1(sK2,sK3)) != u1_pre_topc(sK2)
% 7.44/1.51      | r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2)) = iProver_top ),
% 7.44/1.51      inference(global_propositional_subsumption,
% 7.44/1.51                [status(thm)],
% 7.44/1.51                [c_13628,c_42,c_43,c_44,c_46,c_7026]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_19377,plain,
% 7.44/1.51      ( r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2))
% 7.44/1.51      | u1_pre_topc(k8_tmap_1(sK2,sK3)) != u1_pre_topc(sK2) ),
% 7.44/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_19375]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_5566,plain,
% 7.44/1.51      ( ~ v3_pre_topc(X0,X1) | v3_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.44/1.51      theory(equality) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_6756,plain,
% 7.44/1.51      ( v3_pre_topc(X0,X1)
% 7.44/1.51      | ~ v3_pre_topc(u1_struct_0(X2),X3)
% 7.44/1.51      | X1 != X3
% 7.44/1.51      | X0 != u1_struct_0(X2) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_5566]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_7107,plain,
% 7.44/1.51      ( v3_pre_topc(sK1(X0,X1),X2)
% 7.44/1.51      | ~ v3_pre_topc(u1_struct_0(X1),X3)
% 7.44/1.51      | X2 != X3
% 7.44/1.51      | sK1(X0,X1) != u1_struct_0(X1) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_6756]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_10708,plain,
% 7.44/1.51      ( v3_pre_topc(sK1(X0,sK3),X1)
% 7.44/1.51      | ~ v3_pre_topc(u1_struct_0(sK3),sK2)
% 7.44/1.51      | X1 != sK2
% 7.44/1.51      | sK1(X0,sK3) != u1_struct_0(sK3) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_7107]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_10710,plain,
% 7.44/1.51      ( v3_pre_topc(sK1(sK2,sK3),sK2)
% 7.44/1.51      | ~ v3_pre_topc(u1_struct_0(sK3),sK2)
% 7.44/1.51      | sK1(sK2,sK3) != u1_struct_0(sK3)
% 7.44/1.51      | sK2 != sK2 ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_10708]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_2,plain,
% 7.44/1.51      ( ~ r2_hidden(X0,u1_pre_topc(X1))
% 7.44/1.51      | v3_pre_topc(X0,X1)
% 7.44/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.44/1.51      | ~ l1_pre_topc(X1) ),
% 7.44/1.51      inference(cnf_transformation,[],[f74]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_7091,plain,
% 7.44/1.51      ( ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
% 7.44/1.51      | v3_pre_topc(u1_struct_0(X0),X1)
% 7.44/1.51      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.44/1.51      | ~ l1_pre_topc(X1) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_2]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_7807,plain,
% 7.44/1.51      ( ~ r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK2))
% 7.44/1.51      | v3_pre_topc(u1_struct_0(sK3),sK2)
% 7.44/1.51      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.44/1.51      | ~ l1_pre_topc(sK2) ),
% 7.44/1.51      inference(instantiation,[status(thm)],[c_7091]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_15,plain,
% 7.44/1.51      ( v1_tsep_1(X0,X1)
% 7.44/1.51      | ~ m1_pre_topc(X0,X1)
% 7.44/1.51      | ~ v3_pre_topc(sK1(X1,X0),X1)
% 7.44/1.51      | ~ l1_pre_topc(X1) ),
% 7.44/1.51      inference(cnf_transformation,[],[f89]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_34,negated_conjecture,
% 7.44/1.51      ( ~ v1_tsep_1(sK3,sK2)
% 7.44/1.51      | ~ m1_pre_topc(sK3,sK2)
% 7.44/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
% 7.44/1.51      inference(cnf_transformation,[],[f112]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_336,plain,
% 7.44/1.51      ( ~ v1_tsep_1(sK3,sK2)
% 7.44/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
% 7.44/1.51      inference(prop_impl,[status(thm)],[c_37,c_34]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_712,plain,
% 7.44/1.51      ( ~ m1_pre_topc(X0,X1)
% 7.44/1.51      | ~ v3_pre_topc(sK1(X1,X0),X1)
% 7.44/1.51      | ~ l1_pre_topc(X1)
% 7.44/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
% 7.44/1.51      | sK3 != X0
% 7.44/1.51      | sK2 != X1 ),
% 7.44/1.51      inference(resolution_lifted,[status(thm)],[c_15,c_336]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_713,plain,
% 7.44/1.51      ( ~ m1_pre_topc(sK3,sK2)
% 7.44/1.51      | ~ v3_pre_topc(sK1(sK2,sK3),sK2)
% 7.44/1.51      | ~ l1_pre_topc(sK2)
% 7.44/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
% 7.44/1.51      inference(unflattening,[status(thm)],[c_712]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_715,plain,
% 7.44/1.51      ( ~ v3_pre_topc(sK1(sK2,sK3),sK2)
% 7.44/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
% 7.44/1.51      inference(global_propositional_subsumption,
% 7.44/1.51                [status(thm)],
% 7.44/1.51                [c_713,c_39,c_37]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_16,plain,
% 7.44/1.51      ( v1_tsep_1(X0,X1)
% 7.44/1.51      | ~ m1_pre_topc(X0,X1)
% 7.44/1.51      | ~ l1_pre_topc(X1)
% 7.44/1.51      | sK1(X1,X0) = u1_struct_0(X0) ),
% 7.44/1.51      inference(cnf_transformation,[],[f88]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_701,plain,
% 7.44/1.51      ( ~ m1_pre_topc(X0,X1)
% 7.44/1.51      | ~ l1_pre_topc(X1)
% 7.44/1.51      | sK1(X1,X0) = u1_struct_0(X0)
% 7.44/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
% 7.44/1.51      | sK3 != X0
% 7.44/1.51      | sK2 != X1 ),
% 7.44/1.51      inference(resolution_lifted,[status(thm)],[c_16,c_336]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_702,plain,
% 7.44/1.51      ( ~ m1_pre_topc(sK3,sK2)
% 7.44/1.51      | ~ l1_pre_topc(sK2)
% 7.44/1.51      | sK1(sK2,sK3) = u1_struct_0(sK3)
% 7.44/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
% 7.44/1.51      inference(unflattening,[status(thm)],[c_701]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(c_704,plain,
% 7.44/1.51      ( sK1(sK2,sK3) = u1_struct_0(sK3)
% 7.44/1.51      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
% 7.44/1.51      inference(global_propositional_subsumption,
% 7.44/1.51                [status(thm)],
% 7.44/1.51                [c_702,c_39,c_37]) ).
% 7.44/1.51  
% 7.44/1.51  cnf(contradiction,plain,
% 7.44/1.51      ( $false ),
% 7.44/1.51      inference(minisat,
% 7.44/1.51                [status(thm)],
% 7.44/1.51                [c_31035,c_30473,c_19377,c_10710,c_7807,c_7025,c_5590,
% 7.44/1.51                 c_715,c_704,c_37,c_39]) ).
% 7.44/1.51  
% 7.44/1.51  
% 7.44/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.44/1.51  
% 7.44/1.51  ------                               Statistics
% 7.44/1.51  
% 7.44/1.51  ------ General
% 7.44/1.51  
% 7.44/1.51  abstr_ref_over_cycles:                  0
% 7.44/1.51  abstr_ref_under_cycles:                 0
% 7.44/1.51  gc_basic_clause_elim:                   0
% 7.44/1.51  forced_gc_time:                         0
% 7.44/1.51  parsing_time:                           0.017
% 7.44/1.51  unif_index_cands_time:                  0.
% 7.44/1.51  unif_index_add_time:                    0.
% 7.44/1.51  orderings_time:                         0.
% 7.44/1.51  out_proof_time:                         0.025
% 7.44/1.51  total_time:                             0.765
% 7.44/1.51  num_of_symbols:                         52
% 7.44/1.51  num_of_terms:                           18759
% 7.44/1.51  
% 7.44/1.51  ------ Preprocessing
% 7.44/1.51  
% 7.44/1.51  num_of_splits:                          0
% 7.44/1.51  num_of_split_atoms:                     0
% 7.44/1.51  num_of_reused_defs:                     0
% 7.44/1.51  num_eq_ax_congr_red:                    24
% 7.44/1.51  num_of_sem_filtered_clauses:            1
% 7.44/1.51  num_of_subtypes:                        0
% 7.44/1.51  monotx_restored_types:                  0
% 7.44/1.51  sat_num_of_epr_types:                   0
% 7.44/1.51  sat_num_of_non_cyclic_types:            0
% 7.44/1.51  sat_guarded_non_collapsed_types:        0
% 7.44/1.51  num_pure_diseq_elim:                    0
% 7.44/1.51  simp_replaced_by:                       0
% 7.44/1.51  res_preprocessed:                       196
% 7.44/1.51  prep_upred:                             0
% 7.44/1.51  prep_unflattend:                        143
% 7.44/1.51  smt_new_axioms:                         0
% 7.44/1.51  pred_elim_cands:                        8
% 7.44/1.51  pred_elim:                              2
% 7.44/1.51  pred_elim_cl:                           1
% 7.44/1.51  pred_elim_cycles:                       9
% 7.44/1.51  merged_defs:                            2
% 7.44/1.51  merged_defs_ncl:                        0
% 7.44/1.51  bin_hyper_res:                          2
% 7.44/1.51  prep_cycles:                            4
% 7.44/1.51  pred_elim_time:                         0.098
% 7.44/1.51  splitting_time:                         0.
% 7.44/1.51  sem_filter_time:                        0.
% 7.44/1.51  monotx_time:                            0.
% 7.44/1.51  subtype_inf_time:                       0.
% 7.44/1.51  
% 7.44/1.51  ------ Problem properties
% 7.44/1.51  
% 7.44/1.51  clauses:                                40
% 7.44/1.51  conjectures:                            5
% 7.44/1.51  epr:                                    8
% 7.44/1.51  horn:                                   23
% 7.44/1.51  ground:                                 9
% 7.44/1.51  unary:                                  5
% 7.44/1.51  binary:                                 6
% 7.44/1.51  lits:                                   151
% 7.44/1.51  lits_eq:                                22
% 7.44/1.51  fd_pure:                                0
% 7.44/1.51  fd_pseudo:                              0
% 7.44/1.51  fd_cond:                                0
% 7.44/1.51  fd_pseudo_cond:                         5
% 7.44/1.51  ac_symbols:                             0
% 7.44/1.51  
% 7.44/1.51  ------ Propositional Solver
% 7.44/1.51  
% 7.44/1.51  prop_solver_calls:                      31
% 7.44/1.51  prop_fast_solver_calls:                 3990
% 7.44/1.51  smt_solver_calls:                       0
% 7.44/1.51  smt_fast_solver_calls:                  0
% 7.44/1.51  prop_num_of_clauses:                    6933
% 7.44/1.51  prop_preprocess_simplified:             14422
% 7.44/1.51  prop_fo_subsumed:                       278
% 7.44/1.51  prop_solver_time:                       0.
% 7.44/1.51  smt_solver_time:                        0.
% 7.44/1.51  smt_fast_solver_time:                   0.
% 7.44/1.51  prop_fast_solver_time:                  0.
% 7.44/1.51  prop_unsat_core_time:                   0.
% 7.44/1.51  
% 7.44/1.51  ------ QBF
% 7.44/1.51  
% 7.44/1.51  qbf_q_res:                              0
% 7.44/1.51  qbf_num_tautologies:                    0
% 7.44/1.51  qbf_prep_cycles:                        0
% 7.44/1.51  
% 7.44/1.51  ------ BMC1
% 7.44/1.51  
% 7.44/1.51  bmc1_current_bound:                     -1
% 7.44/1.51  bmc1_last_solved_bound:                 -1
% 7.44/1.51  bmc1_unsat_core_size:                   -1
% 7.44/1.51  bmc1_unsat_core_parents_size:           -1
% 7.44/1.51  bmc1_merge_next_fun:                    0
% 7.44/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.44/1.51  
% 7.44/1.51  ------ Instantiation
% 7.44/1.51  
% 7.44/1.51  inst_num_of_clauses:                    1897
% 7.44/1.51  inst_num_in_passive:                    644
% 7.44/1.51  inst_num_in_active:                     1052
% 7.44/1.51  inst_num_in_unprocessed:                201
% 7.44/1.51  inst_num_of_loops:                      1250
% 7.44/1.51  inst_num_of_learning_restarts:          0
% 7.44/1.51  inst_num_moves_active_passive:          192
% 7.44/1.51  inst_lit_activity:                      0
% 7.44/1.51  inst_lit_activity_moves:                0
% 7.44/1.51  inst_num_tautologies:                   0
% 7.44/1.51  inst_num_prop_implied:                  0
% 7.44/1.51  inst_num_existing_simplified:           0
% 7.44/1.51  inst_num_eq_res_simplified:             0
% 7.44/1.51  inst_num_child_elim:                    0
% 7.44/1.51  inst_num_of_dismatching_blockings:      3552
% 7.44/1.51  inst_num_of_non_proper_insts:           4784
% 7.44/1.51  inst_num_of_duplicates:                 0
% 7.44/1.51  inst_inst_num_from_inst_to_res:         0
% 7.44/1.51  inst_dismatching_checking_time:         0.
% 7.44/1.51  
% 7.44/1.51  ------ Resolution
% 7.44/1.51  
% 7.44/1.51  res_num_of_clauses:                     0
% 7.44/1.51  res_num_in_passive:                     0
% 7.44/1.51  res_num_in_active:                      0
% 7.44/1.51  res_num_of_loops:                       200
% 7.44/1.51  res_forward_subset_subsumed:            375
% 7.44/1.51  res_backward_subset_subsumed:           2
% 7.44/1.51  res_forward_subsumed:                   0
% 7.44/1.51  res_backward_subsumed:                  0
% 7.44/1.51  res_forward_subsumption_resolution:     6
% 7.44/1.51  res_backward_subsumption_resolution:    0
% 7.44/1.51  res_clause_to_clause_subsumption:       3128
% 7.44/1.51  res_orphan_elimination:                 0
% 7.44/1.51  res_tautology_del:                      557
% 7.44/1.51  res_num_eq_res_simplified:              0
% 7.44/1.51  res_num_sel_changes:                    0
% 7.44/1.51  res_moves_from_active_to_pass:          0
% 7.44/1.51  
% 7.44/1.51  ------ Superposition
% 7.44/1.51  
% 7.44/1.51  sup_time_total:                         0.
% 7.44/1.51  sup_time_generating:                    0.
% 7.44/1.51  sup_time_sim_full:                      0.
% 7.44/1.51  sup_time_sim_immed:                     0.
% 7.44/1.51  
% 7.44/1.51  sup_num_of_clauses:                     615
% 7.44/1.51  sup_num_in_active:                      233
% 7.44/1.51  sup_num_in_passive:                     382
% 7.44/1.51  sup_num_of_loops:                       249
% 7.44/1.51  sup_fw_superposition:                   592
% 7.44/1.51  sup_bw_superposition:                   608
% 7.44/1.51  sup_immediate_simplified:               416
% 7.44/1.51  sup_given_eliminated:                   1
% 7.44/1.51  comparisons_done:                       0
% 7.44/1.51  comparisons_avoided:                    26
% 7.44/1.51  
% 7.44/1.51  ------ Simplifications
% 7.44/1.51  
% 7.44/1.51  
% 7.44/1.51  sim_fw_subset_subsumed:                 60
% 7.44/1.51  sim_bw_subset_subsumed:                 31
% 7.44/1.51  sim_fw_subsumed:                        138
% 7.44/1.51  sim_bw_subsumed:                        28
% 7.44/1.51  sim_fw_subsumption_res:                 4
% 7.44/1.51  sim_bw_subsumption_res:                 0
% 7.44/1.51  sim_tautology_del:                      71
% 7.44/1.51  sim_eq_tautology_del:                   67
% 7.44/1.51  sim_eq_res_simp:                        0
% 7.44/1.51  sim_fw_demodulated:                     7
% 7.44/1.51  sim_bw_demodulated:                     12
% 7.44/1.51  sim_light_normalised:                   328
% 7.44/1.51  sim_joinable_taut:                      0
% 7.44/1.51  sim_joinable_simp:                      0
% 7.44/1.51  sim_ac_normalised:                      0
% 7.44/1.51  sim_smt_subsumption:                    0
% 7.44/1.51  
%------------------------------------------------------------------------------
