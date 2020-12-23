%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:10 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :  200 (1535 expanded)
%              Number of clauses        :  109 ( 391 expanded)
%              Number of leaves         :   22 ( 336 expanded)
%              Depth                    :   25
%              Number of atoms          :  866 (9621 expanded)
%              Number of equality atoms :  154 ( 506 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f61,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f62,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f61])).

fof(f64,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( v1_subset_1(sK3,u1_struct_0(X0))
          | ~ v3_tex_2(sK3,X0) )
        & ( ~ v1_subset_1(sK3,u1_struct_0(X0))
          | v3_tex_2(sK3,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( v1_subset_1(X1,u1_struct_0(X0))
              | ~ v3_tex_2(X1,X0) )
            & ( ~ v1_subset_1(X1,u1_struct_0(X0))
              | v3_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(sK2))
            | ~ v3_tex_2(X1,sK2) )
          & ( ~ v1_subset_1(X1,u1_struct_0(sK2))
            | v3_tex_2(X1,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v1_tdlat_3(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,
    ( ( v1_subset_1(sK3,u1_struct_0(sK2))
      | ~ v3_tex_2(sK3,sK2) )
    & ( ~ v1_subset_1(sK3,u1_struct_0(sK2))
      | v3_tex_2(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v1_tdlat_3(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f62,f64,f63])).

fof(f98,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f65])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f99,plain,
    ( ~ v1_subset_1(sK3,u1_struct_0(sK2))
    | v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f69,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f68,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f97,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f57,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f58,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f57])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK1(X0),X0)
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK1(X0),X0)
            & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f58,f59])).

fof(f87,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tex_2(X1,X0)
              & v3_pre_topc(X1,X0) )
           => v1_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f77,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f80,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f94,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f96,plain,(
    v1_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK0(X0,X1)) = X1
        & m1_pre_topc(sK0(X0,X1),X0)
        & ~ v2_struct_0(sK0(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK0(X0,X1)) = X1
            & m1_pre_topc(sK0(X0,X1),X0)
            & ~ v2_struct_0(sK0(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f55])).

fof(f86,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f95,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_tsep_1(X1,X0)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tdlat_3(X1)
            & v1_borsuk_1(X1,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tdlat_3(X1)
            & v1_borsuk_1(X1,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_borsuk_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                <=> v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <=> v4_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <=> v4_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                  | ~ v4_pre_topc(X2,X0) )
                & ( v4_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_borsuk_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                  | ~ v4_pre_topc(X2,X0) )
                & ( v4_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_borsuk_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f51])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f103,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f72,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f82,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f104,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f82])).

fof(f100,plain,
    ( v1_subset_1(sK3,u1_struct_0(sK2))
    | ~ v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | u1_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_tex_2(X1,X0)
              & v1_tops_1(X1,X0) )
           => v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | v1_subset_1(X0,X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_29,negated_conjecture,
    ( v3_tex_2(sK3,sK2)
    | ~ v1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_266,plain,
    ( v3_tex_2(sK3,sK2)
    | ~ v1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(prop_impl,[status(thm)],[c_29])).

cnf(c_521,plain,
    ( v3_tex_2(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 = X0
    | u1_struct_0(sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_266])).

cnf(c_522,plain,
    ( v3_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | u1_struct_0(sK2) = sK3 ),
    inference(unflattening,[status(thm)],[c_521])).

cnf(c_2026,plain,
    ( v3_tex_2(sK3,sK2)
    | u1_struct_0(sK2) = sK3 ),
    inference(prop_impl,[status(thm)],[c_30,c_522])).

cnf(c_2802,plain,
    ( u1_struct_0(sK2) = sK3
    | v3_tex_2(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2026])).

cnf(c_3,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_447,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_3,c_2])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1146,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_447,c_31])).

cnf(c_1147,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1146])).

cnf(c_2810,plain,
    ( k2_struct_0(sK2) = sK3
    | v3_tex_2(sK3,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2802,c_1147])).

cnf(c_23,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_26,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ v3_pre_topc(X0,X1)
    | v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_627,plain,
    ( ~ v3_tex_2(X0,X1)
    | v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_23,c_26])).

cnf(c_11,plain,
    ( ~ v1_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_645,plain,
    ( ~ v3_tex_2(X0,X1)
    | v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_627,c_11])).

cnf(c_15,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1085,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
    inference(resolution,[status(thm)],[c_645,c_15])).

cnf(c_1198,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1085,c_31])).

cnf(c_1199,plain,
    ( ~ v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v1_tdlat_3(sK2)
    | k2_pre_topc(sK2,X0) = u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1198])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_32,negated_conjecture,
    ( v1_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1203,plain,
    ( ~ v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_pre_topc(sK2,X0) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1199,c_34,c_32])).

cnf(c_1469,plain,
    ( ~ v3_tex_2(X0,sK2)
    | k2_pre_topc(sK2,X0) = u1_struct_0(sK2)
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_1203])).

cnf(c_1470,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | k2_pre_topc(sK2,sK3) = u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1469])).

cnf(c_2030,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | k2_pre_topc(sK2,sK3) = u1_struct_0(sK2) ),
    inference(prop_impl,[status(thm)],[c_1470])).

cnf(c_2798,plain,
    ( k2_pre_topc(sK2,sK3) = u1_struct_0(sK2)
    | v3_tex_2(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2030])).

cnf(c_2825,plain,
    ( k2_pre_topc(sK2,sK3) = k2_struct_0(sK2)
    | v3_tex_2(sK3,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2798,c_1147])).

cnf(c_3050,plain,
    ( k2_pre_topc(sK2,sK3) = k2_struct_0(sK2)
    | k2_struct_0(sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_2810,c_2825])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(sK0(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1267,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | v2_struct_0(X1)
    | u1_struct_0(sK0(X1,X0)) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_31])).

cnf(c_1268,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0)
    | v2_struct_0(sK2)
    | u1_struct_0(sK0(sK2,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_1267])).

cnf(c_1272,plain,
    ( v1_xboole_0(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | u1_struct_0(sK0(sK2,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1268,c_34])).

cnf(c_1273,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0)
    | u1_struct_0(sK0(sK2,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_1272])).

cnf(c_25,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_925,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_33])).

cnf(c_926,plain,
    ( ~ v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_xboole_0(X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_925])).

cnf(c_930,plain,
    ( ~ v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_926,c_34,c_31])).

cnf(c_1364,plain,
    ( ~ v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | u1_struct_0(sK0(sK2,X0)) = X0 ),
    inference(resolution,[status(thm)],[c_1273,c_930])).

cnf(c_1459,plain,
    ( ~ v3_tex_2(X0,sK2)
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
    | u1_struct_0(sK0(sK2,X0)) = X0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_1364])).

cnf(c_1460,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | u1_struct_0(sK0(sK2,sK3)) = sK3 ),
    inference(unflattening,[status(thm)],[c_1459])).

cnf(c_2799,plain,
    ( u1_struct_0(sK0(sK2,sK3)) = sK3
    | v3_tex_2(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1460])).

cnf(c_3051,plain,
    ( u1_struct_0(sK0(sK2,sK3)) = sK3
    | k2_struct_0(sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_2810,c_2799])).

cnf(c_19,plain,
    ( m1_pre_topc(sK0(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v1_xboole_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1151,plain,
    ( m1_pre_topc(sK0(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v1_xboole_0(X1)
    | v2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_31])).

cnf(c_1152,plain,
    ( m1_pre_topc(sK0(sK2,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1151])).

cnf(c_1156,plain,
    ( v1_xboole_0(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_pre_topc(sK0(sK2,X0),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1152,c_34])).

cnf(c_1157,plain,
    ( m1_pre_topc(sK0(sK2,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_1156])).

cnf(c_1378,plain,
    ( ~ v3_tex_2(X0,sK2)
    | m1_pre_topc(sK0(sK2,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[status(thm)],[c_1157,c_930])).

cnf(c_1449,plain,
    ( ~ v3_tex_2(X0,sK2)
    | m1_pre_topc(sK0(sK2,X0),sK2)
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_1378])).

cnf(c_1450,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | m1_pre_topc(sK0(sK2,sK3),sK2) ),
    inference(unflattening,[status(thm)],[c_1449])).

cnf(c_2800,plain,
    ( v3_tex_2(sK3,sK2) != iProver_top
    | m1_pre_topc(sK0(sK2,sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1450])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_13,plain,
    ( v1_borsuk_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_9,plain,
    ( ~ v1_borsuk_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v4_pre_topc(u1_struct_0(X0),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_208,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_borsuk_1(X0,X1)
    | v4_pre_topc(u1_struct_0(X0),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_10])).

cnf(c_209,plain,
    ( ~ v1_borsuk_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v4_pre_topc(u1_struct_0(X0),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_208])).

cnf(c_562,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v4_pre_topc(u1_struct_0(X0),X1)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_13,c_209])).

cnf(c_578,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v4_pre_topc(u1_struct_0(X0),X1)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_562,c_11])).

cnf(c_594,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | X1 != X3
    | k2_pre_topc(X3,X2) = X2
    | u1_struct_0(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_578])).

cnf(c_595,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,u1_struct_0(X0)) = u1_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_594])).

cnf(c_599,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,u1_struct_0(X0)) = u1_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_595,c_10])).

cnf(c_1228,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | k2_pre_topc(X1,u1_struct_0(X0)) = u1_struct_0(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_599,c_31])).

cnf(c_1229,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | v2_struct_0(sK2)
    | ~ v1_tdlat_3(sK2)
    | k2_pre_topc(sK2,u1_struct_0(X0)) = u1_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_1228])).

cnf(c_1233,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | k2_pre_topc(sK2,u1_struct_0(X0)) = u1_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1229,c_34,c_32])).

cnf(c_2801,plain,
    ( k2_pre_topc(sK2,u1_struct_0(X0)) = u1_struct_0(X0)
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1233])).

cnf(c_2977,plain,
    ( k2_pre_topc(sK2,u1_struct_0(sK0(sK2,sK3))) = u1_struct_0(sK0(sK2,sK3))
    | v3_tex_2(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2800,c_2801])).

cnf(c_3241,plain,
    ( k2_pre_topc(sK2,u1_struct_0(sK0(sK2,sK3))) = u1_struct_0(sK0(sK2,sK3))
    | k2_struct_0(sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_2810,c_2977])).

cnf(c_3378,plain,
    ( u1_struct_0(sK0(sK2,sK3)) = k2_pre_topc(sK2,sK3)
    | k2_struct_0(sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_3051,c_3241])).

cnf(c_3498,plain,
    ( k2_pre_topc(sK2,sK3) = sK3
    | k2_struct_0(sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_3378,c_3051])).

cnf(c_3540,plain,
    ( k2_struct_0(sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_3050,c_3498])).

cnf(c_6,plain,
    ( ~ l1_pre_topc(X0)
    | k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1172,plain,
    ( k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_31])).

cnf(c_1173,plain,
    ( k2_pre_topc(sK2,k2_struct_0(sK2)) = k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1172])).

cnf(c_3689,plain,
    ( k2_pre_topc(sK2,sK3) = sK3 ),
    inference(demodulation,[status(thm)],[c_3540,c_1173])).

cnf(c_2468,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2901,plain,
    ( k2_pre_topc(sK2,sK3) != X0
    | k2_pre_topc(sK2,sK3) = u1_struct_0(sK2)
    | u1_struct_0(sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_2468])).

cnf(c_2914,plain,
    ( k2_pre_topc(sK2,sK3) = u1_struct_0(sK2)
    | k2_pre_topc(sK2,sK3) != sK3
    | u1_struct_0(sK2) != sK3 ),
    inference(instantiation,[status(thm)],[c_2901])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ v1_subset_1(X0,X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_28,negated_conjecture,
    ( ~ v3_tex_2(sK3,sK2)
    | v1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_268,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | v1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(prop_impl,[status(thm)],[c_28])).

cnf(c_535,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X0))
    | u1_struct_0(sK2) != X0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_268])).

cnf(c_536,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | sK3 != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_1436,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
    | u1_struct_0(sK2) != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_536])).

cnf(c_1999,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | u1_struct_0(sK2) != sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_1436])).

cnf(c_2024,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | u1_struct_0(sK2) != sK3 ),
    inference(prop_impl,[status(thm)],[c_1999])).

cnf(c_2792,plain,
    ( u1_struct_0(sK2) != sK3
    | v3_tex_2(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2024])).

cnf(c_2815,plain,
    ( k2_struct_0(sK2) != sK3
    | v3_tex_2(sK3,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2792,c_1147])).

cnf(c_14,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_24,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_27,plain,
    ( v3_tex_2(X0,X1)
    | ~ v2_tex_2(X0,X1)
    | ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_461,plain,
    ( v3_tex_2(X0,X1)
    | ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_24,c_27])).

cnf(c_479,plain,
    ( v3_tex_2(X0,X1)
    | ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_461,c_11])).

cnf(c_1108,plain,
    ( v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != u1_struct_0(X1) ),
    inference(resolution,[status(thm)],[c_14,c_479])).

cnf(c_1177,plain,
    ( v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | k2_pre_topc(X1,X0) != u1_struct_0(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1108,c_31])).

cnf(c_1178,plain,
    ( v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v1_tdlat_3(sK2)
    | k2_pre_topc(sK2,X0) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1177])).

cnf(c_1182,plain,
    ( v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_pre_topc(sK2,X0) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1178,c_34,c_32])).

cnf(c_1479,plain,
    ( v3_tex_2(X0,sK2)
    | k2_pre_topc(sK2,X0) != u1_struct_0(sK2)
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_1182])).

cnf(c_1480,plain,
    ( v3_tex_2(sK3,sK2)
    | k2_pre_topc(sK2,sK3) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1479])).

cnf(c_1481,plain,
    ( k2_pre_topc(sK2,sK3) != u1_struct_0(sK2)
    | v3_tex_2(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1480])).

cnf(c_523,plain,
    ( u1_struct_0(sK2) = sK3
    | v3_tex_2(sK3,sK2) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_522])).

cnf(c_39,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3689,c_3540,c_2914,c_2815,c_1481,c_523,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:24:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.18/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/0.99  
% 2.18/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.18/0.99  
% 2.18/0.99  ------  iProver source info
% 2.18/0.99  
% 2.18/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.18/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.18/0.99  git: non_committed_changes: false
% 2.18/0.99  git: last_make_outside_of_git: false
% 2.18/0.99  
% 2.18/0.99  ------ 
% 2.18/0.99  
% 2.18/0.99  ------ Input Options
% 2.18/0.99  
% 2.18/0.99  --out_options                           all
% 2.18/0.99  --tptp_safe_out                         true
% 2.18/0.99  --problem_path                          ""
% 2.18/0.99  --include_path                          ""
% 2.18/0.99  --clausifier                            res/vclausify_rel
% 2.18/0.99  --clausifier_options                    --mode clausify
% 2.18/0.99  --stdin                                 false
% 2.18/0.99  --stats_out                             all
% 2.18/0.99  
% 2.18/0.99  ------ General Options
% 2.18/0.99  
% 2.18/0.99  --fof                                   false
% 2.18/0.99  --time_out_real                         305.
% 2.18/0.99  --time_out_virtual                      -1.
% 2.18/0.99  --symbol_type_check                     false
% 2.18/0.99  --clausify_out                          false
% 2.18/0.99  --sig_cnt_out                           false
% 2.18/0.99  --trig_cnt_out                          false
% 2.18/0.99  --trig_cnt_out_tolerance                1.
% 2.18/0.99  --trig_cnt_out_sk_spl                   false
% 2.18/0.99  --abstr_cl_out                          false
% 2.18/0.99  
% 2.18/0.99  ------ Global Options
% 2.18/0.99  
% 2.18/0.99  --schedule                              default
% 2.18/0.99  --add_important_lit                     false
% 2.18/0.99  --prop_solver_per_cl                    1000
% 2.18/0.99  --min_unsat_core                        false
% 2.18/0.99  --soft_assumptions                      false
% 2.18/0.99  --soft_lemma_size                       3
% 2.18/0.99  --prop_impl_unit_size                   0
% 2.18/0.99  --prop_impl_unit                        []
% 2.18/0.99  --share_sel_clauses                     true
% 2.18/0.99  --reset_solvers                         false
% 2.18/0.99  --bc_imp_inh                            [conj_cone]
% 2.18/0.99  --conj_cone_tolerance                   3.
% 2.18/0.99  --extra_neg_conj                        none
% 2.18/0.99  --large_theory_mode                     true
% 2.18/0.99  --prolific_symb_bound                   200
% 2.18/0.99  --lt_threshold                          2000
% 2.18/0.99  --clause_weak_htbl                      true
% 2.18/0.99  --gc_record_bc_elim                     false
% 2.18/0.99  
% 2.18/0.99  ------ Preprocessing Options
% 2.18/0.99  
% 2.18/0.99  --preprocessing_flag                    true
% 2.18/0.99  --time_out_prep_mult                    0.1
% 2.18/0.99  --splitting_mode                        input
% 2.18/0.99  --splitting_grd                         true
% 2.18/0.99  --splitting_cvd                         false
% 2.18/0.99  --splitting_cvd_svl                     false
% 2.18/0.99  --splitting_nvd                         32
% 2.18/0.99  --sub_typing                            true
% 2.18/0.99  --prep_gs_sim                           true
% 2.18/0.99  --prep_unflatten                        true
% 2.18/0.99  --prep_res_sim                          true
% 2.18/0.99  --prep_upred                            true
% 2.18/0.99  --prep_sem_filter                       exhaustive
% 2.18/0.99  --prep_sem_filter_out                   false
% 2.18/0.99  --pred_elim                             true
% 2.18/0.99  --res_sim_input                         true
% 2.18/0.99  --eq_ax_congr_red                       true
% 2.18/0.99  --pure_diseq_elim                       true
% 2.18/0.99  --brand_transform                       false
% 2.18/0.99  --non_eq_to_eq                          false
% 2.18/0.99  --prep_def_merge                        true
% 2.18/0.99  --prep_def_merge_prop_impl              false
% 2.18/0.99  --prep_def_merge_mbd                    true
% 2.18/0.99  --prep_def_merge_tr_red                 false
% 2.18/0.99  --prep_def_merge_tr_cl                  false
% 2.18/0.99  --smt_preprocessing                     true
% 2.18/0.99  --smt_ac_axioms                         fast
% 2.18/0.99  --preprocessed_out                      false
% 2.18/0.99  --preprocessed_stats                    false
% 2.18/0.99  
% 2.18/0.99  ------ Abstraction refinement Options
% 2.18/0.99  
% 2.18/0.99  --abstr_ref                             []
% 2.18/0.99  --abstr_ref_prep                        false
% 2.18/0.99  --abstr_ref_until_sat                   false
% 2.18/0.99  --abstr_ref_sig_restrict                funpre
% 2.18/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.18/0.99  --abstr_ref_under                       []
% 2.18/0.99  
% 2.18/0.99  ------ SAT Options
% 2.18/0.99  
% 2.18/0.99  --sat_mode                              false
% 2.18/0.99  --sat_fm_restart_options                ""
% 2.18/0.99  --sat_gr_def                            false
% 2.18/0.99  --sat_epr_types                         true
% 2.18/0.99  --sat_non_cyclic_types                  false
% 2.18/0.99  --sat_finite_models                     false
% 2.18/0.99  --sat_fm_lemmas                         false
% 2.18/0.99  --sat_fm_prep                           false
% 2.18/0.99  --sat_fm_uc_incr                        true
% 2.18/0.99  --sat_out_model                         small
% 2.18/0.99  --sat_out_clauses                       false
% 2.18/0.99  
% 2.18/0.99  ------ QBF Options
% 2.18/0.99  
% 2.18/0.99  --qbf_mode                              false
% 2.18/0.99  --qbf_elim_univ                         false
% 2.18/0.99  --qbf_dom_inst                          none
% 2.18/0.99  --qbf_dom_pre_inst                      false
% 2.18/0.99  --qbf_sk_in                             false
% 2.18/0.99  --qbf_pred_elim                         true
% 2.18/0.99  --qbf_split                             512
% 2.18/0.99  
% 2.18/0.99  ------ BMC1 Options
% 2.18/0.99  
% 2.18/0.99  --bmc1_incremental                      false
% 2.18/0.99  --bmc1_axioms                           reachable_all
% 2.18/0.99  --bmc1_min_bound                        0
% 2.18/0.99  --bmc1_max_bound                        -1
% 2.18/0.99  --bmc1_max_bound_default                -1
% 2.18/0.99  --bmc1_symbol_reachability              true
% 2.18/0.99  --bmc1_property_lemmas                  false
% 2.18/0.99  --bmc1_k_induction                      false
% 2.18/0.99  --bmc1_non_equiv_states                 false
% 2.18/0.99  --bmc1_deadlock                         false
% 2.18/0.99  --bmc1_ucm                              false
% 2.18/0.99  --bmc1_add_unsat_core                   none
% 2.18/0.99  --bmc1_unsat_core_children              false
% 2.18/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.18/0.99  --bmc1_out_stat                         full
% 2.18/0.99  --bmc1_ground_init                      false
% 2.18/0.99  --bmc1_pre_inst_next_state              false
% 2.18/0.99  --bmc1_pre_inst_state                   false
% 2.18/0.99  --bmc1_pre_inst_reach_state             false
% 2.18/0.99  --bmc1_out_unsat_core                   false
% 2.18/0.99  --bmc1_aig_witness_out                  false
% 2.18/0.99  --bmc1_verbose                          false
% 2.18/0.99  --bmc1_dump_clauses_tptp                false
% 2.18/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.18/0.99  --bmc1_dump_file                        -
% 2.18/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.18/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.18/0.99  --bmc1_ucm_extend_mode                  1
% 2.18/0.99  --bmc1_ucm_init_mode                    2
% 2.18/0.99  --bmc1_ucm_cone_mode                    none
% 2.18/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.18/0.99  --bmc1_ucm_relax_model                  4
% 2.18/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.18/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.18/0.99  --bmc1_ucm_layered_model                none
% 2.18/0.99  --bmc1_ucm_max_lemma_size               10
% 2.18/0.99  
% 2.18/0.99  ------ AIG Options
% 2.18/0.99  
% 2.18/0.99  --aig_mode                              false
% 2.18/0.99  
% 2.18/0.99  ------ Instantiation Options
% 2.18/0.99  
% 2.18/0.99  --instantiation_flag                    true
% 2.18/0.99  --inst_sos_flag                         false
% 2.18/0.99  --inst_sos_phase                        true
% 2.18/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.18/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.18/0.99  --inst_lit_sel_side                     num_symb
% 2.18/0.99  --inst_solver_per_active                1400
% 2.18/0.99  --inst_solver_calls_frac                1.
% 2.18/0.99  --inst_passive_queue_type               priority_queues
% 2.18/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.18/0.99  --inst_passive_queues_freq              [25;2]
% 2.18/0.99  --inst_dismatching                      true
% 2.18/0.99  --inst_eager_unprocessed_to_passive     true
% 2.18/0.99  --inst_prop_sim_given                   true
% 2.18/0.99  --inst_prop_sim_new                     false
% 2.18/0.99  --inst_subs_new                         false
% 2.18/0.99  --inst_eq_res_simp                      false
% 2.18/0.99  --inst_subs_given                       false
% 2.18/0.99  --inst_orphan_elimination               true
% 2.18/0.99  --inst_learning_loop_flag               true
% 2.18/0.99  --inst_learning_start                   3000
% 2.18/0.99  --inst_learning_factor                  2
% 2.18/0.99  --inst_start_prop_sim_after_learn       3
% 2.18/0.99  --inst_sel_renew                        solver
% 2.18/0.99  --inst_lit_activity_flag                true
% 2.18/0.99  --inst_restr_to_given                   false
% 2.18/0.99  --inst_activity_threshold               500
% 2.18/0.99  --inst_out_proof                        true
% 2.18/0.99  
% 2.18/0.99  ------ Resolution Options
% 2.18/0.99  
% 2.18/0.99  --resolution_flag                       true
% 2.18/0.99  --res_lit_sel                           adaptive
% 2.18/0.99  --res_lit_sel_side                      none
% 2.18/0.99  --res_ordering                          kbo
% 2.18/0.99  --res_to_prop_solver                    active
% 2.18/0.99  --res_prop_simpl_new                    false
% 2.18/0.99  --res_prop_simpl_given                  true
% 2.18/0.99  --res_passive_queue_type                priority_queues
% 2.18/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.18/0.99  --res_passive_queues_freq               [15;5]
% 2.18/0.99  --res_forward_subs                      full
% 2.18/0.99  --res_backward_subs                     full
% 2.18/0.99  --res_forward_subs_resolution           true
% 2.18/0.99  --res_backward_subs_resolution          true
% 2.18/0.99  --res_orphan_elimination                true
% 2.18/0.99  --res_time_limit                        2.
% 2.18/0.99  --res_out_proof                         true
% 2.18/0.99  
% 2.18/0.99  ------ Superposition Options
% 2.18/0.99  
% 2.18/0.99  --superposition_flag                    true
% 2.18/0.99  --sup_passive_queue_type                priority_queues
% 2.18/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.18/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.18/0.99  --demod_completeness_check              fast
% 2.18/0.99  --demod_use_ground                      true
% 2.18/0.99  --sup_to_prop_solver                    passive
% 2.18/0.99  --sup_prop_simpl_new                    true
% 2.18/0.99  --sup_prop_simpl_given                  true
% 2.18/0.99  --sup_fun_splitting                     false
% 2.18/0.99  --sup_smt_interval                      50000
% 2.18/0.99  
% 2.18/0.99  ------ Superposition Simplification Setup
% 2.18/0.99  
% 2.18/0.99  --sup_indices_passive                   []
% 2.18/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.18/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/0.99  --sup_full_bw                           [BwDemod]
% 2.18/0.99  --sup_immed_triv                        [TrivRules]
% 2.18/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.18/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/0.99  --sup_immed_bw_main                     []
% 2.18/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.18/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/0.99  
% 2.18/0.99  ------ Combination Options
% 2.18/0.99  
% 2.18/0.99  --comb_res_mult                         3
% 2.18/0.99  --comb_sup_mult                         2
% 2.18/0.99  --comb_inst_mult                        10
% 2.18/0.99  
% 2.18/0.99  ------ Debug Options
% 2.18/0.99  
% 2.18/0.99  --dbg_backtrace                         false
% 2.18/0.99  --dbg_dump_prop_clauses                 false
% 2.18/0.99  --dbg_dump_prop_clauses_file            -
% 2.18/0.99  --dbg_out_stat                          false
% 2.18/0.99  ------ Parsing...
% 2.18/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.18/0.99  
% 2.18/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 2.18/0.99  
% 2.18/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.18/0.99  
% 2.18/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.18/0.99  ------ Proving...
% 2.18/0.99  ------ Problem Properties 
% 2.18/0.99  
% 2.18/0.99  
% 2.18/0.99  clauses                                 15
% 2.18/0.99  conjectures                             0
% 2.18/0.99  EPR                                     0
% 2.18/0.99  Horn                                    14
% 2.18/0.99  unary                                   3
% 2.18/0.99  binary                                  8
% 2.18/0.99  lits                                    31
% 2.18/0.99  lits eq                                 13
% 2.18/0.99  fd_pure                                 0
% 2.18/0.99  fd_pseudo                               0
% 2.18/0.99  fd_cond                                 0
% 2.18/0.99  fd_pseudo_cond                          0
% 2.18/0.99  AC symbols                              0
% 2.18/0.99  
% 2.18/0.99  ------ Schedule dynamic 5 is on 
% 2.18/0.99  
% 2.18/0.99  ------ no conjectures: strip conj schedule 
% 2.18/0.99  
% 2.18/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 2.18/0.99  
% 2.18/0.99  
% 2.18/0.99  ------ 
% 2.18/0.99  Current options:
% 2.18/0.99  ------ 
% 2.18/0.99  
% 2.18/0.99  ------ Input Options
% 2.18/0.99  
% 2.18/0.99  --out_options                           all
% 2.18/0.99  --tptp_safe_out                         true
% 2.18/0.99  --problem_path                          ""
% 2.18/0.99  --include_path                          ""
% 2.18/0.99  --clausifier                            res/vclausify_rel
% 2.18/0.99  --clausifier_options                    --mode clausify
% 2.18/0.99  --stdin                                 false
% 2.18/0.99  --stats_out                             all
% 2.18/0.99  
% 2.18/0.99  ------ General Options
% 2.18/0.99  
% 2.18/0.99  --fof                                   false
% 2.18/0.99  --time_out_real                         305.
% 2.18/0.99  --time_out_virtual                      -1.
% 2.18/0.99  --symbol_type_check                     false
% 2.18/0.99  --clausify_out                          false
% 2.18/0.99  --sig_cnt_out                           false
% 2.18/0.99  --trig_cnt_out                          false
% 2.18/0.99  --trig_cnt_out_tolerance                1.
% 2.18/0.99  --trig_cnt_out_sk_spl                   false
% 2.18/0.99  --abstr_cl_out                          false
% 2.18/0.99  
% 2.18/0.99  ------ Global Options
% 2.18/0.99  
% 2.18/0.99  --schedule                              default
% 2.18/0.99  --add_important_lit                     false
% 2.18/0.99  --prop_solver_per_cl                    1000
% 2.18/0.99  --min_unsat_core                        false
% 2.18/0.99  --soft_assumptions                      false
% 2.18/0.99  --soft_lemma_size                       3
% 2.18/0.99  --prop_impl_unit_size                   0
% 2.18/0.99  --prop_impl_unit                        []
% 2.18/0.99  --share_sel_clauses                     true
% 2.18/0.99  --reset_solvers                         false
% 2.18/0.99  --bc_imp_inh                            [conj_cone]
% 2.18/0.99  --conj_cone_tolerance                   3.
% 2.18/0.99  --extra_neg_conj                        none
% 2.18/0.99  --large_theory_mode                     true
% 2.18/0.99  --prolific_symb_bound                   200
% 2.18/0.99  --lt_threshold                          2000
% 2.18/0.99  --clause_weak_htbl                      true
% 2.18/0.99  --gc_record_bc_elim                     false
% 2.18/0.99  
% 2.18/0.99  ------ Preprocessing Options
% 2.18/0.99  
% 2.18/0.99  --preprocessing_flag                    true
% 2.18/0.99  --time_out_prep_mult                    0.1
% 2.18/0.99  --splitting_mode                        input
% 2.18/0.99  --splitting_grd                         true
% 2.18/0.99  --splitting_cvd                         false
% 2.18/0.99  --splitting_cvd_svl                     false
% 2.18/0.99  --splitting_nvd                         32
% 2.18/0.99  --sub_typing                            true
% 2.18/0.99  --prep_gs_sim                           true
% 2.18/0.99  --prep_unflatten                        true
% 2.18/0.99  --prep_res_sim                          true
% 2.18/0.99  --prep_upred                            true
% 2.18/0.99  --prep_sem_filter                       exhaustive
% 2.18/0.99  --prep_sem_filter_out                   false
% 2.18/0.99  --pred_elim                             true
% 2.18/0.99  --res_sim_input                         true
% 2.18/0.99  --eq_ax_congr_red                       true
% 2.18/0.99  --pure_diseq_elim                       true
% 2.18/0.99  --brand_transform                       false
% 2.18/0.99  --non_eq_to_eq                          false
% 2.18/0.99  --prep_def_merge                        true
% 2.18/0.99  --prep_def_merge_prop_impl              false
% 2.18/0.99  --prep_def_merge_mbd                    true
% 2.18/0.99  --prep_def_merge_tr_red                 false
% 2.18/0.99  --prep_def_merge_tr_cl                  false
% 2.18/0.99  --smt_preprocessing                     true
% 2.18/0.99  --smt_ac_axioms                         fast
% 2.18/0.99  --preprocessed_out                      false
% 2.18/0.99  --preprocessed_stats                    false
% 2.18/0.99  
% 2.18/0.99  ------ Abstraction refinement Options
% 2.18/0.99  
% 2.18/0.99  --abstr_ref                             []
% 2.18/0.99  --abstr_ref_prep                        false
% 2.18/0.99  --abstr_ref_until_sat                   false
% 2.18/0.99  --abstr_ref_sig_restrict                funpre
% 2.18/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.18/0.99  --abstr_ref_under                       []
% 2.18/0.99  
% 2.18/0.99  ------ SAT Options
% 2.18/0.99  
% 2.18/0.99  --sat_mode                              false
% 2.18/0.99  --sat_fm_restart_options                ""
% 2.18/0.99  --sat_gr_def                            false
% 2.18/0.99  --sat_epr_types                         true
% 2.18/0.99  --sat_non_cyclic_types                  false
% 2.18/0.99  --sat_finite_models                     false
% 2.18/0.99  --sat_fm_lemmas                         false
% 2.18/0.99  --sat_fm_prep                           false
% 2.18/0.99  --sat_fm_uc_incr                        true
% 2.18/0.99  --sat_out_model                         small
% 2.18/0.99  --sat_out_clauses                       false
% 2.18/0.99  
% 2.18/0.99  ------ QBF Options
% 2.18/0.99  
% 2.18/0.99  --qbf_mode                              false
% 2.18/0.99  --qbf_elim_univ                         false
% 2.18/0.99  --qbf_dom_inst                          none
% 2.18/0.99  --qbf_dom_pre_inst                      false
% 2.18/0.99  --qbf_sk_in                             false
% 2.18/0.99  --qbf_pred_elim                         true
% 2.18/0.99  --qbf_split                             512
% 2.18/0.99  
% 2.18/0.99  ------ BMC1 Options
% 2.18/0.99  
% 2.18/0.99  --bmc1_incremental                      false
% 2.18/0.99  --bmc1_axioms                           reachable_all
% 2.18/0.99  --bmc1_min_bound                        0
% 2.18/0.99  --bmc1_max_bound                        -1
% 2.18/0.99  --bmc1_max_bound_default                -1
% 2.18/0.99  --bmc1_symbol_reachability              true
% 2.18/0.99  --bmc1_property_lemmas                  false
% 2.18/0.99  --bmc1_k_induction                      false
% 2.18/0.99  --bmc1_non_equiv_states                 false
% 2.18/0.99  --bmc1_deadlock                         false
% 2.18/0.99  --bmc1_ucm                              false
% 2.18/0.99  --bmc1_add_unsat_core                   none
% 2.18/0.99  --bmc1_unsat_core_children              false
% 2.18/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.18/0.99  --bmc1_out_stat                         full
% 2.18/0.99  --bmc1_ground_init                      false
% 2.18/0.99  --bmc1_pre_inst_next_state              false
% 2.18/0.99  --bmc1_pre_inst_state                   false
% 2.18/0.99  --bmc1_pre_inst_reach_state             false
% 2.18/0.99  --bmc1_out_unsat_core                   false
% 2.18/0.99  --bmc1_aig_witness_out                  false
% 2.18/0.99  --bmc1_verbose                          false
% 2.18/0.99  --bmc1_dump_clauses_tptp                false
% 2.18/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.18/0.99  --bmc1_dump_file                        -
% 2.18/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.18/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.18/0.99  --bmc1_ucm_extend_mode                  1
% 2.18/0.99  --bmc1_ucm_init_mode                    2
% 2.18/0.99  --bmc1_ucm_cone_mode                    none
% 2.18/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.18/0.99  --bmc1_ucm_relax_model                  4
% 2.18/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.18/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.18/0.99  --bmc1_ucm_layered_model                none
% 2.18/0.99  --bmc1_ucm_max_lemma_size               10
% 2.18/0.99  
% 2.18/0.99  ------ AIG Options
% 2.18/0.99  
% 2.18/0.99  --aig_mode                              false
% 2.18/0.99  
% 2.18/0.99  ------ Instantiation Options
% 2.18/0.99  
% 2.18/0.99  --instantiation_flag                    true
% 2.18/0.99  --inst_sos_flag                         false
% 2.18/0.99  --inst_sos_phase                        true
% 2.18/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.18/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.18/0.99  --inst_lit_sel_side                     none
% 2.18/0.99  --inst_solver_per_active                1400
% 2.18/0.99  --inst_solver_calls_frac                1.
% 2.18/0.99  --inst_passive_queue_type               priority_queues
% 2.18/0.99  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 2.18/0.99  --inst_passive_queues_freq              [25;2]
% 2.18/0.99  --inst_dismatching                      true
% 2.18/0.99  --inst_eager_unprocessed_to_passive     true
% 2.18/0.99  --inst_prop_sim_given                   true
% 2.18/0.99  --inst_prop_sim_new                     false
% 2.18/0.99  --inst_subs_new                         false
% 2.18/0.99  --inst_eq_res_simp                      false
% 2.18/0.99  --inst_subs_given                       false
% 2.18/0.99  --inst_orphan_elimination               true
% 2.18/0.99  --inst_learning_loop_flag               true
% 2.18/0.99  --inst_learning_start                   3000
% 2.18/0.99  --inst_learning_factor                  2
% 2.18/0.99  --inst_start_prop_sim_after_learn       3
% 2.18/0.99  --inst_sel_renew                        solver
% 2.18/0.99  --inst_lit_activity_flag                true
% 2.18/0.99  --inst_restr_to_given                   false
% 2.18/0.99  --inst_activity_threshold               500
% 2.18/0.99  --inst_out_proof                        true
% 2.18/0.99  
% 2.18/0.99  ------ Resolution Options
% 2.18/0.99  
% 2.18/0.99  --resolution_flag                       false
% 2.18/0.99  --res_lit_sel                           adaptive
% 2.18/0.99  --res_lit_sel_side                      none
% 2.18/0.99  --res_ordering                          kbo
% 2.18/0.99  --res_to_prop_solver                    active
% 2.18/0.99  --res_prop_simpl_new                    false
% 2.18/0.99  --res_prop_simpl_given                  true
% 2.18/0.99  --res_passive_queue_type                priority_queues
% 2.18/0.99  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 2.18/0.99  --res_passive_queues_freq               [15;5]
% 2.18/0.99  --res_forward_subs                      full
% 2.18/0.99  --res_backward_subs                     full
% 2.18/0.99  --res_forward_subs_resolution           true
% 2.18/0.99  --res_backward_subs_resolution          true
% 2.18/0.99  --res_orphan_elimination                true
% 2.18/0.99  --res_time_limit                        2.
% 2.18/0.99  --res_out_proof                         true
% 2.18/0.99  
% 2.18/0.99  ------ Superposition Options
% 2.18/0.99  
% 2.18/0.99  --superposition_flag                    true
% 2.18/0.99  --sup_passive_queue_type                priority_queues
% 2.18/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.18/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.18/0.99  --demod_completeness_check              fast
% 2.18/0.99  --demod_use_ground                      true
% 2.18/0.99  --sup_to_prop_solver                    passive
% 2.18/0.99  --sup_prop_simpl_new                    true
% 2.18/0.99  --sup_prop_simpl_given                  true
% 2.18/0.99  --sup_fun_splitting                     false
% 2.18/0.99  --sup_smt_interval                      50000
% 2.18/0.99  
% 2.18/0.99  ------ Superposition Simplification Setup
% 2.18/0.99  
% 2.18/0.99  --sup_indices_passive                   []
% 2.18/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.18/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/0.99  --sup_full_bw                           [BwDemod]
% 2.18/0.99  --sup_immed_triv                        [TrivRules]
% 2.18/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.18/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/0.99  --sup_immed_bw_main                     []
% 2.18/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.18/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/0.99  
% 2.18/0.99  ------ Combination Options
% 2.18/0.99  
% 2.18/0.99  --comb_res_mult                         3
% 2.18/0.99  --comb_sup_mult                         2
% 2.18/0.99  --comb_inst_mult                        10
% 2.18/0.99  
% 2.18/0.99  ------ Debug Options
% 2.18/0.99  
% 2.18/0.99  --dbg_backtrace                         false
% 2.18/0.99  --dbg_dump_prop_clauses                 false
% 2.18/0.99  --dbg_dump_prop_clauses_file            -
% 2.18/0.99  --dbg_out_stat                          false
% 2.18/0.99  
% 2.18/0.99  
% 2.18/0.99  
% 2.18/0.99  
% 2.18/0.99  ------ Proving...
% 2.18/0.99  
% 2.18/0.99  
% 2.18/0.99  % SZS status Theorem for theBenchmark.p
% 2.18/0.99  
% 2.18/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.18/0.99  
% 2.18/0.99  fof(f19,conjecture,(
% 2.18/0.99    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 2.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.99  
% 2.18/0.99  fof(f20,negated_conjecture,(
% 2.18/0.99    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 2.18/0.99    inference(negated_conjecture,[],[f19])).
% 2.18/0.99  
% 2.18/0.99  fof(f49,plain,(
% 2.18/0.99    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.18/0.99    inference(ennf_transformation,[],[f20])).
% 2.18/0.99  
% 2.18/0.99  fof(f50,plain,(
% 2.18/0.99    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.18/0.99    inference(flattening,[],[f49])).
% 2.18/0.99  
% 2.18/0.99  fof(f61,plain,(
% 2.18/0.99    ? [X0] : (? [X1] : (((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.18/0.99    inference(nnf_transformation,[],[f50])).
% 2.18/0.99  
% 2.18/0.99  fof(f62,plain,(
% 2.18/0.99    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.18/0.99    inference(flattening,[],[f61])).
% 2.18/0.99  
% 2.18/0.99  fof(f64,plain,(
% 2.18/0.99    ( ! [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_subset_1(sK3,u1_struct_0(X0)) | ~v3_tex_2(sK3,X0)) & (~v1_subset_1(sK3,u1_struct_0(X0)) | v3_tex_2(sK3,X0)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.18/0.99    introduced(choice_axiom,[])).
% 2.18/0.99  
% 2.18/0.99  fof(f63,plain,(
% 2.18/0.99    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((v1_subset_1(X1,u1_struct_0(sK2)) | ~v3_tex_2(X1,sK2)) & (~v1_subset_1(X1,u1_struct_0(sK2)) | v3_tex_2(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v1_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.18/0.99    introduced(choice_axiom,[])).
% 2.18/0.99  
% 2.18/0.99  fof(f65,plain,(
% 2.18/0.99    ((v1_subset_1(sK3,u1_struct_0(sK2)) | ~v3_tex_2(sK3,sK2)) & (~v1_subset_1(sK3,u1_struct_0(sK2)) | v3_tex_2(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v1_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.18/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f62,f64,f63])).
% 2.18/0.99  
% 2.18/0.99  fof(f98,plain,(
% 2.18/0.99    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 2.18/0.99    inference(cnf_transformation,[],[f65])).
% 2.18/0.99  
% 2.18/0.99  fof(f12,axiom,(
% 2.18/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 2.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.99  
% 2.18/0.99  fof(f36,plain,(
% 2.18/0.99    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.18/0.99    inference(ennf_transformation,[],[f12])).
% 2.18/0.99  
% 2.18/0.99  fof(f54,plain,(
% 2.18/0.99    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.18/0.99    inference(nnf_transformation,[],[f36])).
% 2.18/0.99  
% 2.18/0.99  fof(f83,plain,(
% 2.18/0.99    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.18/0.99    inference(cnf_transformation,[],[f54])).
% 2.18/0.99  
% 2.18/0.99  fof(f99,plain,(
% 2.18/0.99    ~v1_subset_1(sK3,u1_struct_0(sK2)) | v3_tex_2(sK3,sK2)),
% 2.18/0.99    inference(cnf_transformation,[],[f65])).
% 2.18/0.99  
% 2.18/0.99  fof(f4,axiom,(
% 2.18/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.99  
% 2.18/0.99  fof(f24,plain,(
% 2.18/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.18/0.99    inference(ennf_transformation,[],[f4])).
% 2.18/0.99  
% 2.18/0.99  fof(f69,plain,(
% 2.18/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.18/0.99    inference(cnf_transformation,[],[f24])).
% 2.18/0.99  
% 2.18/0.99  fof(f3,axiom,(
% 2.18/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.99  
% 2.18/0.99  fof(f23,plain,(
% 2.18/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.18/0.99    inference(ennf_transformation,[],[f3])).
% 2.18/0.99  
% 2.18/0.99  fof(f68,plain,(
% 2.18/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.18/0.99    inference(cnf_transformation,[],[f23])).
% 2.18/0.99  
% 2.18/0.99  fof(f97,plain,(
% 2.18/0.99    l1_pre_topc(sK2)),
% 2.18/0.99    inference(cnf_transformation,[],[f65])).
% 2.18/0.99  
% 2.18/0.99  fof(f14,axiom,(
% 2.18/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 2.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.99  
% 2.18/0.99  fof(f39,plain,(
% 2.18/0.99    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.18/0.99    inference(ennf_transformation,[],[f14])).
% 2.18/0.99  
% 2.18/0.99  fof(f40,plain,(
% 2.18/0.99    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.18/0.99    inference(flattening,[],[f39])).
% 2.18/0.99  
% 2.18/0.99  fof(f57,plain,(
% 2.18/0.99    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.18/0.99    inference(nnf_transformation,[],[f40])).
% 2.18/0.99  
% 2.18/0.99  fof(f58,plain,(
% 2.18/0.99    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.18/0.99    inference(rectify,[],[f57])).
% 2.18/0.99  
% 2.18/0.99  fof(f59,plain,(
% 2.18/0.99    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK1(X0),X0) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.18/0.99    introduced(choice_axiom,[])).
% 2.18/0.99  
% 2.18/0.99  fof(f60,plain,(
% 2.18/0.99    ! [X0] : (((v1_tdlat_3(X0) | (~v3_pre_topc(sK1(X0),X0) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.18/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f58,f59])).
% 2.18/0.99  
% 2.18/0.99  fof(f87,plain,(
% 2.18/0.99    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.18/0.99    inference(cnf_transformation,[],[f60])).
% 2.18/0.99  
% 2.18/0.99  fof(f17,axiom,(
% 2.18/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 2.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.99  
% 2.18/0.99  fof(f45,plain,(
% 2.18/0.99    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.18/0.99    inference(ennf_transformation,[],[f17])).
% 2.18/0.99  
% 2.18/0.99  fof(f46,plain,(
% 2.18/0.99    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.18/0.99    inference(flattening,[],[f45])).
% 2.18/0.99  
% 2.18/0.99  fof(f92,plain,(
% 2.18/0.99    ( ! [X0,X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.18/0.99    inference(cnf_transformation,[],[f46])).
% 2.18/0.99  
% 2.18/0.99  fof(f9,axiom,(
% 2.18/0.99    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 2.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.99  
% 2.18/0.99  fof(f31,plain,(
% 2.18/0.99    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 2.18/0.99    inference(ennf_transformation,[],[f9])).
% 2.18/0.99  
% 2.18/0.99  fof(f32,plain,(
% 2.18/0.99    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 2.18/0.99    inference(flattening,[],[f31])).
% 2.18/0.99  
% 2.18/0.99  fof(f77,plain,(
% 2.18/0.99    ( ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 2.18/0.99    inference(cnf_transformation,[],[f32])).
% 2.18/0.99  
% 2.18/0.99  fof(f11,axiom,(
% 2.18/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 2.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.99  
% 2.18/0.99  fof(f35,plain,(
% 2.18/0.99    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.18/0.99    inference(ennf_transformation,[],[f11])).
% 2.18/0.99  
% 2.18/0.99  fof(f53,plain,(
% 2.18/0.99    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.18/0.99    inference(nnf_transformation,[],[f35])).
% 2.18/0.99  
% 2.18/0.99  fof(f80,plain,(
% 2.18/0.99    ( ! [X0,X1] : (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.18/0.99    inference(cnf_transformation,[],[f53])).
% 2.18/0.99  
% 2.18/0.99  fof(f94,plain,(
% 2.18/0.99    ~v2_struct_0(sK2)),
% 2.18/0.99    inference(cnf_transformation,[],[f65])).
% 2.18/0.99  
% 2.18/0.99  fof(f96,plain,(
% 2.18/0.99    v1_tdlat_3(sK2)),
% 2.18/0.99    inference(cnf_transformation,[],[f65])).
% 2.18/0.99  
% 2.18/0.99  fof(f13,axiom,(
% 2.18/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 2.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.99  
% 2.18/0.99  fof(f21,plain,(
% 2.18/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2))))),
% 2.18/0.99    inference(pure_predicate_removal,[],[f13])).
% 2.18/0.99  
% 2.18/0.99  fof(f37,plain,(
% 2.18/0.99    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.18/0.99    inference(ennf_transformation,[],[f21])).
% 2.18/0.99  
% 2.18/0.99  fof(f38,plain,(
% 2.18/0.99    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.18/0.99    inference(flattening,[],[f37])).
% 2.18/0.99  
% 2.18/0.99  fof(f55,plain,(
% 2.18/0.99    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(sK0(X0,X1)) = X1 & m1_pre_topc(sK0(X0,X1),X0) & ~v2_struct_0(sK0(X0,X1))))),
% 2.18/0.99    introduced(choice_axiom,[])).
% 2.18/0.99  
% 2.18/0.99  fof(f56,plain,(
% 2.18/0.99    ! [X0] : (! [X1] : ((u1_struct_0(sK0(X0,X1)) = X1 & m1_pre_topc(sK0(X0,X1),X0) & ~v2_struct_0(sK0(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.18/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f55])).
% 2.18/0.99  
% 2.18/0.99  fof(f86,plain,(
% 2.18/0.99    ( ! [X0,X1] : (u1_struct_0(sK0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.18/0.99    inference(cnf_transformation,[],[f56])).
% 2.18/0.99  
% 2.18/0.99  fof(f16,axiom,(
% 2.18/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 2.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.99  
% 2.18/0.99  fof(f43,plain,(
% 2.18/0.99    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.18/0.99    inference(ennf_transformation,[],[f16])).
% 2.18/0.99  
% 2.18/0.99  fof(f44,plain,(
% 2.18/0.99    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.18/0.99    inference(flattening,[],[f43])).
% 2.18/0.99  
% 2.18/0.99  fof(f91,plain,(
% 2.18/0.99    ( ! [X0,X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.18/0.99    inference(cnf_transformation,[],[f44])).
% 2.18/0.99  
% 2.18/0.99  fof(f95,plain,(
% 2.18/0.99    v2_pre_topc(sK2)),
% 2.18/0.99    inference(cnf_transformation,[],[f65])).
% 2.18/0.99  
% 2.18/0.99  fof(f85,plain,(
% 2.18/0.99    ( ! [X0,X1] : (m1_pre_topc(sK0(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.18/0.99    inference(cnf_transformation,[],[f56])).
% 2.18/0.99  
% 2.18/0.99  fof(f5,axiom,(
% 2.18/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.99  
% 2.18/0.99  fof(f25,plain,(
% 2.18/0.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.18/0.99    inference(ennf_transformation,[],[f5])).
% 2.18/0.99  
% 2.18/0.99  fof(f26,plain,(
% 2.18/0.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.18/0.99    inference(flattening,[],[f25])).
% 2.18/0.99  
% 2.18/0.99  fof(f70,plain,(
% 2.18/0.99    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.18/0.99    inference(cnf_transformation,[],[f26])).
% 2.18/0.99  
% 2.18/0.99  fof(f10,axiom,(
% 2.18/0.99    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0))))),
% 2.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.99  
% 2.18/0.99  fof(f22,plain,(
% 2.18/0.99    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_borsuk_1(X1,X0))))),
% 2.18/0.99    inference(pure_predicate_removal,[],[f10])).
% 2.18/0.99  
% 2.18/0.99  fof(f33,plain,(
% 2.18/0.99    ! [X0] : (! [X1] : ((v1_tdlat_3(X1) & v1_borsuk_1(X1,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.18/0.99    inference(ennf_transformation,[],[f22])).
% 2.18/0.99  
% 2.18/0.99  fof(f34,plain,(
% 2.18/0.99    ! [X0] : (! [X1] : ((v1_tdlat_3(X1) & v1_borsuk_1(X1,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.18/0.99    inference(flattening,[],[f33])).
% 2.18/0.99  
% 2.18/0.99  fof(f78,plain,(
% 2.18/0.99    ( ! [X0,X1] : (v1_borsuk_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.18/0.99    inference(cnf_transformation,[],[f34])).
% 2.18/0.99  
% 2.18/0.99  fof(f7,axiom,(
% 2.18/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0))))))),
% 2.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.99  
% 2.18/0.99  fof(f28,plain,(
% 2.18/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.18/0.99    inference(ennf_transformation,[],[f7])).
% 2.18/0.99  
% 2.18/0.99  fof(f29,plain,(
% 2.18/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.18/0.99    inference(flattening,[],[f28])).
% 2.18/0.99  
% 2.18/0.99  fof(f51,plain,(
% 2.18/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) | ~v4_pre_topc(X2,X0)) & (v4_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.18/0.99    inference(nnf_transformation,[],[f29])).
% 2.18/0.99  
% 2.18/0.99  fof(f52,plain,(
% 2.18/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) | ~v4_pre_topc(X2,X0)) & (v4_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.18/0.99    inference(flattening,[],[f51])).
% 2.18/0.99  
% 2.18/0.99  fof(f73,plain,(
% 2.18/0.99    ( ! [X2,X0,X1] : (v4_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.18/0.99    inference(cnf_transformation,[],[f52])).
% 2.18/0.99  
% 2.18/0.99  fof(f103,plain,(
% 2.18/0.99    ( ! [X0,X1] : (v4_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.18/0.99    inference(equality_resolution,[],[f73])).
% 2.18/0.99  
% 2.18/0.99  fof(f8,axiom,(
% 2.18/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.99  
% 2.18/0.99  fof(f30,plain,(
% 2.18/0.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.18/0.99    inference(ennf_transformation,[],[f8])).
% 2.18/0.99  
% 2.18/0.99  fof(f76,plain,(
% 2.18/0.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.18/0.99    inference(cnf_transformation,[],[f30])).
% 2.18/0.99  
% 2.18/0.99  fof(f6,axiom,(
% 2.18/0.99    ! [X0] : (l1_pre_topc(X0) => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)))),
% 2.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.99  
% 2.18/0.99  fof(f27,plain,(
% 2.18/0.99    ! [X0] : (k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0))),
% 2.18/0.99    inference(ennf_transformation,[],[f6])).
% 2.18/0.99  
% 2.18/0.99  fof(f72,plain,(
% 2.18/0.99    ( ! [X0] : (k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 2.18/0.99    inference(cnf_transformation,[],[f27])).
% 2.18/0.99  
% 2.18/0.99  fof(f82,plain,(
% 2.18/0.99    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.18/0.99    inference(cnf_transformation,[],[f54])).
% 2.18/0.99  
% 2.18/0.99  fof(f104,plain,(
% 2.18/0.99    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 2.18/0.99    inference(equality_resolution,[],[f82])).
% 2.18/0.99  
% 2.18/0.99  fof(f100,plain,(
% 2.18/0.99    v1_subset_1(sK3,u1_struct_0(sK2)) | ~v3_tex_2(sK3,sK2)),
% 2.18/0.99    inference(cnf_transformation,[],[f65])).
% 2.18/0.99  
% 2.18/0.99  fof(f81,plain,(
% 2.18/0.99    ( ! [X0,X1] : (v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.18/0.99    inference(cnf_transformation,[],[f53])).
% 2.18/0.99  
% 2.18/0.99  fof(f15,axiom,(
% 2.18/0.99    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 2.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.99  
% 2.18/0.99  fof(f41,plain,(
% 2.18/0.99    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.18/0.99    inference(ennf_transformation,[],[f15])).
% 2.18/0.99  
% 2.18/0.99  fof(f42,plain,(
% 2.18/0.99    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.18/0.99    inference(flattening,[],[f41])).
% 2.18/0.99  
% 2.18/0.99  fof(f90,plain,(
% 2.18/0.99    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.18/0.99    inference(cnf_transformation,[],[f42])).
% 2.18/0.99  
% 2.18/0.99  fof(f18,axiom,(
% 2.18/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 2.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/0.99  
% 2.18/0.99  fof(f47,plain,(
% 2.18/0.99    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) | (~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.18/0.99    inference(ennf_transformation,[],[f18])).
% 2.18/0.99  
% 2.18/0.99  fof(f48,plain,(
% 2.18/0.99    ! [X0] : (! [X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.18/0.99    inference(flattening,[],[f47])).
% 2.18/0.99  
% 2.18/0.99  fof(f93,plain,(
% 2.18/0.99    ( ! [X0,X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.18/0.99    inference(cnf_transformation,[],[f48])).
% 2.18/0.99  
% 2.18/0.99  cnf(c_30,negated_conjecture,
% 2.18/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.18/0.99      inference(cnf_transformation,[],[f98]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_16,plain,
% 2.18/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.18/0.99      | v1_subset_1(X0,X1)
% 2.18/0.99      | X0 = X1 ),
% 2.18/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_29,negated_conjecture,
% 2.18/0.99      ( v3_tex_2(sK3,sK2) | ~ v1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.18/0.99      inference(cnf_transformation,[],[f99]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_266,plain,
% 2.18/0.99      ( v3_tex_2(sK3,sK2) | ~ v1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.18/0.99      inference(prop_impl,[status(thm)],[c_29]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_521,plain,
% 2.18/0.99      ( v3_tex_2(sK3,sK2)
% 2.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.18/0.99      | X1 = X0
% 2.18/0.99      | u1_struct_0(sK2) != X1
% 2.18/0.99      | sK3 != X0 ),
% 2.18/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_266]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_522,plain,
% 2.18/0.99      ( v3_tex_2(sK3,sK2)
% 2.18/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.18/0.99      | u1_struct_0(sK2) = sK3 ),
% 2.18/0.99      inference(unflattening,[status(thm)],[c_521]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_2026,plain,
% 2.18/0.99      ( v3_tex_2(sK3,sK2) | u1_struct_0(sK2) = sK3 ),
% 2.18/0.99      inference(prop_impl,[status(thm)],[c_30,c_522]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_2802,plain,
% 2.18/0.99      ( u1_struct_0(sK2) = sK3 | v3_tex_2(sK3,sK2) = iProver_top ),
% 2.18/0.99      inference(predicate_to_equality,[status(thm)],[c_2026]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_3,plain,
% 2.18/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.18/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_2,plain,
% 2.18/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.18/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_447,plain,
% 2.18/0.99      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.18/0.99      inference(resolution,[status(thm)],[c_3,c_2]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_31,negated_conjecture,
% 2.18/0.99      ( l1_pre_topc(sK2) ),
% 2.18/0.99      inference(cnf_transformation,[],[f97]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1146,plain,
% 2.18/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK2 != X0 ),
% 2.18/0.99      inference(resolution_lifted,[status(thm)],[c_447,c_31]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1147,plain,
% 2.18/0.99      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 2.18/0.99      inference(unflattening,[status(thm)],[c_1146]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_2810,plain,
% 2.18/0.99      ( k2_struct_0(sK2) = sK3 | v3_tex_2(sK3,sK2) = iProver_top ),
% 2.18/0.99      inference(demodulation,[status(thm)],[c_2802,c_1147]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_23,plain,
% 2.18/0.99      ( v3_pre_topc(X0,X1)
% 2.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/0.99      | ~ v1_tdlat_3(X1)
% 2.18/0.99      | ~ v2_pre_topc(X1)
% 2.18/0.99      | ~ l1_pre_topc(X1) ),
% 2.18/0.99      inference(cnf_transformation,[],[f87]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_26,plain,
% 2.18/0.99      ( ~ v3_tex_2(X0,X1)
% 2.18/0.99      | ~ v3_pre_topc(X0,X1)
% 2.18/0.99      | v1_tops_1(X0,X1)
% 2.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/0.99      | v2_struct_0(X1)
% 2.18/0.99      | ~ v2_pre_topc(X1)
% 2.18/0.99      | ~ l1_pre_topc(X1) ),
% 2.18/0.99      inference(cnf_transformation,[],[f92]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_627,plain,
% 2.18/0.99      ( ~ v3_tex_2(X0,X1)
% 2.18/0.99      | v1_tops_1(X0,X1)
% 2.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/0.99      | v2_struct_0(X1)
% 2.18/0.99      | ~ v1_tdlat_3(X1)
% 2.18/0.99      | ~ v2_pre_topc(X1)
% 2.18/0.99      | ~ l1_pre_topc(X1) ),
% 2.18/0.99      inference(resolution,[status(thm)],[c_23,c_26]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_11,plain,
% 2.18/0.99      ( ~ v1_tdlat_3(X0) | v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 2.18/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_645,plain,
% 2.18/0.99      ( ~ v3_tex_2(X0,X1)
% 2.18/0.99      | v1_tops_1(X0,X1)
% 2.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/0.99      | v2_struct_0(X1)
% 2.18/0.99      | ~ v1_tdlat_3(X1)
% 2.18/0.99      | ~ l1_pre_topc(X1) ),
% 2.18/0.99      inference(forward_subsumption_resolution,
% 2.18/0.99                [status(thm)],
% 2.18/0.99                [c_627,c_11]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_15,plain,
% 2.18/0.99      ( ~ v1_tops_1(X0,X1)
% 2.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/0.99      | ~ l1_pre_topc(X1)
% 2.18/0.99      | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
% 2.18/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1085,plain,
% 2.18/0.99      ( ~ v3_tex_2(X0,X1)
% 2.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/0.99      | v2_struct_0(X1)
% 2.18/0.99      | ~ v1_tdlat_3(X1)
% 2.18/0.99      | ~ l1_pre_topc(X1)
% 2.18/0.99      | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
% 2.18/0.99      inference(resolution,[status(thm)],[c_645,c_15]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1198,plain,
% 2.18/0.99      ( ~ v3_tex_2(X0,X1)
% 2.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/0.99      | v2_struct_0(X1)
% 2.18/0.99      | ~ v1_tdlat_3(X1)
% 2.18/0.99      | k2_pre_topc(X1,X0) = u1_struct_0(X1)
% 2.18/0.99      | sK2 != X1 ),
% 2.18/0.99      inference(resolution_lifted,[status(thm)],[c_1085,c_31]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1199,plain,
% 2.18/0.99      ( ~ v3_tex_2(X0,sK2)
% 2.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.18/0.99      | v2_struct_0(sK2)
% 2.18/0.99      | ~ v1_tdlat_3(sK2)
% 2.18/0.99      | k2_pre_topc(sK2,X0) = u1_struct_0(sK2) ),
% 2.18/0.99      inference(unflattening,[status(thm)],[c_1198]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_34,negated_conjecture,
% 2.18/0.99      ( ~ v2_struct_0(sK2) ),
% 2.18/0.99      inference(cnf_transformation,[],[f94]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_32,negated_conjecture,
% 2.18/0.99      ( v1_tdlat_3(sK2) ),
% 2.18/0.99      inference(cnf_transformation,[],[f96]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1203,plain,
% 2.18/0.99      ( ~ v3_tex_2(X0,sK2)
% 2.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.18/0.99      | k2_pre_topc(sK2,X0) = u1_struct_0(sK2) ),
% 2.18/0.99      inference(global_propositional_subsumption,
% 2.18/0.99                [status(thm)],
% 2.18/0.99                [c_1199,c_34,c_32]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1469,plain,
% 2.18/0.99      ( ~ v3_tex_2(X0,sK2)
% 2.18/0.99      | k2_pre_topc(sK2,X0) = u1_struct_0(sK2)
% 2.18/0.99      | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
% 2.18/0.99      | sK3 != X0 ),
% 2.18/0.99      inference(resolution_lifted,[status(thm)],[c_30,c_1203]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1470,plain,
% 2.18/0.99      ( ~ v3_tex_2(sK3,sK2) | k2_pre_topc(sK2,sK3) = u1_struct_0(sK2) ),
% 2.18/0.99      inference(unflattening,[status(thm)],[c_1469]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_2030,plain,
% 2.18/0.99      ( ~ v3_tex_2(sK3,sK2) | k2_pre_topc(sK2,sK3) = u1_struct_0(sK2) ),
% 2.18/0.99      inference(prop_impl,[status(thm)],[c_1470]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_2798,plain,
% 2.18/0.99      ( k2_pre_topc(sK2,sK3) = u1_struct_0(sK2)
% 2.18/0.99      | v3_tex_2(sK3,sK2) != iProver_top ),
% 2.18/0.99      inference(predicate_to_equality,[status(thm)],[c_2030]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_2825,plain,
% 2.18/0.99      ( k2_pre_topc(sK2,sK3) = k2_struct_0(sK2)
% 2.18/0.99      | v3_tex_2(sK3,sK2) != iProver_top ),
% 2.18/0.99      inference(light_normalisation,[status(thm)],[c_2798,c_1147]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_3050,plain,
% 2.18/0.99      ( k2_pre_topc(sK2,sK3) = k2_struct_0(sK2)
% 2.18/0.99      | k2_struct_0(sK2) = sK3 ),
% 2.18/0.99      inference(superposition,[status(thm)],[c_2810,c_2825]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_18,plain,
% 2.18/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/0.99      | v1_xboole_0(X0)
% 2.18/0.99      | v2_struct_0(X1)
% 2.18/0.99      | ~ l1_pre_topc(X1)
% 2.18/0.99      | u1_struct_0(sK0(X1,X0)) = X0 ),
% 2.18/0.99      inference(cnf_transformation,[],[f86]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1267,plain,
% 2.18/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/0.99      | v1_xboole_0(X0)
% 2.18/0.99      | v2_struct_0(X1)
% 2.18/0.99      | u1_struct_0(sK0(X1,X0)) = X0
% 2.18/0.99      | sK2 != X1 ),
% 2.18/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_31]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1268,plain,
% 2.18/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.18/0.99      | v1_xboole_0(X0)
% 2.18/0.99      | v2_struct_0(sK2)
% 2.18/0.99      | u1_struct_0(sK0(sK2,X0)) = X0 ),
% 2.18/0.99      inference(unflattening,[status(thm)],[c_1267]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1272,plain,
% 2.18/0.99      ( v1_xboole_0(X0)
% 2.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.18/0.99      | u1_struct_0(sK0(sK2,X0)) = X0 ),
% 2.18/0.99      inference(global_propositional_subsumption,
% 2.18/0.99                [status(thm)],
% 2.18/0.99                [c_1268,c_34]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1273,plain,
% 2.18/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.18/0.99      | v1_xboole_0(X0)
% 2.18/0.99      | u1_struct_0(sK0(sK2,X0)) = X0 ),
% 2.18/0.99      inference(renaming,[status(thm)],[c_1272]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_25,plain,
% 2.18/0.99      ( ~ v3_tex_2(X0,X1)
% 2.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/0.99      | ~ v1_xboole_0(X0)
% 2.18/0.99      | v2_struct_0(X1)
% 2.18/0.99      | ~ v2_pre_topc(X1)
% 2.18/0.99      | ~ l1_pre_topc(X1) ),
% 2.18/0.99      inference(cnf_transformation,[],[f91]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_33,negated_conjecture,
% 2.18/0.99      ( v2_pre_topc(sK2) ),
% 2.18/0.99      inference(cnf_transformation,[],[f95]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_925,plain,
% 2.18/0.99      ( ~ v3_tex_2(X0,X1)
% 2.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/0.99      | ~ v1_xboole_0(X0)
% 2.18/0.99      | v2_struct_0(X1)
% 2.18/0.99      | ~ l1_pre_topc(X1)
% 2.18/0.99      | sK2 != X1 ),
% 2.18/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_33]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_926,plain,
% 2.18/0.99      ( ~ v3_tex_2(X0,sK2)
% 2.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.18/0.99      | ~ v1_xboole_0(X0)
% 2.18/0.99      | v2_struct_0(sK2)
% 2.18/0.99      | ~ l1_pre_topc(sK2) ),
% 2.18/0.99      inference(unflattening,[status(thm)],[c_925]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_930,plain,
% 2.18/0.99      ( ~ v3_tex_2(X0,sK2)
% 2.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.18/0.99      | ~ v1_xboole_0(X0) ),
% 2.18/0.99      inference(global_propositional_subsumption,
% 2.18/0.99                [status(thm)],
% 2.18/0.99                [c_926,c_34,c_31]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1364,plain,
% 2.18/0.99      ( ~ v3_tex_2(X0,sK2)
% 2.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.18/0.99      | u1_struct_0(sK0(sK2,X0)) = X0 ),
% 2.18/0.99      inference(resolution,[status(thm)],[c_1273,c_930]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1459,plain,
% 2.18/0.99      ( ~ v3_tex_2(X0,sK2)
% 2.18/0.99      | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
% 2.18/0.99      | u1_struct_0(sK0(sK2,X0)) = X0
% 2.18/0.99      | sK3 != X0 ),
% 2.18/0.99      inference(resolution_lifted,[status(thm)],[c_30,c_1364]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1460,plain,
% 2.18/0.99      ( ~ v3_tex_2(sK3,sK2) | u1_struct_0(sK0(sK2,sK3)) = sK3 ),
% 2.18/0.99      inference(unflattening,[status(thm)],[c_1459]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_2799,plain,
% 2.18/0.99      ( u1_struct_0(sK0(sK2,sK3)) = sK3
% 2.18/0.99      | v3_tex_2(sK3,sK2) != iProver_top ),
% 2.18/0.99      inference(predicate_to_equality,[status(thm)],[c_1460]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_3051,plain,
% 2.18/0.99      ( u1_struct_0(sK0(sK2,sK3)) = sK3 | k2_struct_0(sK2) = sK3 ),
% 2.18/0.99      inference(superposition,[status(thm)],[c_2810,c_2799]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_19,plain,
% 2.18/0.99      ( m1_pre_topc(sK0(X0,X1),X0)
% 2.18/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.18/0.99      | v1_xboole_0(X1)
% 2.18/0.99      | v2_struct_0(X0)
% 2.18/0.99      | ~ l1_pre_topc(X0) ),
% 2.18/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1151,plain,
% 2.18/0.99      ( m1_pre_topc(sK0(X0,X1),X0)
% 2.18/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.18/0.99      | v1_xboole_0(X1)
% 2.18/0.99      | v2_struct_0(X0)
% 2.18/0.99      | sK2 != X0 ),
% 2.18/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_31]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1152,plain,
% 2.18/0.99      ( m1_pre_topc(sK0(sK2,X0),sK2)
% 2.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.18/0.99      | v1_xboole_0(X0)
% 2.18/0.99      | v2_struct_0(sK2) ),
% 2.18/0.99      inference(unflattening,[status(thm)],[c_1151]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1156,plain,
% 2.18/0.99      ( v1_xboole_0(X0)
% 2.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.18/0.99      | m1_pre_topc(sK0(sK2,X0),sK2) ),
% 2.18/0.99      inference(global_propositional_subsumption,
% 2.18/0.99                [status(thm)],
% 2.18/0.99                [c_1152,c_34]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1157,plain,
% 2.18/0.99      ( m1_pre_topc(sK0(sK2,X0),sK2)
% 2.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.18/0.99      | v1_xboole_0(X0) ),
% 2.18/0.99      inference(renaming,[status(thm)],[c_1156]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1378,plain,
% 2.18/0.99      ( ~ v3_tex_2(X0,sK2)
% 2.18/0.99      | m1_pre_topc(sK0(sK2,X0),sK2)
% 2.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.18/0.99      inference(resolution,[status(thm)],[c_1157,c_930]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1449,plain,
% 2.18/0.99      ( ~ v3_tex_2(X0,sK2)
% 2.18/0.99      | m1_pre_topc(sK0(sK2,X0),sK2)
% 2.18/0.99      | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
% 2.18/0.99      | sK3 != X0 ),
% 2.18/0.99      inference(resolution_lifted,[status(thm)],[c_30,c_1378]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1450,plain,
% 2.18/0.99      ( ~ v3_tex_2(sK3,sK2) | m1_pre_topc(sK0(sK2,sK3),sK2) ),
% 2.18/0.99      inference(unflattening,[status(thm)],[c_1449]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_2800,plain,
% 2.18/0.99      ( v3_tex_2(sK3,sK2) != iProver_top
% 2.18/0.99      | m1_pre_topc(sK0(sK2,sK3),sK2) = iProver_top ),
% 2.18/0.99      inference(predicate_to_equality,[status(thm)],[c_1450]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_5,plain,
% 2.18/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/0.99      | ~ v4_pre_topc(X0,X1)
% 2.18/0.99      | ~ l1_pre_topc(X1)
% 2.18/0.99      | k2_pre_topc(X1,X0) = X0 ),
% 2.18/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_13,plain,
% 2.18/0.99      ( v1_borsuk_1(X0,X1)
% 2.18/0.99      | ~ m1_pre_topc(X0,X1)
% 2.18/0.99      | v2_struct_0(X1)
% 2.18/0.99      | ~ v1_tdlat_3(X1)
% 2.18/0.99      | ~ v2_pre_topc(X1)
% 2.18/0.99      | ~ l1_pre_topc(X1) ),
% 2.18/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_9,plain,
% 2.18/0.99      ( ~ v1_borsuk_1(X0,X1)
% 2.18/0.99      | ~ m1_pre_topc(X0,X1)
% 2.18/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/0.99      | v4_pre_topc(u1_struct_0(X0),X1)
% 2.18/0.99      | ~ v2_pre_topc(X1)
% 2.18/0.99      | ~ l1_pre_topc(X1) ),
% 2.18/0.99      inference(cnf_transformation,[],[f103]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_10,plain,
% 2.18/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.18/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/0.99      | ~ l1_pre_topc(X1) ),
% 2.18/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_208,plain,
% 2.18/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.18/0.99      | ~ v1_borsuk_1(X0,X1)
% 2.18/0.99      | v4_pre_topc(u1_struct_0(X0),X1)
% 2.18/0.99      | ~ v2_pre_topc(X1)
% 2.18/0.99      | ~ l1_pre_topc(X1) ),
% 2.18/0.99      inference(global_propositional_subsumption,
% 2.18/0.99                [status(thm)],
% 2.18/0.99                [c_9,c_10]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_209,plain,
% 2.18/0.99      ( ~ v1_borsuk_1(X0,X1)
% 2.18/0.99      | ~ m1_pre_topc(X0,X1)
% 2.18/0.99      | v4_pre_topc(u1_struct_0(X0),X1)
% 2.18/0.99      | ~ v2_pre_topc(X1)
% 2.18/0.99      | ~ l1_pre_topc(X1) ),
% 2.18/0.99      inference(renaming,[status(thm)],[c_208]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_562,plain,
% 2.18/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.18/0.99      | v4_pre_topc(u1_struct_0(X0),X1)
% 2.18/0.99      | v2_struct_0(X1)
% 2.18/0.99      | ~ v1_tdlat_3(X1)
% 2.18/0.99      | ~ v2_pre_topc(X1)
% 2.18/0.99      | ~ l1_pre_topc(X1) ),
% 2.18/0.99      inference(resolution,[status(thm)],[c_13,c_209]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_578,plain,
% 2.18/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.18/0.99      | v4_pre_topc(u1_struct_0(X0),X1)
% 2.18/0.99      | v2_struct_0(X1)
% 2.18/0.99      | ~ v1_tdlat_3(X1)
% 2.18/0.99      | ~ l1_pre_topc(X1) ),
% 2.18/0.99      inference(forward_subsumption_resolution,
% 2.18/0.99                [status(thm)],
% 2.18/0.99                [c_562,c_11]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_594,plain,
% 2.18/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.18/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.18/0.99      | v2_struct_0(X1)
% 2.18/0.99      | ~ v1_tdlat_3(X1)
% 2.18/0.99      | ~ l1_pre_topc(X3)
% 2.18/0.99      | ~ l1_pre_topc(X1)
% 2.18/0.99      | X1 != X3
% 2.18/0.99      | k2_pre_topc(X3,X2) = X2
% 2.18/0.99      | u1_struct_0(X0) != X2 ),
% 2.18/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_578]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_595,plain,
% 2.18/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.18/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/0.99      | v2_struct_0(X1)
% 2.18/0.99      | ~ v1_tdlat_3(X1)
% 2.18/0.99      | ~ l1_pre_topc(X1)
% 2.18/0.99      | k2_pre_topc(X1,u1_struct_0(X0)) = u1_struct_0(X0) ),
% 2.18/0.99      inference(unflattening,[status(thm)],[c_594]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_599,plain,
% 2.18/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.18/0.99      | v2_struct_0(X1)
% 2.18/0.99      | ~ v1_tdlat_3(X1)
% 2.18/0.99      | ~ l1_pre_topc(X1)
% 2.18/0.99      | k2_pre_topc(X1,u1_struct_0(X0)) = u1_struct_0(X0) ),
% 2.18/0.99      inference(global_propositional_subsumption,
% 2.18/0.99                [status(thm)],
% 2.18/0.99                [c_595,c_10]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1228,plain,
% 2.18/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.18/0.99      | v2_struct_0(X1)
% 2.18/0.99      | ~ v1_tdlat_3(X1)
% 2.18/0.99      | k2_pre_topc(X1,u1_struct_0(X0)) = u1_struct_0(X0)
% 2.18/0.99      | sK2 != X1 ),
% 2.18/0.99      inference(resolution_lifted,[status(thm)],[c_599,c_31]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1229,plain,
% 2.18/0.99      ( ~ m1_pre_topc(X0,sK2)
% 2.18/0.99      | v2_struct_0(sK2)
% 2.18/0.99      | ~ v1_tdlat_3(sK2)
% 2.18/0.99      | k2_pre_topc(sK2,u1_struct_0(X0)) = u1_struct_0(X0) ),
% 2.18/0.99      inference(unflattening,[status(thm)],[c_1228]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1233,plain,
% 2.18/0.99      ( ~ m1_pre_topc(X0,sK2)
% 2.18/0.99      | k2_pre_topc(sK2,u1_struct_0(X0)) = u1_struct_0(X0) ),
% 2.18/0.99      inference(global_propositional_subsumption,
% 2.18/0.99                [status(thm)],
% 2.18/0.99                [c_1229,c_34,c_32]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_2801,plain,
% 2.18/0.99      ( k2_pre_topc(sK2,u1_struct_0(X0)) = u1_struct_0(X0)
% 2.18/0.99      | m1_pre_topc(X0,sK2) != iProver_top ),
% 2.18/0.99      inference(predicate_to_equality,[status(thm)],[c_1233]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_2977,plain,
% 2.18/0.99      ( k2_pre_topc(sK2,u1_struct_0(sK0(sK2,sK3))) = u1_struct_0(sK0(sK2,sK3))
% 2.18/0.99      | v3_tex_2(sK3,sK2) != iProver_top ),
% 2.18/0.99      inference(superposition,[status(thm)],[c_2800,c_2801]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_3241,plain,
% 2.18/0.99      ( k2_pre_topc(sK2,u1_struct_0(sK0(sK2,sK3))) = u1_struct_0(sK0(sK2,sK3))
% 2.18/0.99      | k2_struct_0(sK2) = sK3 ),
% 2.18/0.99      inference(superposition,[status(thm)],[c_2810,c_2977]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_3378,plain,
% 2.18/0.99      ( u1_struct_0(sK0(sK2,sK3)) = k2_pre_topc(sK2,sK3)
% 2.18/0.99      | k2_struct_0(sK2) = sK3 ),
% 2.18/0.99      inference(superposition,[status(thm)],[c_3051,c_3241]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_3498,plain,
% 2.18/0.99      ( k2_pre_topc(sK2,sK3) = sK3 | k2_struct_0(sK2) = sK3 ),
% 2.18/0.99      inference(superposition,[status(thm)],[c_3378,c_3051]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_3540,plain,
% 2.18/0.99      ( k2_struct_0(sK2) = sK3 ),
% 2.18/0.99      inference(superposition,[status(thm)],[c_3050,c_3498]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_6,plain,
% 2.18/0.99      ( ~ l1_pre_topc(X0)
% 2.18/0.99      | k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) ),
% 2.18/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1172,plain,
% 2.18/0.99      ( k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) | sK2 != X0 ),
% 2.18/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_31]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1173,plain,
% 2.18/0.99      ( k2_pre_topc(sK2,k2_struct_0(sK2)) = k2_struct_0(sK2) ),
% 2.18/0.99      inference(unflattening,[status(thm)],[c_1172]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_3689,plain,
% 2.18/0.99      ( k2_pre_topc(sK2,sK3) = sK3 ),
% 2.18/0.99      inference(demodulation,[status(thm)],[c_3540,c_1173]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_2468,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_2901,plain,
% 2.18/0.99      ( k2_pre_topc(sK2,sK3) != X0
% 2.18/0.99      | k2_pre_topc(sK2,sK3) = u1_struct_0(sK2)
% 2.18/0.99      | u1_struct_0(sK2) != X0 ),
% 2.18/0.99      inference(instantiation,[status(thm)],[c_2468]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_2914,plain,
% 2.18/0.99      ( k2_pre_topc(sK2,sK3) = u1_struct_0(sK2)
% 2.18/0.99      | k2_pre_topc(sK2,sK3) != sK3
% 2.18/0.99      | u1_struct_0(sK2) != sK3 ),
% 2.18/0.99      inference(instantiation,[status(thm)],[c_2901]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_17,plain,
% 2.18/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X0)) | ~ v1_subset_1(X0,X0) ),
% 2.18/0.99      inference(cnf_transformation,[],[f104]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_28,negated_conjecture,
% 2.18/0.99      ( ~ v3_tex_2(sK3,sK2) | v1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.18/0.99      inference(cnf_transformation,[],[f100]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_268,plain,
% 2.18/0.99      ( ~ v3_tex_2(sK3,sK2) | v1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.18/0.99      inference(prop_impl,[status(thm)],[c_28]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_535,plain,
% 2.18/0.99      ( ~ v3_tex_2(sK3,sK2)
% 2.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X0))
% 2.18/0.99      | u1_struct_0(sK2) != X0
% 2.18/0.99      | sK3 != X0 ),
% 2.18/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_268]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_536,plain,
% 2.18/0.99      ( ~ v3_tex_2(sK3,sK2)
% 2.18/0.99      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.18/0.99      | sK3 != u1_struct_0(sK2) ),
% 2.18/0.99      inference(unflattening,[status(thm)],[c_535]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1436,plain,
% 2.18/0.99      ( ~ v3_tex_2(sK3,sK2)
% 2.18/0.99      | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
% 2.18/0.99      | u1_struct_0(sK2) != sK3 ),
% 2.18/0.99      inference(resolution_lifted,[status(thm)],[c_30,c_536]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1999,plain,
% 2.18/0.99      ( ~ v3_tex_2(sK3,sK2) | u1_struct_0(sK2) != sK3 ),
% 2.18/0.99      inference(equality_resolution_simp,[status(thm)],[c_1436]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_2024,plain,
% 2.18/0.99      ( ~ v3_tex_2(sK3,sK2) | u1_struct_0(sK2) != sK3 ),
% 2.18/0.99      inference(prop_impl,[status(thm)],[c_1999]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_2792,plain,
% 2.18/0.99      ( u1_struct_0(sK2) != sK3 | v3_tex_2(sK3,sK2) != iProver_top ),
% 2.18/0.99      inference(predicate_to_equality,[status(thm)],[c_2024]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_2815,plain,
% 2.18/0.99      ( k2_struct_0(sK2) != sK3 | v3_tex_2(sK3,sK2) != iProver_top ),
% 2.18/0.99      inference(light_normalisation,[status(thm)],[c_2792,c_1147]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_14,plain,
% 2.18/0.99      ( v1_tops_1(X0,X1)
% 2.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/0.99      | ~ l1_pre_topc(X1)
% 2.18/0.99      | k2_pre_topc(X1,X0) != u1_struct_0(X1) ),
% 2.18/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_24,plain,
% 2.18/0.99      ( v2_tex_2(X0,X1)
% 2.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/0.99      | v2_struct_0(X1)
% 2.18/0.99      | ~ v1_tdlat_3(X1)
% 2.18/0.99      | ~ v2_pre_topc(X1)
% 2.18/0.99      | ~ l1_pre_topc(X1) ),
% 2.18/0.99      inference(cnf_transformation,[],[f90]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_27,plain,
% 2.18/0.99      ( v3_tex_2(X0,X1)
% 2.18/0.99      | ~ v2_tex_2(X0,X1)
% 2.18/0.99      | ~ v1_tops_1(X0,X1)
% 2.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/0.99      | v2_struct_0(X1)
% 2.18/0.99      | ~ v2_pre_topc(X1)
% 2.18/0.99      | ~ l1_pre_topc(X1) ),
% 2.18/0.99      inference(cnf_transformation,[],[f93]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_461,plain,
% 2.18/0.99      ( v3_tex_2(X0,X1)
% 2.18/0.99      | ~ v1_tops_1(X0,X1)
% 2.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/0.99      | v2_struct_0(X1)
% 2.18/0.99      | ~ v1_tdlat_3(X1)
% 2.18/0.99      | ~ v2_pre_topc(X1)
% 2.18/0.99      | ~ l1_pre_topc(X1) ),
% 2.18/0.99      inference(resolution,[status(thm)],[c_24,c_27]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_479,plain,
% 2.18/0.99      ( v3_tex_2(X0,X1)
% 2.18/0.99      | ~ v1_tops_1(X0,X1)
% 2.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/0.99      | v2_struct_0(X1)
% 2.18/0.99      | ~ v1_tdlat_3(X1)
% 2.18/0.99      | ~ l1_pre_topc(X1) ),
% 2.18/0.99      inference(forward_subsumption_resolution,
% 2.18/0.99                [status(thm)],
% 2.18/0.99                [c_461,c_11]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1108,plain,
% 2.18/0.99      ( v3_tex_2(X0,X1)
% 2.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/0.99      | v2_struct_0(X1)
% 2.18/0.99      | ~ v1_tdlat_3(X1)
% 2.18/0.99      | ~ l1_pre_topc(X1)
% 2.18/0.99      | k2_pre_topc(X1,X0) != u1_struct_0(X1) ),
% 2.18/0.99      inference(resolution,[status(thm)],[c_14,c_479]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1177,plain,
% 2.18/0.99      ( v3_tex_2(X0,X1)
% 2.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/0.99      | v2_struct_0(X1)
% 2.18/0.99      | ~ v1_tdlat_3(X1)
% 2.18/0.99      | k2_pre_topc(X1,X0) != u1_struct_0(X1)
% 2.18/0.99      | sK2 != X1 ),
% 2.18/0.99      inference(resolution_lifted,[status(thm)],[c_1108,c_31]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1178,plain,
% 2.18/0.99      ( v3_tex_2(X0,sK2)
% 2.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.18/0.99      | v2_struct_0(sK2)
% 2.18/0.99      | ~ v1_tdlat_3(sK2)
% 2.18/0.99      | k2_pre_topc(sK2,X0) != u1_struct_0(sK2) ),
% 2.18/0.99      inference(unflattening,[status(thm)],[c_1177]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1182,plain,
% 2.18/0.99      ( v3_tex_2(X0,sK2)
% 2.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.18/0.99      | k2_pre_topc(sK2,X0) != u1_struct_0(sK2) ),
% 2.18/0.99      inference(global_propositional_subsumption,
% 2.18/0.99                [status(thm)],
% 2.18/0.99                [c_1178,c_34,c_32]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1479,plain,
% 2.18/0.99      ( v3_tex_2(X0,sK2)
% 2.18/0.99      | k2_pre_topc(sK2,X0) != u1_struct_0(sK2)
% 2.18/0.99      | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
% 2.18/0.99      | sK3 != X0 ),
% 2.18/0.99      inference(resolution_lifted,[status(thm)],[c_30,c_1182]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1480,plain,
% 2.18/0.99      ( v3_tex_2(sK3,sK2) | k2_pre_topc(sK2,sK3) != u1_struct_0(sK2) ),
% 2.18/0.99      inference(unflattening,[status(thm)],[c_1479]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_1481,plain,
% 2.18/0.99      ( k2_pre_topc(sK2,sK3) != u1_struct_0(sK2)
% 2.18/0.99      | v3_tex_2(sK3,sK2) = iProver_top ),
% 2.18/0.99      inference(predicate_to_equality,[status(thm)],[c_1480]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_523,plain,
% 2.18/0.99      ( u1_struct_0(sK2) = sK3
% 2.18/0.99      | v3_tex_2(sK3,sK2) = iProver_top
% 2.18/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.18/0.99      inference(predicate_to_equality,[status(thm)],[c_522]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(c_39,plain,
% 2.18/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.18/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.18/0.99  
% 2.18/0.99  cnf(contradiction,plain,
% 2.18/0.99      ( $false ),
% 2.18/0.99      inference(minisat,
% 2.18/0.99                [status(thm)],
% 2.18/0.99                [c_3689,c_3540,c_2914,c_2815,c_1481,c_523,c_39]) ).
% 2.18/0.99  
% 2.18/0.99  
% 2.18/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.18/0.99  
% 2.18/0.99  ------                               Statistics
% 2.18/0.99  
% 2.18/0.99  ------ General
% 2.18/0.99  
% 2.18/0.99  abstr_ref_over_cycles:                  0
% 2.18/0.99  abstr_ref_under_cycles:                 0
% 2.18/0.99  gc_basic_clause_elim:                   0
% 2.18/0.99  forced_gc_time:                         0
% 2.18/0.99  parsing_time:                           0.01
% 2.18/0.99  unif_index_cands_time:                  0.
% 2.18/0.99  unif_index_add_time:                    0.
% 2.18/0.99  orderings_time:                         0.
% 2.18/0.99  out_proof_time:                         0.014
% 2.18/0.99  total_time:                             0.122
% 2.18/0.99  num_of_symbols:                         55
% 2.18/0.99  num_of_terms:                           1285
% 2.18/0.99  
% 2.18/0.99  ------ Preprocessing
% 2.18/0.99  
% 2.18/0.99  num_of_splits:                          0
% 2.18/0.99  num_of_split_atoms:                     0
% 2.18/0.99  num_of_reused_defs:                     0
% 2.18/0.99  num_eq_ax_congr_red:                    17
% 2.18/0.99  num_of_sem_filtered_clauses:            1
% 2.18/0.99  num_of_subtypes:                        0
% 2.18/0.99  monotx_restored_types:                  0
% 2.18/0.99  sat_num_of_epr_types:                   0
% 2.18/0.99  sat_num_of_non_cyclic_types:            0
% 2.18/0.99  sat_guarded_non_collapsed_types:        0
% 2.18/0.99  num_pure_diseq_elim:                    0
% 2.18/0.99  simp_replaced_by:                       0
% 2.18/0.99  res_preprocessed:                       98
% 2.18/0.99  prep_upred:                             0
% 2.18/0.99  prep_unflattend:                        55
% 2.18/0.99  smt_new_axioms:                         0
% 2.18/0.99  pred_elim_cands:                        2
% 2.18/0.99  pred_elim:                              13
% 2.18/0.99  pred_elim_cl:                           19
% 2.18/0.99  pred_elim_cycles:                       20
% 2.18/0.99  merged_defs:                            14
% 2.18/0.99  merged_defs_ncl:                        0
% 2.18/0.99  bin_hyper_res:                          14
% 2.18/0.99  prep_cycles:                            4
% 2.18/0.99  pred_elim_time:                         0.032
% 2.18/0.99  splitting_time:                         0.
% 2.18/0.99  sem_filter_time:                        0.
% 2.18/0.99  monotx_time:                            0.
% 2.18/0.99  subtype_inf_time:                       0.
% 2.18/0.99  
% 2.18/0.99  ------ Problem properties
% 2.18/0.99  
% 2.18/0.99  clauses:                                15
% 2.18/0.99  conjectures:                            0
% 2.18/0.99  epr:                                    0
% 2.18/0.99  horn:                                   14
% 2.18/0.99  ground:                                 9
% 2.18/0.99  unary:                                  3
% 2.18/0.99  binary:                                 8
% 2.18/0.99  lits:                                   31
% 2.18/0.99  lits_eq:                                13
% 2.18/0.99  fd_pure:                                0
% 2.18/0.99  fd_pseudo:                              0
% 2.18/0.99  fd_cond:                                0
% 2.18/0.99  fd_pseudo_cond:                         0
% 2.18/0.99  ac_symbols:                             0
% 2.18/0.99  
% 2.18/0.99  ------ Propositional Solver
% 2.18/0.99  
% 2.18/0.99  prop_solver_calls:                      28
% 2.18/0.99  prop_fast_solver_calls:                 1060
% 2.18/0.99  smt_solver_calls:                       0
% 2.18/0.99  smt_fast_solver_calls:                  0
% 2.18/0.99  prop_num_of_clauses:                    734
% 2.18/0.99  prop_preprocess_simplified:             3124
% 2.18/0.99  prop_fo_subsumed:                       52
% 2.18/0.99  prop_solver_time:                       0.
% 2.18/0.99  smt_solver_time:                        0.
% 2.18/0.99  smt_fast_solver_time:                   0.
% 2.18/0.99  prop_fast_solver_time:                  0.
% 2.18/0.99  prop_unsat_core_time:                   0.
% 2.18/0.99  
% 2.18/0.99  ------ QBF
% 2.18/0.99  
% 2.18/0.99  qbf_q_res:                              0
% 2.18/0.99  qbf_num_tautologies:                    0
% 2.18/0.99  qbf_prep_cycles:                        0
% 2.18/0.99  
% 2.18/0.99  ------ BMC1
% 2.18/0.99  
% 2.18/0.99  bmc1_current_bound:                     -1
% 2.18/0.99  bmc1_last_solved_bound:                 -1
% 2.18/0.99  bmc1_unsat_core_size:                   -1
% 2.18/0.99  bmc1_unsat_core_parents_size:           -1
% 2.18/0.99  bmc1_merge_next_fun:                    0
% 2.18/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.18/0.99  
% 2.18/0.99  ------ Instantiation
% 2.18/0.99  
% 2.18/0.99  inst_num_of_clauses:                    184
% 2.18/0.99  inst_num_in_passive:                    64
% 2.18/0.99  inst_num_in_active:                     114
% 2.18/0.99  inst_num_in_unprocessed:                6
% 2.18/0.99  inst_num_of_loops:                      150
% 2.18/1.00  inst_num_of_learning_restarts:          0
% 2.18/1.00  inst_num_moves_active_passive:          31
% 2.18/1.00  inst_lit_activity:                      0
% 2.18/1.00  inst_lit_activity_moves:                0
% 2.18/1.00  inst_num_tautologies:                   0
% 2.18/1.00  inst_num_prop_implied:                  0
% 2.18/1.00  inst_num_existing_simplified:           0
% 2.18/1.00  inst_num_eq_res_simplified:             0
% 2.18/1.00  inst_num_child_elim:                    0
% 2.18/1.00  inst_num_of_dismatching_blockings:      28
% 2.18/1.00  inst_num_of_non_proper_insts:           175
% 2.18/1.00  inst_num_of_duplicates:                 0
% 2.18/1.00  inst_inst_num_from_inst_to_res:         0
% 2.18/1.00  inst_dismatching_checking_time:         0.
% 2.18/1.00  
% 2.18/1.00  ------ Resolution
% 2.18/1.00  
% 2.18/1.00  res_num_of_clauses:                     0
% 2.18/1.00  res_num_in_passive:                     0
% 2.18/1.00  res_num_in_active:                      0
% 2.18/1.00  res_num_of_loops:                       102
% 2.18/1.00  res_forward_subset_subsumed:            48
% 2.18/1.00  res_backward_subset_subsumed:           0
% 2.18/1.00  res_forward_subsumed:                   3
% 2.18/1.00  res_backward_subsumed:                  0
% 2.18/1.00  res_forward_subsumption_resolution:     4
% 2.18/1.00  res_backward_subsumption_resolution:    0
% 2.18/1.00  res_clause_to_clause_subsumption:       124
% 2.18/1.00  res_orphan_elimination:                 0
% 2.18/1.00  res_tautology_del:                      68
% 2.18/1.00  res_num_eq_res_simplified:              1
% 2.18/1.00  res_num_sel_changes:                    0
% 2.18/1.00  res_moves_from_active_to_pass:          0
% 2.18/1.00  
% 2.18/1.00  ------ Superposition
% 2.18/1.00  
% 2.18/1.00  sup_time_total:                         0.
% 2.18/1.00  sup_time_generating:                    0.
% 2.18/1.00  sup_time_sim_full:                      0.
% 2.18/1.00  sup_time_sim_immed:                     0.
% 2.18/1.00  
% 2.18/1.00  sup_num_of_clauses:                     22
% 2.18/1.00  sup_num_in_active:                      13
% 2.18/1.00  sup_num_in_passive:                     9
% 2.18/1.00  sup_num_of_loops:                       28
% 2.18/1.00  sup_fw_superposition:                   17
% 2.18/1.00  sup_bw_superposition:                   20
% 2.18/1.00  sup_immediate_simplified:               13
% 2.18/1.00  sup_given_eliminated:                   1
% 2.18/1.00  comparisons_done:                       0
% 2.18/1.00  comparisons_avoided:                    9
% 2.18/1.00  
% 2.18/1.00  ------ Simplifications
% 2.18/1.00  
% 2.18/1.00  
% 2.18/1.00  sim_fw_subset_subsumed:                 7
% 2.18/1.00  sim_bw_subset_subsumed:                 3
% 2.18/1.00  sim_fw_subsumed:                        1
% 2.18/1.00  sim_bw_subsumed:                        1
% 2.18/1.00  sim_fw_subsumption_res:                 0
% 2.18/1.00  sim_bw_subsumption_res:                 0
% 2.18/1.00  sim_tautology_del:                      4
% 2.18/1.00  sim_eq_tautology_del:                   2
% 2.18/1.00  sim_eq_res_simp:                        3
% 2.18/1.00  sim_fw_demodulated:                     2
% 2.18/1.00  sim_bw_demodulated:                     12
% 2.18/1.00  sim_light_normalised:                   12
% 2.18/1.00  sim_joinable_taut:                      0
% 2.18/1.00  sim_joinable_simp:                      0
% 2.18/1.00  sim_ac_normalised:                      0
% 2.18/1.00  sim_smt_subsumption:                    0
% 2.18/1.00  
%------------------------------------------------------------------------------
