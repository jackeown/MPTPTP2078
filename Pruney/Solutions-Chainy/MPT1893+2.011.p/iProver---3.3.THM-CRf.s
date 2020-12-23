%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:39 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 900 expanded)
%              Number of clauses        :   77 ( 231 expanded)
%              Number of leaves         :   17 ( 238 expanded)
%              Depth                    :   20
%              Number of atoms          :  485 (6185 expanded)
%              Number of equality atoms :   94 ( 219 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( v1_subset_1(X1,u1_struct_0(X0))
              & v3_tex_2(X1,X0)
              & ( v4_pre_topc(X1,X0)
                | v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ~ ( v1_subset_1(X1,u1_struct_0(X0))
                & v3_tex_2(X1,X0)
                & ( v4_pre_topc(X1,X0)
                  | v3_pre_topc(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v3_tex_2(X1,X0)
          & ( v4_pre_topc(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v3_tex_2(X1,X0)
          & ( v4_pre_topc(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v3_tex_2(X1,X0)
          & ( v4_pre_topc(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v1_subset_1(sK2,u1_struct_0(X0))
        & v3_tex_2(sK2,X0)
        & ( v4_pre_topc(sK2,X0)
          | v3_pre_topc(sK2,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_subset_1(X1,u1_struct_0(X0))
            & v3_tex_2(X1,X0)
            & ( v4_pre_topc(X1,X0)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(sK1))
          & v3_tex_2(X1,sK1)
          & ( v4_pre_topc(X1,sK1)
            | v3_pre_topc(X1,sK1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v3_tdlat_3(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( v1_subset_1(sK2,u1_struct_0(sK1))
    & v3_tex_2(sK2,sK1)
    & ( v4_pre_topc(sK2,sK1)
      | v3_pre_topc(sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v3_tdlat_3(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f33,f41,f40])).

fof(f67,plain,
    ( v4_pre_topc(sK2,sK1)
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f65,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f66,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f36,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK0(X0),X0)
        & v4_pre_topc(sK0(X0),X0)
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK0(X0),X0)
            & v4_pre_topc(sK0(X0),X0)
            & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f57,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f63,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f64,plain,(
    v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
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

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f54,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f14,axiom,(
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

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f68,plain,(
    v3_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f62,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X0))
        & v1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f69,plain,(
    v1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_21,negated_conjecture,
    ( v3_pre_topc(sK2,sK1)
    | v4_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_9,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_452,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_23])).

cnf(c_453,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),X0),sK1)
    | v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_452])).

cnf(c_512,plain,
    ( v4_pre_topc(X0,sK1)
    | v4_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_subset_1(u1_struct_0(sK1),X0) != sK2
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_453])).

cnf(c_575,plain,
    ( v4_pre_topc(X0,sK1)
    | v4_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_subset_1(u1_struct_0(sK1),X0) != sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_512])).

cnf(c_834,plain,
    ( k3_subset_1(u1_struct_0(sK1),X0) != sK2
    | v4_pre_topc(X0,sK1) = iProver_top
    | v4_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_575])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_31,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_17,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_387,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_388,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_387])).

cnf(c_24,negated_conjecture,
    ( v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_392,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_388,c_24,c_23])).

cnf(c_533,plain,
    ( ~ v4_pre_topc(X0,sK1)
    | v4_pre_topc(X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_subset_1(u1_struct_0(sK1),X1) != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_392,c_453])).

cnf(c_534,plain,
    ( v4_pre_topc(X0,sK1)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK1),X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_533])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_546,plain,
    ( v4_pre_topc(X0,sK1)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK1),X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_534,c_3])).

cnf(c_924,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    | v4_pre_topc(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_546])).

cnf(c_925,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) != iProver_top
    | v4_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_924])).

cnf(c_944,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_945,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_944])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_960,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1143,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    | v4_pre_topc(sK2,sK1)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_575])).

cnf(c_1144,plain,
    ( k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK2)) != sK2
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) = iProver_top
    | v4_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1143])).

cnf(c_1174,plain,
    ( v4_pre_topc(sK2,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_834,c_22,c_31,c_925,c_945,c_960,c_1144])).

cnf(c_839,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_8,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_467,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_23])).

cnf(c_468,plain,
    ( ~ v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_467])).

cnf(c_836,plain,
    ( k2_pre_topc(sK1,X0) = X0
    | v4_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_468])).

cnf(c_1054,plain,
    ( k2_pre_topc(sK1,sK2) = sK2
    | v4_pre_topc(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_839,c_836])).

cnf(c_12,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_18,plain,
    ( ~ v3_tex_2(X0,X1)
    | v1_tops_1(X0,X1)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_20,negated_conjecture,
    ( v3_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_346,plain,
    ( v1_tops_1(X0,X1)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_20])).

cnf(c_347,plain,
    ( v1_tops_1(sK2,sK1)
    | ~ v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_346])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_349,plain,
    ( v1_tops_1(sK2,sK1)
    | ~ v3_pre_topc(sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_347,c_26,c_25,c_23,c_22])).

cnf(c_364,plain,
    ( ~ v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1)
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_349])).

cnf(c_365,plain,
    ( ~ v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_367,plain,
    ( ~ v3_pre_topc(sK2,sK1)
    | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_365,c_23,c_22])).

cnf(c_504,plain,
    ( ~ v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1)
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_367,c_392])).

cnf(c_505,plain,
    ( ~ v4_pre_topc(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_504])).

cnf(c_494,plain,
    ( v4_pre_topc(sK2,sK1)
    | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_21,c_367])).

cnf(c_507,plain,
    ( k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_505,c_22,c_494])).

cnf(c_1055,plain,
    ( u1_struct_0(sK1) = sK2
    | v4_pre_topc(sK2,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1054,c_507])).

cnf(c_1179,plain,
    ( u1_struct_0(sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_1174,c_1055])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_843,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1316,plain,
    ( k3_subset_1(u1_struct_0(sK1),sK2) = k4_xboole_0(u1_struct_0(sK1),sK2) ),
    inference(superposition,[status(thm)],[c_839,c_843])).

cnf(c_1564,plain,
    ( k3_subset_1(sK2,sK2) = k4_xboole_0(sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_1179,c_1316])).

cnf(c_5,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_840,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_841,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1268,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_840,c_841])).

cnf(c_1315,plain,
    ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_840,c_843])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1320,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1315,c_1])).

cnf(c_1911,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1268,c_1320])).

cnf(c_2014,plain,
    ( k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1564,c_1911])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_13,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(k3_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_6,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_148,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X0,X1)
    | ~ v1_xboole_0(k3_subset_1(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_6])).

cnf(c_149,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(k3_subset_1(X1,X0)) ),
    inference(renaming,[status(thm)],[c_148])).

cnf(c_303,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_149])).

cnf(c_19,negated_conjecture,
    ( v1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_324,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) != k1_xboole_0
    | u1_struct_0(sK1) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_303,c_19])).

cnf(c_325,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_subset_1(u1_struct_0(sK1),sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_324])).

cnf(c_327,plain,
    ( k3_subset_1(u1_struct_0(sK1),sK2) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_325,c_22])).

cnf(c_1398,plain,
    ( k4_xboole_0(u1_struct_0(sK1),sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1316,c_327])).

cnf(c_1563,plain,
    ( k4_xboole_0(sK2,sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1179,c_1398])).

cnf(c_2016,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2014,c_1563])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:04:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.39/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/0.99  
% 2.39/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.39/0.99  
% 2.39/0.99  ------  iProver source info
% 2.39/0.99  
% 2.39/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.39/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.39/0.99  git: non_committed_changes: false
% 2.39/0.99  git: last_make_outside_of_git: false
% 2.39/0.99  
% 2.39/0.99  ------ 
% 2.39/0.99  
% 2.39/0.99  ------ Input Options
% 2.39/0.99  
% 2.39/0.99  --out_options                           all
% 2.39/0.99  --tptp_safe_out                         true
% 2.39/0.99  --problem_path                          ""
% 2.39/0.99  --include_path                          ""
% 2.39/0.99  --clausifier                            res/vclausify_rel
% 2.39/0.99  --clausifier_options                    --mode clausify
% 2.39/0.99  --stdin                                 false
% 2.39/0.99  --stats_out                             all
% 2.39/0.99  
% 2.39/0.99  ------ General Options
% 2.39/0.99  
% 2.39/0.99  --fof                                   false
% 2.39/0.99  --time_out_real                         305.
% 2.39/0.99  --time_out_virtual                      -1.
% 2.39/0.99  --symbol_type_check                     false
% 2.39/0.99  --clausify_out                          false
% 2.39/0.99  --sig_cnt_out                           false
% 2.39/0.99  --trig_cnt_out                          false
% 2.39/0.99  --trig_cnt_out_tolerance                1.
% 2.39/0.99  --trig_cnt_out_sk_spl                   false
% 2.39/0.99  --abstr_cl_out                          false
% 2.39/0.99  
% 2.39/0.99  ------ Global Options
% 2.39/0.99  
% 2.39/0.99  --schedule                              default
% 2.39/0.99  --add_important_lit                     false
% 2.39/0.99  --prop_solver_per_cl                    1000
% 2.39/0.99  --min_unsat_core                        false
% 2.39/0.99  --soft_assumptions                      false
% 2.39/0.99  --soft_lemma_size                       3
% 2.39/0.99  --prop_impl_unit_size                   0
% 2.39/0.99  --prop_impl_unit                        []
% 2.39/0.99  --share_sel_clauses                     true
% 2.39/0.99  --reset_solvers                         false
% 2.39/0.99  --bc_imp_inh                            [conj_cone]
% 2.39/0.99  --conj_cone_tolerance                   3.
% 2.39/0.99  --extra_neg_conj                        none
% 2.39/0.99  --large_theory_mode                     true
% 2.39/0.99  --prolific_symb_bound                   200
% 2.39/0.99  --lt_threshold                          2000
% 2.39/0.99  --clause_weak_htbl                      true
% 2.39/0.99  --gc_record_bc_elim                     false
% 2.39/0.99  
% 2.39/0.99  ------ Preprocessing Options
% 2.39/0.99  
% 2.39/0.99  --preprocessing_flag                    true
% 2.39/0.99  --time_out_prep_mult                    0.1
% 2.39/0.99  --splitting_mode                        input
% 2.39/0.99  --splitting_grd                         true
% 2.39/0.99  --splitting_cvd                         false
% 2.39/0.99  --splitting_cvd_svl                     false
% 2.39/0.99  --splitting_nvd                         32
% 2.39/0.99  --sub_typing                            true
% 2.39/0.99  --prep_gs_sim                           true
% 2.39/0.99  --prep_unflatten                        true
% 2.39/0.99  --prep_res_sim                          true
% 2.39/0.99  --prep_upred                            true
% 2.39/0.99  --prep_sem_filter                       exhaustive
% 2.39/0.99  --prep_sem_filter_out                   false
% 2.39/0.99  --pred_elim                             true
% 2.39/0.99  --res_sim_input                         true
% 2.39/0.99  --eq_ax_congr_red                       true
% 2.39/0.99  --pure_diseq_elim                       true
% 2.39/0.99  --brand_transform                       false
% 2.39/0.99  --non_eq_to_eq                          false
% 2.39/0.99  --prep_def_merge                        true
% 2.39/0.99  --prep_def_merge_prop_impl              false
% 2.39/0.99  --prep_def_merge_mbd                    true
% 2.39/0.99  --prep_def_merge_tr_red                 false
% 2.39/0.99  --prep_def_merge_tr_cl                  false
% 2.39/0.99  --smt_preprocessing                     true
% 2.39/0.99  --smt_ac_axioms                         fast
% 2.39/0.99  --preprocessed_out                      false
% 2.39/0.99  --preprocessed_stats                    false
% 2.39/0.99  
% 2.39/0.99  ------ Abstraction refinement Options
% 2.39/0.99  
% 2.39/0.99  --abstr_ref                             []
% 2.39/0.99  --abstr_ref_prep                        false
% 2.39/0.99  --abstr_ref_until_sat                   false
% 2.39/0.99  --abstr_ref_sig_restrict                funpre
% 2.39/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.39/0.99  --abstr_ref_under                       []
% 2.39/0.99  
% 2.39/0.99  ------ SAT Options
% 2.39/0.99  
% 2.39/0.99  --sat_mode                              false
% 2.39/0.99  --sat_fm_restart_options                ""
% 2.39/0.99  --sat_gr_def                            false
% 2.39/0.99  --sat_epr_types                         true
% 2.39/0.99  --sat_non_cyclic_types                  false
% 2.39/0.99  --sat_finite_models                     false
% 2.39/0.99  --sat_fm_lemmas                         false
% 2.39/0.99  --sat_fm_prep                           false
% 2.39/0.99  --sat_fm_uc_incr                        true
% 2.39/0.99  --sat_out_model                         small
% 2.39/0.99  --sat_out_clauses                       false
% 2.39/0.99  
% 2.39/0.99  ------ QBF Options
% 2.39/0.99  
% 2.39/0.99  --qbf_mode                              false
% 2.39/0.99  --qbf_elim_univ                         false
% 2.39/0.99  --qbf_dom_inst                          none
% 2.39/0.99  --qbf_dom_pre_inst                      false
% 2.39/0.99  --qbf_sk_in                             false
% 2.39/0.99  --qbf_pred_elim                         true
% 2.39/0.99  --qbf_split                             512
% 2.39/0.99  
% 2.39/0.99  ------ BMC1 Options
% 2.39/0.99  
% 2.39/0.99  --bmc1_incremental                      false
% 2.39/0.99  --bmc1_axioms                           reachable_all
% 2.39/0.99  --bmc1_min_bound                        0
% 2.39/0.99  --bmc1_max_bound                        -1
% 2.39/0.99  --bmc1_max_bound_default                -1
% 2.39/0.99  --bmc1_symbol_reachability              true
% 2.39/0.99  --bmc1_property_lemmas                  false
% 2.39/0.99  --bmc1_k_induction                      false
% 2.39/0.99  --bmc1_non_equiv_states                 false
% 2.39/0.99  --bmc1_deadlock                         false
% 2.39/0.99  --bmc1_ucm                              false
% 2.39/0.99  --bmc1_add_unsat_core                   none
% 2.39/0.99  --bmc1_unsat_core_children              false
% 2.39/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.39/0.99  --bmc1_out_stat                         full
% 2.39/0.99  --bmc1_ground_init                      false
% 2.39/0.99  --bmc1_pre_inst_next_state              false
% 2.39/0.99  --bmc1_pre_inst_state                   false
% 2.39/0.99  --bmc1_pre_inst_reach_state             false
% 2.39/0.99  --bmc1_out_unsat_core                   false
% 2.39/0.99  --bmc1_aig_witness_out                  false
% 2.39/0.99  --bmc1_verbose                          false
% 2.39/0.99  --bmc1_dump_clauses_tptp                false
% 2.39/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.39/0.99  --bmc1_dump_file                        -
% 2.39/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.39/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.39/0.99  --bmc1_ucm_extend_mode                  1
% 2.39/0.99  --bmc1_ucm_init_mode                    2
% 2.39/0.99  --bmc1_ucm_cone_mode                    none
% 2.39/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.39/0.99  --bmc1_ucm_relax_model                  4
% 2.39/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.39/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.39/0.99  --bmc1_ucm_layered_model                none
% 2.39/0.99  --bmc1_ucm_max_lemma_size               10
% 2.39/0.99  
% 2.39/0.99  ------ AIG Options
% 2.39/0.99  
% 2.39/0.99  --aig_mode                              false
% 2.39/0.99  
% 2.39/0.99  ------ Instantiation Options
% 2.39/0.99  
% 2.39/0.99  --instantiation_flag                    true
% 2.39/0.99  --inst_sos_flag                         false
% 2.39/0.99  --inst_sos_phase                        true
% 2.39/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.39/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.39/0.99  --inst_lit_sel_side                     num_symb
% 2.39/0.99  --inst_solver_per_active                1400
% 2.39/0.99  --inst_solver_calls_frac                1.
% 2.39/0.99  --inst_passive_queue_type               priority_queues
% 2.39/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.39/0.99  --inst_passive_queues_freq              [25;2]
% 2.39/0.99  --inst_dismatching                      true
% 2.39/0.99  --inst_eager_unprocessed_to_passive     true
% 2.39/0.99  --inst_prop_sim_given                   true
% 2.39/0.99  --inst_prop_sim_new                     false
% 2.39/0.99  --inst_subs_new                         false
% 2.39/0.99  --inst_eq_res_simp                      false
% 2.39/0.99  --inst_subs_given                       false
% 2.39/0.99  --inst_orphan_elimination               true
% 2.39/0.99  --inst_learning_loop_flag               true
% 2.39/0.99  --inst_learning_start                   3000
% 2.39/0.99  --inst_learning_factor                  2
% 2.39/0.99  --inst_start_prop_sim_after_learn       3
% 2.39/0.99  --inst_sel_renew                        solver
% 2.39/0.99  --inst_lit_activity_flag                true
% 2.39/0.99  --inst_restr_to_given                   false
% 2.39/0.99  --inst_activity_threshold               500
% 2.39/0.99  --inst_out_proof                        true
% 2.39/0.99  
% 2.39/0.99  ------ Resolution Options
% 2.39/0.99  
% 2.39/0.99  --resolution_flag                       true
% 2.39/0.99  --res_lit_sel                           adaptive
% 2.39/0.99  --res_lit_sel_side                      none
% 2.39/0.99  --res_ordering                          kbo
% 2.39/0.99  --res_to_prop_solver                    active
% 2.39/0.99  --res_prop_simpl_new                    false
% 2.39/0.99  --res_prop_simpl_given                  true
% 2.39/0.99  --res_passive_queue_type                priority_queues
% 2.39/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.39/0.99  --res_passive_queues_freq               [15;5]
% 2.39/0.99  --res_forward_subs                      full
% 2.39/0.99  --res_backward_subs                     full
% 2.39/0.99  --res_forward_subs_resolution           true
% 2.39/0.99  --res_backward_subs_resolution          true
% 2.39/0.99  --res_orphan_elimination                true
% 2.39/0.99  --res_time_limit                        2.
% 2.39/0.99  --res_out_proof                         true
% 2.39/0.99  
% 2.39/0.99  ------ Superposition Options
% 2.39/0.99  
% 2.39/0.99  --superposition_flag                    true
% 2.39/0.99  --sup_passive_queue_type                priority_queues
% 2.39/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.39/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.39/0.99  --demod_completeness_check              fast
% 2.39/0.99  --demod_use_ground                      true
% 2.39/0.99  --sup_to_prop_solver                    passive
% 2.39/0.99  --sup_prop_simpl_new                    true
% 2.39/0.99  --sup_prop_simpl_given                  true
% 2.39/0.99  --sup_fun_splitting                     false
% 2.39/0.99  --sup_smt_interval                      50000
% 2.39/0.99  
% 2.39/0.99  ------ Superposition Simplification Setup
% 2.39/0.99  
% 2.39/0.99  --sup_indices_passive                   []
% 2.39/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.39/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.39/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.39/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.39/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.39/0.99  --sup_full_bw                           [BwDemod]
% 2.39/0.99  --sup_immed_triv                        [TrivRules]
% 2.39/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.39/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.39/0.99  --sup_immed_bw_main                     []
% 2.39/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.39/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.39/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.39/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.39/0.99  
% 2.39/0.99  ------ Combination Options
% 2.39/0.99  
% 2.39/0.99  --comb_res_mult                         3
% 2.39/0.99  --comb_sup_mult                         2
% 2.39/0.99  --comb_inst_mult                        10
% 2.39/0.99  
% 2.39/0.99  ------ Debug Options
% 2.39/0.99  
% 2.39/0.99  --dbg_backtrace                         false
% 2.39/0.99  --dbg_dump_prop_clauses                 false
% 2.39/0.99  --dbg_dump_prop_clauses_file            -
% 2.39/0.99  --dbg_out_stat                          false
% 2.39/0.99  ------ Parsing...
% 2.39/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.39/0.99  
% 2.39/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 2.39/0.99  
% 2.39/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.39/0.99  
% 2.39/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.39/0.99  ------ Proving...
% 2.39/0.99  ------ Problem Properties 
% 2.39/0.99  
% 2.39/0.99  
% 2.39/0.99  clauses                                 13
% 2.39/0.99  conjectures                             1
% 2.39/0.99  EPR                                     0
% 2.39/0.99  Horn                                    12
% 2.39/0.99  unary                                   5
% 2.39/0.99  binary                                  4
% 2.39/0.99  lits                                    26
% 2.39/0.99  lits eq                                 9
% 2.39/0.99  fd_pure                                 0
% 2.39/0.99  fd_pseudo                               0
% 2.39/0.99  fd_cond                                 0
% 2.39/0.99  fd_pseudo_cond                          0
% 2.39/0.99  AC symbols                              0
% 2.39/0.99  
% 2.39/0.99  ------ Schedule dynamic 5 is on 
% 2.39/0.99  
% 2.39/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.39/0.99  
% 2.39/0.99  
% 2.39/0.99  ------ 
% 2.39/0.99  Current options:
% 2.39/0.99  ------ 
% 2.39/0.99  
% 2.39/0.99  ------ Input Options
% 2.39/0.99  
% 2.39/0.99  --out_options                           all
% 2.39/0.99  --tptp_safe_out                         true
% 2.39/0.99  --problem_path                          ""
% 2.39/0.99  --include_path                          ""
% 2.39/0.99  --clausifier                            res/vclausify_rel
% 2.39/0.99  --clausifier_options                    --mode clausify
% 2.39/0.99  --stdin                                 false
% 2.39/0.99  --stats_out                             all
% 2.39/0.99  
% 2.39/0.99  ------ General Options
% 2.39/0.99  
% 2.39/0.99  --fof                                   false
% 2.39/0.99  --time_out_real                         305.
% 2.39/0.99  --time_out_virtual                      -1.
% 2.39/0.99  --symbol_type_check                     false
% 2.39/0.99  --clausify_out                          false
% 2.39/0.99  --sig_cnt_out                           false
% 2.39/0.99  --trig_cnt_out                          false
% 2.39/0.99  --trig_cnt_out_tolerance                1.
% 2.39/0.99  --trig_cnt_out_sk_spl                   false
% 2.39/0.99  --abstr_cl_out                          false
% 2.39/0.99  
% 2.39/0.99  ------ Global Options
% 2.39/0.99  
% 2.39/0.99  --schedule                              default
% 2.39/0.99  --add_important_lit                     false
% 2.39/0.99  --prop_solver_per_cl                    1000
% 2.39/0.99  --min_unsat_core                        false
% 2.39/0.99  --soft_assumptions                      false
% 2.39/0.99  --soft_lemma_size                       3
% 2.39/0.99  --prop_impl_unit_size                   0
% 2.39/0.99  --prop_impl_unit                        []
% 2.39/0.99  --share_sel_clauses                     true
% 2.39/0.99  --reset_solvers                         false
% 2.39/0.99  --bc_imp_inh                            [conj_cone]
% 2.39/0.99  --conj_cone_tolerance                   3.
% 2.39/0.99  --extra_neg_conj                        none
% 2.39/0.99  --large_theory_mode                     true
% 2.39/0.99  --prolific_symb_bound                   200
% 2.39/0.99  --lt_threshold                          2000
% 2.39/0.99  --clause_weak_htbl                      true
% 2.39/0.99  --gc_record_bc_elim                     false
% 2.39/0.99  
% 2.39/0.99  ------ Preprocessing Options
% 2.39/0.99  
% 2.39/0.99  --preprocessing_flag                    true
% 2.39/0.99  --time_out_prep_mult                    0.1
% 2.39/0.99  --splitting_mode                        input
% 2.39/0.99  --splitting_grd                         true
% 2.39/0.99  --splitting_cvd                         false
% 2.39/0.99  --splitting_cvd_svl                     false
% 2.39/0.99  --splitting_nvd                         32
% 2.39/0.99  --sub_typing                            true
% 2.39/0.99  --prep_gs_sim                           true
% 2.39/0.99  --prep_unflatten                        true
% 2.39/0.99  --prep_res_sim                          true
% 2.39/0.99  --prep_upred                            true
% 2.39/0.99  --prep_sem_filter                       exhaustive
% 2.39/0.99  --prep_sem_filter_out                   false
% 2.39/0.99  --pred_elim                             true
% 2.39/0.99  --res_sim_input                         true
% 2.39/0.99  --eq_ax_congr_red                       true
% 2.39/0.99  --pure_diseq_elim                       true
% 2.39/0.99  --brand_transform                       false
% 2.39/0.99  --non_eq_to_eq                          false
% 2.39/0.99  --prep_def_merge                        true
% 2.39/0.99  --prep_def_merge_prop_impl              false
% 2.39/0.99  --prep_def_merge_mbd                    true
% 2.39/0.99  --prep_def_merge_tr_red                 false
% 2.39/0.99  --prep_def_merge_tr_cl                  false
% 2.39/0.99  --smt_preprocessing                     true
% 2.39/0.99  --smt_ac_axioms                         fast
% 2.39/0.99  --preprocessed_out                      false
% 2.39/0.99  --preprocessed_stats                    false
% 2.39/0.99  
% 2.39/0.99  ------ Abstraction refinement Options
% 2.39/0.99  
% 2.39/0.99  --abstr_ref                             []
% 2.39/0.99  --abstr_ref_prep                        false
% 2.39/0.99  --abstr_ref_until_sat                   false
% 2.39/0.99  --abstr_ref_sig_restrict                funpre
% 2.39/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.39/0.99  --abstr_ref_under                       []
% 2.39/0.99  
% 2.39/0.99  ------ SAT Options
% 2.39/0.99  
% 2.39/0.99  --sat_mode                              false
% 2.39/0.99  --sat_fm_restart_options                ""
% 2.39/0.99  --sat_gr_def                            false
% 2.39/0.99  --sat_epr_types                         true
% 2.39/0.99  --sat_non_cyclic_types                  false
% 2.39/0.99  --sat_finite_models                     false
% 2.39/0.99  --sat_fm_lemmas                         false
% 2.39/0.99  --sat_fm_prep                           false
% 2.39/0.99  --sat_fm_uc_incr                        true
% 2.39/0.99  --sat_out_model                         small
% 2.39/0.99  --sat_out_clauses                       false
% 2.39/0.99  
% 2.39/0.99  ------ QBF Options
% 2.39/0.99  
% 2.39/0.99  --qbf_mode                              false
% 2.39/0.99  --qbf_elim_univ                         false
% 2.39/0.99  --qbf_dom_inst                          none
% 2.39/0.99  --qbf_dom_pre_inst                      false
% 2.39/0.99  --qbf_sk_in                             false
% 2.39/0.99  --qbf_pred_elim                         true
% 2.39/0.99  --qbf_split                             512
% 2.39/0.99  
% 2.39/0.99  ------ BMC1 Options
% 2.39/0.99  
% 2.39/0.99  --bmc1_incremental                      false
% 2.39/0.99  --bmc1_axioms                           reachable_all
% 2.39/0.99  --bmc1_min_bound                        0
% 2.39/0.99  --bmc1_max_bound                        -1
% 2.39/0.99  --bmc1_max_bound_default                -1
% 2.39/0.99  --bmc1_symbol_reachability              true
% 2.39/0.99  --bmc1_property_lemmas                  false
% 2.39/0.99  --bmc1_k_induction                      false
% 2.39/0.99  --bmc1_non_equiv_states                 false
% 2.39/0.99  --bmc1_deadlock                         false
% 2.39/0.99  --bmc1_ucm                              false
% 2.39/0.99  --bmc1_add_unsat_core                   none
% 2.39/0.99  --bmc1_unsat_core_children              false
% 2.39/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.39/0.99  --bmc1_out_stat                         full
% 2.39/0.99  --bmc1_ground_init                      false
% 2.39/0.99  --bmc1_pre_inst_next_state              false
% 2.39/0.99  --bmc1_pre_inst_state                   false
% 2.39/0.99  --bmc1_pre_inst_reach_state             false
% 2.39/0.99  --bmc1_out_unsat_core                   false
% 2.39/0.99  --bmc1_aig_witness_out                  false
% 2.39/0.99  --bmc1_verbose                          false
% 2.39/0.99  --bmc1_dump_clauses_tptp                false
% 2.39/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.39/0.99  --bmc1_dump_file                        -
% 2.39/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.39/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.39/0.99  --bmc1_ucm_extend_mode                  1
% 2.39/0.99  --bmc1_ucm_init_mode                    2
% 2.39/0.99  --bmc1_ucm_cone_mode                    none
% 2.39/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.39/0.99  --bmc1_ucm_relax_model                  4
% 2.39/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.39/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.39/0.99  --bmc1_ucm_layered_model                none
% 2.39/0.99  --bmc1_ucm_max_lemma_size               10
% 2.39/0.99  
% 2.39/0.99  ------ AIG Options
% 2.39/0.99  
% 2.39/0.99  --aig_mode                              false
% 2.39/0.99  
% 2.39/0.99  ------ Instantiation Options
% 2.39/0.99  
% 2.39/0.99  --instantiation_flag                    true
% 2.39/0.99  --inst_sos_flag                         false
% 2.39/0.99  --inst_sos_phase                        true
% 2.39/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.39/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.39/0.99  --inst_lit_sel_side                     none
% 2.39/0.99  --inst_solver_per_active                1400
% 2.39/0.99  --inst_solver_calls_frac                1.
% 2.39/0.99  --inst_passive_queue_type               priority_queues
% 2.39/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.39/0.99  --inst_passive_queues_freq              [25;2]
% 2.39/0.99  --inst_dismatching                      true
% 2.39/0.99  --inst_eager_unprocessed_to_passive     true
% 2.39/0.99  --inst_prop_sim_given                   true
% 2.39/0.99  --inst_prop_sim_new                     false
% 2.39/0.99  --inst_subs_new                         false
% 2.39/0.99  --inst_eq_res_simp                      false
% 2.39/0.99  --inst_subs_given                       false
% 2.39/0.99  --inst_orphan_elimination               true
% 2.39/0.99  --inst_learning_loop_flag               true
% 2.39/0.99  --inst_learning_start                   3000
% 2.39/0.99  --inst_learning_factor                  2
% 2.39/0.99  --inst_start_prop_sim_after_learn       3
% 2.39/0.99  --inst_sel_renew                        solver
% 2.39/0.99  --inst_lit_activity_flag                true
% 2.39/0.99  --inst_restr_to_given                   false
% 2.39/0.99  --inst_activity_threshold               500
% 2.39/0.99  --inst_out_proof                        true
% 2.39/0.99  
% 2.39/0.99  ------ Resolution Options
% 2.39/0.99  
% 2.39/0.99  --resolution_flag                       false
% 2.39/0.99  --res_lit_sel                           adaptive
% 2.39/0.99  --res_lit_sel_side                      none
% 2.39/0.99  --res_ordering                          kbo
% 2.39/0.99  --res_to_prop_solver                    active
% 2.39/0.99  --res_prop_simpl_new                    false
% 2.39/0.99  --res_prop_simpl_given                  true
% 2.39/0.99  --res_passive_queue_type                priority_queues
% 2.39/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.39/0.99  --res_passive_queues_freq               [15;5]
% 2.39/0.99  --res_forward_subs                      full
% 2.39/0.99  --res_backward_subs                     full
% 2.39/0.99  --res_forward_subs_resolution           true
% 2.39/0.99  --res_backward_subs_resolution          true
% 2.39/0.99  --res_orphan_elimination                true
% 2.39/0.99  --res_time_limit                        2.
% 2.39/0.99  --res_out_proof                         true
% 2.39/0.99  
% 2.39/0.99  ------ Superposition Options
% 2.39/0.99  
% 2.39/0.99  --superposition_flag                    true
% 2.39/0.99  --sup_passive_queue_type                priority_queues
% 2.39/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.39/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.39/0.99  --demod_completeness_check              fast
% 2.39/0.99  --demod_use_ground                      true
% 2.39/0.99  --sup_to_prop_solver                    passive
% 2.39/0.99  --sup_prop_simpl_new                    true
% 2.39/0.99  --sup_prop_simpl_given                  true
% 2.39/0.99  --sup_fun_splitting                     false
% 2.39/0.99  --sup_smt_interval                      50000
% 2.39/0.99  
% 2.39/0.99  ------ Superposition Simplification Setup
% 2.39/0.99  
% 2.39/0.99  --sup_indices_passive                   []
% 2.39/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.39/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.39/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.39/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.39/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.39/0.99  --sup_full_bw                           [BwDemod]
% 2.39/0.99  --sup_immed_triv                        [TrivRules]
% 2.39/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.39/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.39/0.99  --sup_immed_bw_main                     []
% 2.39/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.39/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.39/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.39/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.39/0.99  
% 2.39/0.99  ------ Combination Options
% 2.39/0.99  
% 2.39/0.99  --comb_res_mult                         3
% 2.39/0.99  --comb_sup_mult                         2
% 2.39/0.99  --comb_inst_mult                        10
% 2.39/0.99  
% 2.39/0.99  ------ Debug Options
% 2.39/0.99  
% 2.39/0.99  --dbg_backtrace                         false
% 2.39/0.99  --dbg_dump_prop_clauses                 false
% 2.39/0.99  --dbg_dump_prop_clauses_file            -
% 2.39/0.99  --dbg_out_stat                          false
% 2.39/0.99  
% 2.39/0.99  
% 2.39/0.99  
% 2.39/0.99  
% 2.39/0.99  ------ Proving...
% 2.39/0.99  
% 2.39/0.99  
% 2.39/0.99  % SZS status Theorem for theBenchmark.p
% 2.39/0.99  
% 2.39/0.99   Resolution empty clause
% 2.39/0.99  
% 2.39/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.39/0.99  
% 2.39/0.99  fof(f15,conjecture,(
% 2.39/0.99    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)))))),
% 2.39/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.39/0.99  
% 2.39/0.99  fof(f16,negated_conjecture,(
% 2.39/0.99    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)))))),
% 2.39/0.99    inference(negated_conjecture,[],[f15])).
% 2.39/0.99  
% 2.39/0.99  fof(f32,plain,(
% 2.39/0.99    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.39/0.99    inference(ennf_transformation,[],[f16])).
% 2.39/0.99  
% 2.39/0.99  fof(f33,plain,(
% 2.39/0.99    ? [X0] : (? [X1] : (v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.39/0.99    inference(flattening,[],[f32])).
% 2.39/0.99  
% 2.39/0.99  fof(f41,plain,(
% 2.39/0.99    ( ! [X0] : (? [X1] : (v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v1_subset_1(sK2,u1_struct_0(X0)) & v3_tex_2(sK2,X0) & (v4_pre_topc(sK2,X0) | v3_pre_topc(sK2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.39/0.99    introduced(choice_axiom,[])).
% 2.39/0.99  
% 2.39/0.99  fof(f40,plain,(
% 2.39/0.99    ? [X0] : (? [X1] : (v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (v1_subset_1(X1,u1_struct_0(sK1)) & v3_tex_2(X1,sK1) & (v4_pre_topc(X1,sK1) | v3_pre_topc(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v3_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.39/0.99    introduced(choice_axiom,[])).
% 2.39/0.99  
% 2.39/0.99  fof(f42,plain,(
% 2.39/0.99    (v1_subset_1(sK2,u1_struct_0(sK1)) & v3_tex_2(sK2,sK1) & (v4_pre_topc(sK2,sK1) | v3_pre_topc(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v3_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.39/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f33,f41,f40])).
% 2.39/0.99  
% 2.39/0.99  fof(f67,plain,(
% 2.39/0.99    v4_pre_topc(sK2,sK1) | v3_pre_topc(sK2,sK1)),
% 2.39/0.99    inference(cnf_transformation,[],[f42])).
% 2.39/0.99  
% 2.39/0.99  fof(f10,axiom,(
% 2.39/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 2.39/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.39/0.99  
% 2.39/0.99  fof(f24,plain,(
% 2.39/0.99    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.39/0.99    inference(ennf_transformation,[],[f10])).
% 2.39/0.99  
% 2.39/0.99  fof(f34,plain,(
% 2.39/0.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.39/0.99    inference(nnf_transformation,[],[f24])).
% 2.39/0.99  
% 2.39/0.99  fof(f53,plain,(
% 2.39/0.99    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.39/0.99    inference(cnf_transformation,[],[f34])).
% 2.39/0.99  
% 2.39/0.99  fof(f65,plain,(
% 2.39/0.99    l1_pre_topc(sK1)),
% 2.39/0.99    inference(cnf_transformation,[],[f42])).
% 2.39/0.99  
% 2.39/0.99  fof(f66,plain,(
% 2.39/0.99    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.39/0.99    inference(cnf_transformation,[],[f42])).
% 2.39/0.99  
% 2.39/0.99  fof(f13,axiom,(
% 2.39/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 2.39/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.39/0.99  
% 2.39/0.99  fof(f28,plain,(
% 2.39/0.99    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.39/0.99    inference(ennf_transformation,[],[f13])).
% 2.39/0.99  
% 2.39/0.99  fof(f29,plain,(
% 2.39/0.99    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.39/0.99    inference(flattening,[],[f28])).
% 2.39/0.99  
% 2.39/0.99  fof(f36,plain,(
% 2.39/0.99    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.39/0.99    inference(nnf_transformation,[],[f29])).
% 2.39/0.99  
% 2.39/0.99  fof(f37,plain,(
% 2.39/0.99    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.39/0.99    inference(rectify,[],[f36])).
% 2.39/0.99  
% 2.39/0.99  fof(f38,plain,(
% 2.39/0.99    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK0(X0),X0) & v4_pre_topc(sK0(X0),X0) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.39/0.99    introduced(choice_axiom,[])).
% 2.39/0.99  
% 2.39/0.99  fof(f39,plain,(
% 2.39/0.99    ! [X0] : (((v3_tdlat_3(X0) | (~v3_pre_topc(sK0(X0),X0) & v4_pre_topc(sK0(X0),X0) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.39/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 2.39/0.99  
% 2.39/0.99  fof(f57,plain,(
% 2.39/0.99    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.39/0.99    inference(cnf_transformation,[],[f39])).
% 2.39/0.99  
% 2.39/0.99  fof(f63,plain,(
% 2.39/0.99    v2_pre_topc(sK1)),
% 2.39/0.99    inference(cnf_transformation,[],[f42])).
% 2.39/0.99  
% 2.39/0.99  fof(f64,plain,(
% 2.39/0.99    v3_tdlat_3(sK1)),
% 2.39/0.99    inference(cnf_transformation,[],[f42])).
% 2.39/0.99  
% 2.39/0.99  fof(f4,axiom,(
% 2.39/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.39/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.39/0.99  
% 2.39/0.99  fof(f19,plain,(
% 2.39/0.99    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.39/0.99    inference(ennf_transformation,[],[f4])).
% 2.39/0.99  
% 2.39/0.99  fof(f46,plain,(
% 2.39/0.99    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.39/0.99    inference(cnf_transformation,[],[f19])).
% 2.39/0.99  
% 2.39/0.99  fof(f5,axiom,(
% 2.39/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.39/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.39/0.99  
% 2.39/0.99  fof(f20,plain,(
% 2.39/0.99    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.39/0.99    inference(ennf_transformation,[],[f5])).
% 2.39/0.99  
% 2.39/0.99  fof(f47,plain,(
% 2.39/0.99    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.39/0.99    inference(cnf_transformation,[],[f20])).
% 2.39/0.99  
% 2.39/0.99  fof(f9,axiom,(
% 2.39/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.39/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.39/0.99  
% 2.39/0.99  fof(f22,plain,(
% 2.39/0.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.39/0.99    inference(ennf_transformation,[],[f9])).
% 2.39/0.99  
% 2.39/0.99  fof(f23,plain,(
% 2.39/0.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.39/0.99    inference(flattening,[],[f22])).
% 2.39/0.99  
% 2.39/0.99  fof(f50,plain,(
% 2.39/0.99    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.39/0.99    inference(cnf_transformation,[],[f23])).
% 2.39/0.99  
% 2.39/0.99  fof(f11,axiom,(
% 2.39/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 2.39/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.39/0.99  
% 2.39/0.99  fof(f25,plain,(
% 2.39/0.99    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.39/0.99    inference(ennf_transformation,[],[f11])).
% 2.39/0.99  
% 2.39/0.99  fof(f35,plain,(
% 2.39/0.99    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.39/0.99    inference(nnf_transformation,[],[f25])).
% 2.39/0.99  
% 2.39/0.99  fof(f54,plain,(
% 2.39/0.99    ( ! [X0,X1] : (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.39/0.99    inference(cnf_transformation,[],[f35])).
% 2.39/0.99  
% 2.39/0.99  fof(f14,axiom,(
% 2.39/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 2.39/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.39/0.99  
% 2.39/0.99  fof(f30,plain,(
% 2.39/0.99    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.39/0.99    inference(ennf_transformation,[],[f14])).
% 2.39/0.99  
% 2.39/0.99  fof(f31,plain,(
% 2.39/0.99    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.39/0.99    inference(flattening,[],[f30])).
% 2.39/0.99  
% 2.39/0.99  fof(f61,plain,(
% 2.39/0.99    ( ! [X0,X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.39/0.99    inference(cnf_transformation,[],[f31])).
% 2.39/0.99  
% 2.39/0.99  fof(f68,plain,(
% 2.39/0.99    v3_tex_2(sK2,sK1)),
% 2.39/0.99    inference(cnf_transformation,[],[f42])).
% 2.39/0.99  
% 2.39/0.99  fof(f62,plain,(
% 2.39/0.99    ~v2_struct_0(sK1)),
% 2.39/0.99    inference(cnf_transformation,[],[f42])).
% 2.39/0.99  
% 2.39/0.99  fof(f3,axiom,(
% 2.39/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.39/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.39/0.99  
% 2.39/0.99  fof(f18,plain,(
% 2.39/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.39/0.99    inference(ennf_transformation,[],[f3])).
% 2.39/0.99  
% 2.39/0.99  fof(f45,plain,(
% 2.39/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.39/0.99    inference(cnf_transformation,[],[f18])).
% 2.39/0.99  
% 2.39/0.99  fof(f6,axiom,(
% 2.39/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.39/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.39/0.99  
% 2.39/0.99  fof(f48,plain,(
% 2.39/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.39/0.99    inference(cnf_transformation,[],[f6])).
% 2.39/0.99  
% 2.39/0.99  fof(f2,axiom,(
% 2.39/0.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.39/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.39/0.99  
% 2.39/0.99  fof(f44,plain,(
% 2.39/0.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.39/0.99    inference(cnf_transformation,[],[f2])).
% 2.39/0.99  
% 2.39/0.99  fof(f1,axiom,(
% 2.39/0.99    v1_xboole_0(k1_xboole_0)),
% 2.39/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.39/0.99  
% 2.39/0.99  fof(f43,plain,(
% 2.39/0.99    v1_xboole_0(k1_xboole_0)),
% 2.39/0.99    inference(cnf_transformation,[],[f1])).
% 2.39/0.99  
% 2.39/0.99  fof(f12,axiom,(
% 2.39/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(X0)) & v1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k3_subset_1(X0,X1)))),
% 2.39/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.39/0.99  
% 2.39/0.99  fof(f26,plain,(
% 2.39/0.99    ! [X0,X1] : (~v1_xboole_0(k3_subset_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.39/0.99    inference(ennf_transformation,[],[f12])).
% 2.39/0.99  
% 2.39/0.99  fof(f27,plain,(
% 2.39/0.99    ! [X0,X1] : (~v1_xboole_0(k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.39/0.99    inference(flattening,[],[f26])).
% 2.39/0.99  
% 2.39/0.99  fof(f56,plain,(
% 2.39/0.99    ( ! [X0,X1] : (~v1_xboole_0(k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.39/0.99    inference(cnf_transformation,[],[f27])).
% 2.39/0.99  
% 2.39/0.99  fof(f7,axiom,(
% 2.39/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~v1_subset_1(X1,X0)))),
% 2.39/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.39/0.99  
% 2.39/0.99  fof(f21,plain,(
% 2.39/0.99    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.39/0.99    inference(ennf_transformation,[],[f7])).
% 2.39/0.99  
% 2.39/0.99  fof(f49,plain,(
% 2.39/0.99    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.39/0.99    inference(cnf_transformation,[],[f21])).
% 2.39/0.99  
% 2.39/0.99  fof(f69,plain,(
% 2.39/0.99    v1_subset_1(sK2,u1_struct_0(sK1))),
% 2.39/0.99    inference(cnf_transformation,[],[f42])).
% 2.39/0.99  
% 2.39/0.99  cnf(c_21,negated_conjecture,
% 2.39/0.99      ( v3_pre_topc(sK2,sK1) | v4_pre_topc(sK2,sK1) ),
% 2.39/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_9,plain,
% 2.39/0.99      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 2.39/0.99      | v4_pre_topc(X1,X0)
% 2.39/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.39/0.99      | ~ l1_pre_topc(X0) ),
% 2.39/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_23,negated_conjecture,
% 2.39/0.99      ( l1_pre_topc(sK1) ),
% 2.39/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_452,plain,
% 2.39/0.99      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 2.39/0.99      | v4_pre_topc(X1,X0)
% 2.39/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.39/0.99      | sK1 != X0 ),
% 2.39/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_23]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_453,plain,
% 2.39/0.99      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),X0),sK1)
% 2.39/0.99      | v4_pre_topc(X0,sK1)
% 2.39/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.39/0.99      inference(unflattening,[status(thm)],[c_452]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_512,plain,
% 2.39/0.99      ( v4_pre_topc(X0,sK1)
% 2.39/0.99      | v4_pre_topc(sK2,sK1)
% 2.39/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.39/0.99      | k3_subset_1(u1_struct_0(sK1),X0) != sK2
% 2.39/0.99      | sK1 != sK1 ),
% 2.39/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_453]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_575,plain,
% 2.39/0.99      ( v4_pre_topc(X0,sK1)
% 2.39/0.99      | v4_pre_topc(sK2,sK1)
% 2.39/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.39/0.99      | k3_subset_1(u1_struct_0(sK1),X0) != sK2 ),
% 2.39/0.99      inference(equality_resolution_simp,[status(thm)],[c_512]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_834,plain,
% 2.39/0.99      ( k3_subset_1(u1_struct_0(sK1),X0) != sK2
% 2.39/0.99      | v4_pre_topc(X0,sK1) = iProver_top
% 2.39/0.99      | v4_pre_topc(sK2,sK1) = iProver_top
% 2.39/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.39/0.99      inference(predicate_to_equality,[status(thm)],[c_575]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_22,negated_conjecture,
% 2.39/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.39/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_31,plain,
% 2.39/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.39/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_17,plain,
% 2.39/0.99      ( v3_pre_topc(X0,X1)
% 2.39/0.99      | ~ v4_pre_topc(X0,X1)
% 2.39/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.39/0.99      | ~ v3_tdlat_3(X1)
% 2.39/0.99      | ~ l1_pre_topc(X1)
% 2.39/0.99      | ~ v2_pre_topc(X1) ),
% 2.39/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_25,negated_conjecture,
% 2.39/0.99      ( v2_pre_topc(sK1) ),
% 2.39/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_387,plain,
% 2.39/0.99      ( v3_pre_topc(X0,X1)
% 2.39/0.99      | ~ v4_pre_topc(X0,X1)
% 2.39/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.39/0.99      | ~ v3_tdlat_3(X1)
% 2.39/0.99      | ~ l1_pre_topc(X1)
% 2.39/0.99      | sK1 != X1 ),
% 2.39/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_388,plain,
% 2.39/0.99      ( v3_pre_topc(X0,sK1)
% 2.39/0.99      | ~ v4_pre_topc(X0,sK1)
% 2.39/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.39/0.99      | ~ v3_tdlat_3(sK1)
% 2.39/0.99      | ~ l1_pre_topc(sK1) ),
% 2.39/0.99      inference(unflattening,[status(thm)],[c_387]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_24,negated_conjecture,
% 2.39/0.99      ( v3_tdlat_3(sK1) ),
% 2.39/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_392,plain,
% 2.39/0.99      ( v3_pre_topc(X0,sK1)
% 2.39/0.99      | ~ v4_pre_topc(X0,sK1)
% 2.39/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.39/0.99      inference(global_propositional_subsumption,
% 2.39/0.99                [status(thm)],
% 2.39/0.99                [c_388,c_24,c_23]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_533,plain,
% 2.39/0.99      ( ~ v4_pre_topc(X0,sK1)
% 2.39/0.99      | v4_pre_topc(X1,sK1)
% 2.39/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.39/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.39/0.99      | k3_subset_1(u1_struct_0(sK1),X1) != X0
% 2.39/0.99      | sK1 != sK1 ),
% 2.39/0.99      inference(resolution_lifted,[status(thm)],[c_392,c_453]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_534,plain,
% 2.39/0.99      ( v4_pre_topc(X0,sK1)
% 2.39/0.99      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK1),X0),sK1)
% 2.39/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.39/0.99      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.39/0.99      inference(unflattening,[status(thm)],[c_533]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_3,plain,
% 2.39/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.39/0.99      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 2.39/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_546,plain,
% 2.39/0.99      ( v4_pre_topc(X0,sK1)
% 2.39/0.99      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK1),X0),sK1)
% 2.39/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.39/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_534,c_3]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_924,plain,
% 2.39/0.99      ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
% 2.39/0.99      | v4_pre_topc(sK2,sK1)
% 2.39/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.39/0.99      inference(instantiation,[status(thm)],[c_546]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_925,plain,
% 2.39/0.99      ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) != iProver_top
% 2.39/0.99      | v4_pre_topc(sK2,sK1) = iProver_top
% 2.39/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.39/0.99      inference(predicate_to_equality,[status(thm)],[c_924]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_944,plain,
% 2.39/0.99      ( m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.39/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.39/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_945,plain,
% 2.39/0.99      ( m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.39/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.39/0.99      inference(predicate_to_equality,[status(thm)],[c_944]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_4,plain,
% 2.39/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.39/0.99      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 2.39/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_960,plain,
% 2.39/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.39/0.99      | k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK2)) = sK2 ),
% 2.39/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_1143,plain,
% 2.39/0.99      ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
% 2.39/0.99      | v4_pre_topc(sK2,sK1)
% 2.39/0.99      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.39/0.99      | k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK2)) != sK2 ),
% 2.39/0.99      inference(instantiation,[status(thm)],[c_575]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_1144,plain,
% 2.39/0.99      ( k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK2)) != sK2
% 2.39/0.99      | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) = iProver_top
% 2.39/0.99      | v4_pre_topc(sK2,sK1) = iProver_top
% 2.39/0.99      | m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.39/0.99      inference(predicate_to_equality,[status(thm)],[c_1143]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_1174,plain,
% 2.39/0.99      ( v4_pre_topc(sK2,sK1) = iProver_top ),
% 2.39/0.99      inference(global_propositional_subsumption,
% 2.39/0.99                [status(thm)],
% 2.39/0.99                [c_834,c_22,c_31,c_925,c_945,c_960,c_1144]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_839,plain,
% 2.39/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.39/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_8,plain,
% 2.39/0.99      ( ~ v4_pre_topc(X0,X1)
% 2.39/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.39/0.99      | ~ l1_pre_topc(X1)
% 2.39/0.99      | k2_pre_topc(X1,X0) = X0 ),
% 2.39/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_467,plain,
% 2.39/0.99      ( ~ v4_pre_topc(X0,X1)
% 2.39/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.39/0.99      | k2_pre_topc(X1,X0) = X0
% 2.39/0.99      | sK1 != X1 ),
% 2.39/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_23]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_468,plain,
% 2.39/0.99      ( ~ v4_pre_topc(X0,sK1)
% 2.39/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.39/0.99      | k2_pre_topc(sK1,X0) = X0 ),
% 2.39/0.99      inference(unflattening,[status(thm)],[c_467]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_836,plain,
% 2.39/0.99      ( k2_pre_topc(sK1,X0) = X0
% 2.39/0.99      | v4_pre_topc(X0,sK1) != iProver_top
% 2.39/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.39/0.99      inference(predicate_to_equality,[status(thm)],[c_468]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_1054,plain,
% 2.39/0.99      ( k2_pre_topc(sK1,sK2) = sK2 | v4_pre_topc(sK2,sK1) != iProver_top ),
% 2.39/0.99      inference(superposition,[status(thm)],[c_839,c_836]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_12,plain,
% 2.39/0.99      ( ~ v1_tops_1(X0,X1)
% 2.39/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.39/0.99      | ~ l1_pre_topc(X1)
% 2.39/0.99      | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
% 2.39/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_18,plain,
% 2.39/0.99      ( ~ v3_tex_2(X0,X1)
% 2.39/0.99      | v1_tops_1(X0,X1)
% 2.39/0.99      | ~ v3_pre_topc(X0,X1)
% 2.39/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.39/0.99      | v2_struct_0(X1)
% 2.39/0.99      | ~ l1_pre_topc(X1)
% 2.39/0.99      | ~ v2_pre_topc(X1) ),
% 2.39/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_20,negated_conjecture,
% 2.39/0.99      ( v3_tex_2(sK2,sK1) ),
% 2.39/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_346,plain,
% 2.39/0.99      ( v1_tops_1(X0,X1)
% 2.39/0.99      | ~ v3_pre_topc(X0,X1)
% 2.39/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.39/0.99      | v2_struct_0(X1)
% 2.39/0.99      | ~ l1_pre_topc(X1)
% 2.39/0.99      | ~ v2_pre_topc(X1)
% 2.39/0.99      | sK1 != X1
% 2.39/0.99      | sK2 != X0 ),
% 2.39/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_20]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_347,plain,
% 2.39/0.99      ( v1_tops_1(sK2,sK1)
% 2.39/0.99      | ~ v3_pre_topc(sK2,sK1)
% 2.39/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.39/0.99      | v2_struct_0(sK1)
% 2.39/0.99      | ~ l1_pre_topc(sK1)
% 2.39/0.99      | ~ v2_pre_topc(sK1) ),
% 2.39/0.99      inference(unflattening,[status(thm)],[c_346]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_26,negated_conjecture,
% 2.39/0.99      ( ~ v2_struct_0(sK1) ),
% 2.39/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_349,plain,
% 2.39/0.99      ( v1_tops_1(sK2,sK1) | ~ v3_pre_topc(sK2,sK1) ),
% 2.39/0.99      inference(global_propositional_subsumption,
% 2.39/0.99                [status(thm)],
% 2.39/0.99                [c_347,c_26,c_25,c_23,c_22]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_364,plain,
% 2.39/0.99      ( ~ v3_pre_topc(sK2,sK1)
% 2.39/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.39/0.99      | ~ l1_pre_topc(X1)
% 2.39/0.99      | k2_pre_topc(X1,X0) = u1_struct_0(X1)
% 2.39/0.99      | sK1 != X1
% 2.39/0.99      | sK2 != X0 ),
% 2.39/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_349]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_365,plain,
% 2.39/0.99      ( ~ v3_pre_topc(sK2,sK1)
% 2.39/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.39/0.99      | ~ l1_pre_topc(sK1)
% 2.39/0.99      | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
% 2.39/0.99      inference(unflattening,[status(thm)],[c_364]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_367,plain,
% 2.39/0.99      ( ~ v3_pre_topc(sK2,sK1) | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
% 2.39/0.99      inference(global_propositional_subsumption,
% 2.39/0.99                [status(thm)],
% 2.39/0.99                [c_365,c_23,c_22]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_504,plain,
% 2.39/0.99      ( ~ v4_pre_topc(X0,sK1)
% 2.39/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.39/0.99      | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1)
% 2.39/0.99      | sK1 != sK1
% 2.39/0.99      | sK2 != X0 ),
% 2.39/0.99      inference(resolution_lifted,[status(thm)],[c_367,c_392]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_505,plain,
% 2.39/0.99      ( ~ v4_pre_topc(sK2,sK1)
% 2.39/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.39/0.99      | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
% 2.39/0.99      inference(unflattening,[status(thm)],[c_504]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_494,plain,
% 2.39/0.99      ( v4_pre_topc(sK2,sK1) | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
% 2.39/0.99      inference(resolution,[status(thm)],[c_21,c_367]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_507,plain,
% 2.39/0.99      ( k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
% 2.39/0.99      inference(global_propositional_subsumption,
% 2.39/0.99                [status(thm)],
% 2.39/0.99                [c_505,c_22,c_494]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_1055,plain,
% 2.39/0.99      ( u1_struct_0(sK1) = sK2 | v4_pre_topc(sK2,sK1) != iProver_top ),
% 2.39/0.99      inference(demodulation,[status(thm)],[c_1054,c_507]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_1179,plain,
% 2.39/0.99      ( u1_struct_0(sK1) = sK2 ),
% 2.39/0.99      inference(superposition,[status(thm)],[c_1174,c_1055]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_2,plain,
% 2.39/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.39/0.99      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 2.39/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_843,plain,
% 2.39/0.99      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 2.39/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.39/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_1316,plain,
% 2.39/0.99      ( k3_subset_1(u1_struct_0(sK1),sK2) = k4_xboole_0(u1_struct_0(sK1),sK2) ),
% 2.39/0.99      inference(superposition,[status(thm)],[c_839,c_843]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_1564,plain,
% 2.39/0.99      ( k3_subset_1(sK2,sK2) = k4_xboole_0(sK2,sK2) ),
% 2.39/0.99      inference(demodulation,[status(thm)],[c_1179,c_1316]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_5,plain,
% 2.39/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.39/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_840,plain,
% 2.39/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.39/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_841,plain,
% 2.39/0.99      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 2.39/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.39/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_1268,plain,
% 2.39/0.99      ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 2.39/0.99      inference(superposition,[status(thm)],[c_840,c_841]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_1315,plain,
% 2.39/0.99      ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 2.39/0.99      inference(superposition,[status(thm)],[c_840,c_843]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_1,plain,
% 2.39/0.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.39/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_1320,plain,
% 2.39/0.99      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 2.39/0.99      inference(light_normalisation,[status(thm)],[c_1315,c_1]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_1911,plain,
% 2.39/0.99      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 2.39/0.99      inference(light_normalisation,[status(thm)],[c_1268,c_1320]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_2014,plain,
% 2.39/0.99      ( k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
% 2.39/0.99      inference(demodulation,[status(thm)],[c_1564,c_1911]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_0,plain,
% 2.39/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.39/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_13,plain,
% 2.39/0.99      ( ~ v1_subset_1(X0,X1)
% 2.39/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.39/0.99      | v1_xboole_0(X1)
% 2.39/0.99      | ~ v1_xboole_0(k3_subset_1(X1,X0)) ),
% 2.39/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_6,plain,
% 2.39/0.99      ( ~ v1_subset_1(X0,X1)
% 2.39/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.39/0.99      | ~ v1_xboole_0(X1) ),
% 2.39/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_148,plain,
% 2.39/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.39/0.99      | ~ v1_subset_1(X0,X1)
% 2.39/0.99      | ~ v1_xboole_0(k3_subset_1(X1,X0)) ),
% 2.39/0.99      inference(global_propositional_subsumption,[status(thm)],[c_13,c_6]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_149,plain,
% 2.39/0.99      ( ~ v1_subset_1(X0,X1)
% 2.39/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.39/0.99      | ~ v1_xboole_0(k3_subset_1(X1,X0)) ),
% 2.39/0.99      inference(renaming,[status(thm)],[c_148]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_303,plain,
% 2.39/0.99      ( ~ v1_subset_1(X0,X1)
% 2.39/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.39/0.99      | k3_subset_1(X1,X0) != k1_xboole_0 ),
% 2.39/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_149]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_19,negated_conjecture,
% 2.39/0.99      ( v1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.39/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_324,plain,
% 2.39/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.39/0.99      | k3_subset_1(X1,X0) != k1_xboole_0
% 2.39/0.99      | u1_struct_0(sK1) != X1
% 2.39/0.99      | sK2 != X0 ),
% 2.39/0.99      inference(resolution_lifted,[status(thm)],[c_303,c_19]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_325,plain,
% 2.39/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.39/0.99      | k3_subset_1(u1_struct_0(sK1),sK2) != k1_xboole_0 ),
% 2.39/0.99      inference(unflattening,[status(thm)],[c_324]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_327,plain,
% 2.39/0.99      ( k3_subset_1(u1_struct_0(sK1),sK2) != k1_xboole_0 ),
% 2.39/0.99      inference(global_propositional_subsumption,[status(thm)],[c_325,c_22]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_1398,plain,
% 2.39/0.99      ( k4_xboole_0(u1_struct_0(sK1),sK2) != k1_xboole_0 ),
% 2.39/0.99      inference(demodulation,[status(thm)],[c_1316,c_327]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_1563,plain,
% 2.39/0.99      ( k4_xboole_0(sK2,sK2) != k1_xboole_0 ),
% 2.39/0.99      inference(demodulation,[status(thm)],[c_1179,c_1398]) ).
% 2.39/0.99  
% 2.39/0.99  cnf(c_2016,plain,
% 2.39/0.99      ( $false ),
% 2.39/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_2014,c_1563]) ).
% 2.39/0.99  
% 2.39/0.99  
% 2.39/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.39/0.99  
% 2.39/0.99  ------                               Statistics
% 2.39/0.99  
% 2.39/0.99  ------ General
% 2.39/0.99  
% 2.39/0.99  abstr_ref_over_cycles:                  0
% 2.39/0.99  abstr_ref_under_cycles:                 0
% 2.39/0.99  gc_basic_clause_elim:                   0
% 2.39/0.99  forced_gc_time:                         0
% 2.39/0.99  parsing_time:                           0.012
% 2.39/0.99  unif_index_cands_time:                  0.
% 2.39/0.99  unif_index_add_time:                    0.
% 2.39/0.99  orderings_time:                         0.
% 2.39/0.99  out_proof_time:                         0.013
% 2.39/0.99  total_time:                             0.101
% 2.39/0.99  num_of_symbols:                         51
% 2.39/0.99  num_of_terms:                           1609
% 2.39/0.99  
% 2.39/0.99  ------ Preprocessing
% 2.39/0.99  
% 2.39/0.99  num_of_splits:                          0
% 2.39/0.99  num_of_split_atoms:                     0
% 2.39/0.99  num_of_reused_defs:                     0
% 2.39/0.99  num_eq_ax_congr_red:                    8
% 2.39/0.99  num_of_sem_filtered_clauses:            1
% 2.39/0.99  num_of_subtypes:                        0
% 2.39/0.99  monotx_restored_types:                  0
% 2.39/0.99  sat_num_of_epr_types:                   0
% 2.39/0.99  sat_num_of_non_cyclic_types:            0
% 2.39/0.99  sat_guarded_non_collapsed_types:        0
% 2.39/0.99  num_pure_diseq_elim:                    0
% 2.39/0.99  simp_replaced_by:                       0
% 2.39/0.99  res_preprocessed:                       85
% 2.39/0.99  prep_upred:                             0
% 2.39/0.99  prep_unflattend:                        18
% 2.39/0.99  smt_new_axioms:                         0
% 2.39/0.99  pred_elim_cands:                        2
% 2.39/0.99  pred_elim:                              9
% 2.39/0.99  pred_elim_cl:                           14
% 2.39/0.99  pred_elim_cycles:                       11
% 2.39/0.99  merged_defs:                            0
% 2.39/0.99  merged_defs_ncl:                        0
% 2.39/0.99  bin_hyper_res:                          0
% 2.39/0.99  prep_cycles:                            4
% 2.39/0.99  pred_elim_time:                         0.006
% 2.39/0.99  splitting_time:                         0.
% 2.39/0.99  sem_filter_time:                        0.
% 2.39/0.99  monotx_time:                            0.
% 2.39/0.99  subtype_inf_time:                       0.
% 2.39/0.99  
% 2.39/0.99  ------ Problem properties
% 2.39/0.99  
% 2.39/0.99  clauses:                                13
% 2.39/0.99  conjectures:                            1
% 2.39/0.99  epr:                                    0
% 2.39/0.99  horn:                                   12
% 2.39/0.99  ground:                                 4
% 2.39/0.99  unary:                                  5
% 2.39/0.99  binary:                                 4
% 2.39/0.99  lits:                                   26
% 2.39/0.99  lits_eq:                                9
% 2.39/0.99  fd_pure:                                0
% 2.39/0.99  fd_pseudo:                              0
% 2.39/0.99  fd_cond:                                0
% 2.39/0.99  fd_pseudo_cond:                         0
% 2.39/0.99  ac_symbols:                             0
% 2.39/0.99  
% 2.39/0.99  ------ Propositional Solver
% 2.39/0.99  
% 2.39/0.99  prop_solver_calls:                      27
% 2.39/0.99  prop_fast_solver_calls:                 521
% 2.39/0.99  smt_solver_calls:                       0
% 2.39/0.99  smt_fast_solver_calls:                  0
% 2.39/0.99  prop_num_of_clauses:                    746
% 2.39/0.99  prop_preprocess_simplified:             2767
% 2.39/0.99  prop_fo_subsumed:                       17
% 2.39/0.99  prop_solver_time:                       0.
% 2.39/0.99  smt_solver_time:                        0.
% 2.39/0.99  smt_fast_solver_time:                   0.
% 2.39/0.99  prop_fast_solver_time:                  0.
% 2.39/0.99  prop_unsat_core_time:                   0.
% 2.39/0.99  
% 2.39/0.99  ------ QBF
% 2.39/0.99  
% 2.39/0.99  qbf_q_res:                              0
% 2.39/0.99  qbf_num_tautologies:                    0
% 2.39/0.99  qbf_prep_cycles:                        0
% 2.39/0.99  
% 2.39/0.99  ------ BMC1
% 2.39/0.99  
% 2.39/0.99  bmc1_current_bound:                     -1
% 2.39/0.99  bmc1_last_solved_bound:                 -1
% 2.39/0.99  bmc1_unsat_core_size:                   -1
% 2.39/0.99  bmc1_unsat_core_parents_size:           -1
% 2.39/0.99  bmc1_merge_next_fun:                    0
% 2.39/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.39/0.99  
% 2.39/0.99  ------ Instantiation
% 2.39/0.99  
% 2.39/0.99  inst_num_of_clauses:                    233
% 2.39/0.99  inst_num_in_passive:                    101
% 2.39/0.99  inst_num_in_active:                     124
% 2.39/0.99  inst_num_in_unprocessed:                8
% 2.39/0.99  inst_num_of_loops:                      140
% 2.39/0.99  inst_num_of_learning_restarts:          0
% 2.39/0.99  inst_num_moves_active_passive:          13
% 2.39/0.99  inst_lit_activity:                      0
% 2.39/0.99  inst_lit_activity_moves:                0
% 2.39/0.99  inst_num_tautologies:                   0
% 2.39/0.99  inst_num_prop_implied:                  0
% 2.39/0.99  inst_num_existing_simplified:           0
% 2.39/0.99  inst_num_eq_res_simplified:             0
% 2.39/0.99  inst_num_child_elim:                    0
% 2.39/0.99  inst_num_of_dismatching_blockings:      26
% 2.39/0.99  inst_num_of_non_proper_insts:           181
% 2.39/0.99  inst_num_of_duplicates:                 0
% 2.39/0.99  inst_inst_num_from_inst_to_res:         0
% 2.39/0.99  inst_dismatching_checking_time:         0.
% 2.39/0.99  
% 2.39/0.99  ------ Resolution
% 2.39/0.99  
% 2.39/0.99  res_num_of_clauses:                     0
% 2.39/0.99  res_num_in_passive:                     0
% 2.39/0.99  res_num_in_active:                      0
% 2.39/0.99  res_num_of_loops:                       89
% 2.39/0.99  res_forward_subset_subsumed:            12
% 2.39/0.99  res_backward_subset_subsumed:           0
% 2.39/0.99  res_forward_subsumed:                   0
% 2.39/0.99  res_backward_subsumed:                  1
% 2.39/0.99  res_forward_subsumption_resolution:     1
% 2.39/0.99  res_backward_subsumption_resolution:    0
% 2.39/0.99  res_clause_to_clause_subsumption:       40
% 2.39/0.99  res_orphan_elimination:                 0
% 2.39/0.99  res_tautology_del:                      19
% 2.39/0.99  res_num_eq_res_simplified:              1
% 2.39/0.99  res_num_sel_changes:                    0
% 2.39/0.99  res_moves_from_active_to_pass:          0
% 2.39/0.99  
% 2.39/0.99  ------ Superposition
% 2.39/0.99  
% 2.39/0.99  sup_time_total:                         0.
% 2.39/0.99  sup_time_generating:                    0.
% 2.39/0.99  sup_time_sim_full:                      0.
% 2.39/0.99  sup_time_sim_immed:                     0.
% 2.39/0.99  
% 2.39/0.99  sup_num_of_clauses:                     24
% 2.39/0.99  sup_num_in_active:                      14
% 2.39/0.99  sup_num_in_passive:                     10
% 2.39/0.99  sup_num_of_loops:                       26
% 2.39/0.99  sup_fw_superposition:                   7
% 2.39/0.99  sup_bw_superposition:                   9
% 2.39/0.99  sup_immediate_simplified:               5
% 2.39/0.99  sup_given_eliminated:                   0
% 2.39/0.99  comparisons_done:                       0
% 2.39/0.99  comparisons_avoided:                    0
% 2.39/0.99  
% 2.39/0.99  ------ Simplifications
% 2.39/0.99  
% 2.39/0.99  
% 2.39/0.99  sim_fw_subset_subsumed:                 3
% 2.39/0.99  sim_bw_subset_subsumed:                 1
% 2.39/0.99  sim_fw_subsumed:                        0
% 2.39/0.99  sim_bw_subsumed:                        0
% 2.39/0.99  sim_fw_subsumption_res:                 1
% 2.39/0.99  sim_bw_subsumption_res:                 0
% 2.39/0.99  sim_tautology_del:                      0
% 2.39/0.99  sim_eq_tautology_del:                   1
% 2.39/0.99  sim_eq_res_simp:                        1
% 2.39/0.99  sim_fw_demodulated:                     3
% 2.39/0.99  sim_bw_demodulated:                     11
% 2.39/0.99  sim_light_normalised:                   3
% 2.39/0.99  sim_joinable_taut:                      0
% 2.39/0.99  sim_joinable_simp:                      0
% 2.39/0.99  sim_ac_normalised:                      0
% 2.39/0.99  sim_smt_subsumption:                    0
% 2.39/0.99  
%------------------------------------------------------------------------------
