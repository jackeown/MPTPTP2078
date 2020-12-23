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
% DateTime   : Thu Dec  3 12:27:38 EST 2020

% Result     : Theorem 3.30s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 979 expanded)
%              Number of clauses        :  117 ( 324 expanded)
%              Number of leaves         :   23 ( 235 expanded)
%              Depth                    :   26
%              Number of atoms          :  604 (5573 expanded)
%              Number of equality atoms :  166 ( 318 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

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
    inference(ennf_transformation,[],[f18])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f43,plain,(
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

fof(f42,plain,
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

fof(f44,plain,
    ( v1_subset_1(sK2,u1_struct_0(sK1))
    & v3_tex_2(sK2,sK1)
    & ( v4_pre_topc(sK2,sK1)
      | v3_pre_topc(sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v3_tdlat_3(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f34,f43,f42])).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f73,plain,
    ( v4_pre_topc(sK2,sK1)
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f71,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK0(X0),X0)
        & v4_pre_topc(sK0(X0),X0)
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f63,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f70,plain,(
    v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f60,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,(
    v3_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X0))
        & v1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f75,plain,(
    v1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f76,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f45,f50,f50])).

fof(f5,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1420,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1421,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2568,plain,
    ( r1_tarski(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1420,c_1421])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_218,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_219,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_218])).

cnf(c_271,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_219])).

cnf(c_1419,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_271])).

cnf(c_4979,plain,
    ( k3_subset_1(u1_struct_0(sK1),sK2) = k4_xboole_0(u1_struct_0(sK1),sK2) ),
    inference(superposition,[status(thm)],[c_2568,c_1419])).

cnf(c_24,negated_conjecture,
    ( v3_pre_topc(sK2,sK1)
    | v4_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_12,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_744,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_26])).

cnf(c_745,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),X0),sK1)
    | v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_744])).

cnf(c_804,plain,
    ( v4_pre_topc(X0,sK1)
    | v4_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_subset_1(u1_struct_0(sK1),X0) != sK2
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_745])).

cnf(c_868,plain,
    ( v4_pre_topc(X0,sK1)
    | v4_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_subset_1(u1_struct_0(sK1),X0) != sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_804])).

cnf(c_1413,plain,
    ( k3_subset_1(u1_struct_0(sK1),X0) != sK2
    | v4_pre_topc(X0,sK1) = iProver_top
    | v4_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_868])).

cnf(c_6027,plain,
    ( k4_xboole_0(u1_struct_0(sK1),sK2) != sK2
    | v4_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4979,c_1413])).

cnf(c_34,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2128,plain,
    ( r1_tarski(k4_xboole_0(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2129,plain,
    ( r1_tarski(k4_xboole_0(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2128])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_272,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_219])).

cnf(c_1418,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_272])).

cnf(c_4719,plain,
    ( k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_2568,c_1418])).

cnf(c_1422,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_20,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_679,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_28])).

cnf(c_680,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_679])).

cnf(c_27,negated_conjecture,
    ( v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_684,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_680,c_27,c_26])).

cnf(c_825,plain,
    ( ~ v4_pre_topc(X0,sK1)
    | v4_pre_topc(X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_subset_1(u1_struct_0(sK1),X1) != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_684,c_745])).

cnf(c_826,plain,
    ( v4_pre_topc(X0,sK1)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK1),X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_825])).

cnf(c_1414,plain,
    ( v4_pre_topc(X0,sK1) = iProver_top
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),X0),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_826])).

cnf(c_2575,plain,
    ( v4_pre_topc(X0,sK1) = iProver_top
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),X0),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k3_subset_1(u1_struct_0(sK1),X0),u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1422,c_1414])).

cnf(c_4765,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK2)),sK1) != iProver_top
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4719,c_2575])).

cnf(c_4787,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) = iProver_top
    | v4_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4765,c_4719])).

cnf(c_1071,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_1079,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1071])).

cnf(c_1062,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1081,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1062])).

cnf(c_1534,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1629,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK1))
    | k3_subset_1(u1_struct_0(sK1),sK2) = k4_xboole_0(u1_struct_0(sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_271])).

cnf(c_1065,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1610,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k4_xboole_0(X2,X3),X2)
    | X1 != X2
    | X0 != k4_xboole_0(X2,X3) ),
    inference(instantiation,[status(thm)],[c_1065])).

cnf(c_1883,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK1),sK2),X0)
    | ~ r1_tarski(k4_xboole_0(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | X0 != u1_struct_0(sK1)
    | k3_subset_1(u1_struct_0(sK1),sK2) != k4_xboole_0(u1_struct_0(sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_1610])).

cnf(c_3473,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ r1_tarski(k4_xboole_0(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | k3_subset_1(u1_struct_0(sK1),sK2) != k4_xboole_0(u1_struct_0(sK1),sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1883])).

cnf(c_3474,plain,
    ( k3_subset_1(u1_struct_0(sK1),sK2) != k4_xboole_0(u1_struct_0(sK1),sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | r1_tarski(k3_subset_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
    | r1_tarski(k4_xboole_0(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3473])).

cnf(c_4320,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    | v4_pre_topc(sK2,sK1)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(sK2,u1_struct_0(sK1)) ),
    inference(resolution,[status(thm)],[c_272,c_868])).

cnf(c_1628,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK1))
    | k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_272])).

cnf(c_1706,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    | v4_pre_topc(sK2,sK1)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_868])).

cnf(c_4516,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_pre_topc(sK2,sK1)
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4320,c_25,c_1534,c_1628,c_1706])).

cnf(c_4517,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    | v4_pre_topc(sK2,sK1)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_4516])).

cnf(c_4766,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK2)),sK1) != iProver_top
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4719,c_1414])).

cnf(c_4778,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) = iProver_top
    | v4_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4766,c_4719])).

cnf(c_4793,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    | ~ v4_pre_topc(sK2,sK1)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4778])).

cnf(c_4796,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4517,c_25,c_4793])).

cnf(c_4812,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    | ~ r1_tarski(k3_subset_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
    inference(resolution,[status(thm)],[c_4796,c_8])).

cnf(c_4813,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) = iProver_top
    | r1_tarski(k3_subset_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4812])).

cnf(c_4970,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4787,c_25,c_1079,c_1081,c_1534,c_1629,c_2129,c_3474,c_4813])).

cnf(c_6015,plain,
    ( v4_pre_topc(k4_xboole_0(u1_struct_0(sK1),sK2),sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4979,c_4970])).

cnf(c_6025,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) != iProver_top
    | v4_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k4_xboole_0(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4979,c_2575])).

cnf(c_6047,plain,
    ( v4_pre_topc(k4_xboole_0(u1_struct_0(sK1),sK2),sK1) != iProver_top
    | v4_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k4_xboole_0(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6025,c_4979])).

cnf(c_6609,plain,
    ( v4_pre_topc(sK2,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6027,c_34,c_2129,c_6015,c_6047])).

cnf(c_11,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_759,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_26])).

cnf(c_760,plain,
    ( ~ v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_759])).

cnf(c_1415,plain,
    ( k2_pre_topc(sK1,X0) = X0
    | v4_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_760])).

cnf(c_1657,plain,
    ( k2_pre_topc(sK1,sK2) = sK2
    | v4_pre_topc(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1420,c_1415])).

cnf(c_15,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_21,plain,
    ( ~ v3_tex_2(X0,X1)
    | v1_tops_1(X0,X1)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_23,negated_conjecture,
    ( v3_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_446,plain,
    ( v1_tops_1(X0,X1)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_23])).

cnf(c_447,plain,
    ( v1_tops_1(sK2,sK1)
    | ~ v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_446])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_449,plain,
    ( v1_tops_1(sK2,sK1)
    | ~ v3_pre_topc(sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_447,c_29,c_28,c_26,c_25])).

cnf(c_464,plain,
    ( ~ v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1)
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_449])).

cnf(c_465,plain,
    ( ~ v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_464])).

cnf(c_467,plain,
    ( ~ v3_pre_topc(sK2,sK1)
    | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_465,c_26,c_25])).

cnf(c_796,plain,
    ( ~ v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1)
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_467,c_684])).

cnf(c_797,plain,
    ( ~ v4_pre_topc(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_796])).

cnf(c_786,plain,
    ( v4_pre_topc(sK2,sK1)
    | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_24,c_467])).

cnf(c_799,plain,
    ( k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_797,c_25,c_786])).

cnf(c_1658,plain,
    ( u1_struct_0(sK1) = sK2
    | v4_pre_topc(sK2,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1657,c_799])).

cnf(c_6614,plain,
    ( u1_struct_0(sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_6609,c_1658])).

cnf(c_216,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_217,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_216])).

cnf(c_1,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_16,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(k3_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_7,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_162,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X0,X1)
    | ~ v1_xboole_0(k3_subset_1(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_7])).

cnf(c_163,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(k3_subset_1(X1,X0)) ),
    inference(renaming,[status(thm)],[c_162])).

cnf(c_276,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(k3_subset_1(X1,X0)) ),
    inference(bin_hyper_res,[status(thm)],[c_163,c_219])).

cnf(c_399,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_276])).

cnf(c_22,negated_conjecture,
    ( v1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_420,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,X0) != k1_xboole_0
    | u1_struct_0(sK1) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_399,c_22])).

cnf(c_421,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK1))
    | k3_subset_1(u1_struct_0(sK1),sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_557,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(u1_struct_0(sK1),sK2) != k1_xboole_0
    | u1_struct_0(sK1) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_217,c_421])).

cnf(c_558,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_subset_1(u1_struct_0(sK1),sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_557])).

cnf(c_560,plain,
    ( k3_subset_1(u1_struct_0(sK1),sK2) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_558,c_25])).

cnf(c_6017,plain,
    ( k4_xboole_0(u1_struct_0(sK1),sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4979,c_560])).

cnf(c_6618,plain,
    ( k4_xboole_0(sK2,sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6614,c_6017])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1914,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_1424,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2141,plain,
    ( r1_tarski(k4_xboole_0(X0,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1914,c_1424])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1423,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2341,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2141,c_1423])).

cnf(c_6705,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6618,c_2341])).

cnf(c_6706,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_6705])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 16:25:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.30/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.00  
% 3.30/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.30/1.00  
% 3.30/1.00  ------  iProver source info
% 3.30/1.00  
% 3.30/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.30/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.30/1.00  git: non_committed_changes: false
% 3.30/1.00  git: last_make_outside_of_git: false
% 3.30/1.00  
% 3.30/1.00  ------ 
% 3.30/1.00  ------ Parsing...
% 3.30/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.30/1.00  
% 3.30/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 3.30/1.00  
% 3.30/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.30/1.00  
% 3.30/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.30/1.00  ------ Proving...
% 3.30/1.00  ------ Problem Properties 
% 3.30/1.00  
% 3.30/1.00  
% 3.30/1.00  clauses                                 16
% 3.30/1.00  conjectures                             1
% 3.30/1.00  EPR                                     1
% 3.30/1.00  Horn                                    15
% 3.30/1.00  unary                                   6
% 3.30/1.00  binary                                  6
% 3.30/1.00  lits                                    32
% 3.30/1.00  lits eq                                 11
% 3.30/1.00  fd_pure                                 0
% 3.30/1.00  fd_pseudo                               0
% 3.30/1.00  fd_cond                                 1
% 3.30/1.00  fd_pseudo_cond                          0
% 3.30/1.00  AC symbols                              0
% 3.30/1.00  
% 3.30/1.00  ------ Input Options Time Limit: Unbounded
% 3.30/1.00  
% 3.30/1.00  
% 3.30/1.00  ------ 
% 3.30/1.00  Current options:
% 3.30/1.00  ------ 
% 3.30/1.00  
% 3.30/1.00  
% 3.30/1.00  
% 3.30/1.00  
% 3.30/1.00  ------ Proving...
% 3.30/1.00  
% 3.30/1.00  
% 3.30/1.00  % SZS status Theorem for theBenchmark.p
% 3.30/1.00  
% 3.30/1.00   Resolution empty clause
% 3.30/1.00  
% 3.30/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.30/1.00  
% 3.30/1.00  fof(f17,conjecture,(
% 3.30/1.00    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)))))),
% 3.30/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f18,negated_conjecture,(
% 3.30/1.00    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)))))),
% 3.30/1.00    inference(negated_conjecture,[],[f17])).
% 3.30/1.00  
% 3.30/1.00  fof(f33,plain,(
% 3.30/1.00    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.30/1.00    inference(ennf_transformation,[],[f18])).
% 3.30/1.00  
% 3.30/1.00  fof(f34,plain,(
% 3.30/1.00    ? [X0] : (? [X1] : (v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.30/1.00    inference(flattening,[],[f33])).
% 3.30/1.00  
% 3.30/1.00  fof(f43,plain,(
% 3.30/1.00    ( ! [X0] : (? [X1] : (v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v1_subset_1(sK2,u1_struct_0(X0)) & v3_tex_2(sK2,X0) & (v4_pre_topc(sK2,X0) | v3_pre_topc(sK2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.30/1.00    introduced(choice_axiom,[])).
% 3.30/1.00  
% 3.30/1.00  fof(f42,plain,(
% 3.30/1.00    ? [X0] : (? [X1] : (v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (v1_subset_1(X1,u1_struct_0(sK1)) & v3_tex_2(X1,sK1) & (v4_pre_topc(X1,sK1) | v3_pre_topc(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v3_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 3.30/1.00    introduced(choice_axiom,[])).
% 3.30/1.00  
% 3.30/1.00  fof(f44,plain,(
% 3.30/1.00    (v1_subset_1(sK2,u1_struct_0(sK1)) & v3_tex_2(sK2,sK1) & (v4_pre_topc(sK2,sK1) | v3_pre_topc(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v3_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 3.30/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f34,f43,f42])).
% 3.30/1.00  
% 3.30/1.00  fof(f72,plain,(
% 3.30/1.00    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 3.30/1.00    inference(cnf_transformation,[],[f44])).
% 3.30/1.00  
% 3.30/1.00  fof(f10,axiom,(
% 3.30/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.30/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f35,plain,(
% 3.30/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.30/1.00    inference(nnf_transformation,[],[f10])).
% 3.30/1.00  
% 3.30/1.00  fof(f54,plain,(
% 3.30/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.30/1.00    inference(cnf_transformation,[],[f35])).
% 3.30/1.00  
% 3.30/1.00  fof(f7,axiom,(
% 3.30/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.30/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f20,plain,(
% 3.30/1.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.30/1.00    inference(ennf_transformation,[],[f7])).
% 3.30/1.00  
% 3.30/1.00  fof(f51,plain,(
% 3.30/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.30/1.00    inference(cnf_transformation,[],[f20])).
% 3.30/1.00  
% 3.30/1.00  fof(f55,plain,(
% 3.30/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f35])).
% 3.30/1.00  
% 3.30/1.00  fof(f73,plain,(
% 3.30/1.00    v4_pre_topc(sK2,sK1) | v3_pre_topc(sK2,sK1)),
% 3.30/1.00    inference(cnf_transformation,[],[f44])).
% 3.30/1.00  
% 3.30/1.00  fof(f12,axiom,(
% 3.30/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 3.30/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f25,plain,(
% 3.30/1.00    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.30/1.00    inference(ennf_transformation,[],[f12])).
% 3.30/1.00  
% 3.30/1.00  fof(f36,plain,(
% 3.30/1.00    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.30/1.00    inference(nnf_transformation,[],[f25])).
% 3.30/1.00  
% 3.30/1.00  fof(f59,plain,(
% 3.30/1.00    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f36])).
% 3.30/1.00  
% 3.30/1.00  fof(f71,plain,(
% 3.30/1.00    l1_pre_topc(sK1)),
% 3.30/1.00    inference(cnf_transformation,[],[f44])).
% 3.30/1.00  
% 3.30/1.00  fof(f3,axiom,(
% 3.30/1.00    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.30/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f47,plain,(
% 3.30/1.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f3])).
% 3.30/1.00  
% 3.30/1.00  fof(f8,axiom,(
% 3.30/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.30/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f21,plain,(
% 3.30/1.00    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.30/1.00    inference(ennf_transformation,[],[f8])).
% 3.30/1.00  
% 3.30/1.00  fof(f52,plain,(
% 3.30/1.00    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.30/1.00    inference(cnf_transformation,[],[f21])).
% 3.30/1.00  
% 3.30/1.00  fof(f15,axiom,(
% 3.30/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 3.30/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f29,plain,(
% 3.30/1.00    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.30/1.00    inference(ennf_transformation,[],[f15])).
% 3.30/1.00  
% 3.30/1.00  fof(f30,plain,(
% 3.30/1.00    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.30/1.00    inference(flattening,[],[f29])).
% 3.30/1.00  
% 3.30/1.00  fof(f38,plain,(
% 3.30/1.00    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.30/1.00    inference(nnf_transformation,[],[f30])).
% 3.30/1.00  
% 3.30/1.00  fof(f39,plain,(
% 3.30/1.00    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.30/1.00    inference(rectify,[],[f38])).
% 3.30/1.00  
% 3.30/1.00  fof(f40,plain,(
% 3.30/1.00    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK0(X0),X0) & v4_pre_topc(sK0(X0),X0) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.30/1.00    introduced(choice_axiom,[])).
% 3.30/1.00  
% 3.30/1.00  fof(f41,plain,(
% 3.30/1.00    ! [X0] : (((v3_tdlat_3(X0) | (~v3_pre_topc(sK0(X0),X0) & v4_pre_topc(sK0(X0),X0) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.30/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).
% 3.30/1.00  
% 3.30/1.00  fof(f63,plain,(
% 3.30/1.00    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f41])).
% 3.30/1.00  
% 3.30/1.00  fof(f69,plain,(
% 3.30/1.00    v2_pre_topc(sK1)),
% 3.30/1.00    inference(cnf_transformation,[],[f44])).
% 3.30/1.00  
% 3.30/1.00  fof(f70,plain,(
% 3.30/1.00    v3_tdlat_3(sK1)),
% 3.30/1.00    inference(cnf_transformation,[],[f44])).
% 3.30/1.00  
% 3.30/1.00  fof(f11,axiom,(
% 3.30/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.30/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f23,plain,(
% 3.30/1.00    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.30/1.00    inference(ennf_transformation,[],[f11])).
% 3.30/1.00  
% 3.30/1.00  fof(f24,plain,(
% 3.30/1.00    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.30/1.00    inference(flattening,[],[f23])).
% 3.30/1.00  
% 3.30/1.00  fof(f56,plain,(
% 3.30/1.00    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f24])).
% 3.30/1.00  
% 3.30/1.00  fof(f13,axiom,(
% 3.30/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 3.30/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f26,plain,(
% 3.30/1.00    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.30/1.00    inference(ennf_transformation,[],[f13])).
% 3.30/1.00  
% 3.30/1.00  fof(f37,plain,(
% 3.30/1.00    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.30/1.00    inference(nnf_transformation,[],[f26])).
% 3.30/1.00  
% 3.30/1.00  fof(f60,plain,(
% 3.30/1.00    ( ! [X0,X1] : (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f37])).
% 3.30/1.00  
% 3.30/1.00  fof(f16,axiom,(
% 3.30/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 3.30/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f31,plain,(
% 3.30/1.00    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.30/1.00    inference(ennf_transformation,[],[f16])).
% 3.30/1.00  
% 3.30/1.00  fof(f32,plain,(
% 3.30/1.00    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.30/1.00    inference(flattening,[],[f31])).
% 3.30/1.00  
% 3.30/1.00  fof(f67,plain,(
% 3.30/1.00    ( ! [X0,X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f32])).
% 3.30/1.00  
% 3.30/1.00  fof(f74,plain,(
% 3.30/1.00    v3_tex_2(sK2,sK1)),
% 3.30/1.00    inference(cnf_transformation,[],[f44])).
% 3.30/1.00  
% 3.30/1.00  fof(f68,plain,(
% 3.30/1.00    ~v2_struct_0(sK1)),
% 3.30/1.00    inference(cnf_transformation,[],[f44])).
% 3.30/1.00  
% 3.30/1.00  fof(f2,axiom,(
% 3.30/1.00    v1_xboole_0(k1_xboole_0)),
% 3.30/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f46,plain,(
% 3.30/1.00    v1_xboole_0(k1_xboole_0)),
% 3.30/1.00    inference(cnf_transformation,[],[f2])).
% 3.30/1.00  
% 3.30/1.00  fof(f14,axiom,(
% 3.30/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(X0)) & v1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k3_subset_1(X0,X1)))),
% 3.30/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f27,plain,(
% 3.30/1.00    ! [X0,X1] : (~v1_xboole_0(k3_subset_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.30/1.00    inference(ennf_transformation,[],[f14])).
% 3.30/1.00  
% 3.30/1.00  fof(f28,plain,(
% 3.30/1.00    ! [X0,X1] : (~v1_xboole_0(k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.30/1.00    inference(flattening,[],[f27])).
% 3.30/1.00  
% 3.30/1.00  fof(f62,plain,(
% 3.30/1.00    ( ! [X0,X1] : (~v1_xboole_0(k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f28])).
% 3.30/1.00  
% 3.30/1.00  fof(f9,axiom,(
% 3.30/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~v1_subset_1(X1,X0)))),
% 3.30/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f22,plain,(
% 3.30/1.00    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.30/1.00    inference(ennf_transformation,[],[f9])).
% 3.30/1.00  
% 3.30/1.00  fof(f53,plain,(
% 3.30/1.00    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f22])).
% 3.30/1.00  
% 3.30/1.00  fof(f75,plain,(
% 3.30/1.00    v1_subset_1(sK2,u1_struct_0(sK1))),
% 3.30/1.00    inference(cnf_transformation,[],[f44])).
% 3.30/1.00  
% 3.30/1.00  fof(f4,axiom,(
% 3.30/1.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.30/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f48,plain,(
% 3.30/1.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.30/1.00    inference(cnf_transformation,[],[f4])).
% 3.30/1.00  
% 3.30/1.00  fof(f1,axiom,(
% 3.30/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.30/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f45,plain,(
% 3.30/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f1])).
% 3.30/1.00  
% 3.30/1.00  fof(f6,axiom,(
% 3.30/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.30/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f50,plain,(
% 3.30/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.30/1.00    inference(cnf_transformation,[],[f6])).
% 3.30/1.00  
% 3.30/1.00  fof(f76,plain,(
% 3.30/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.30/1.00    inference(definition_unfolding,[],[f45,f50,f50])).
% 3.30/1.00  
% 3.30/1.00  fof(f5,axiom,(
% 3.30/1.00    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 3.30/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f19,plain,(
% 3.30/1.00    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 3.30/1.00    inference(ennf_transformation,[],[f5])).
% 3.30/1.00  
% 3.30/1.00  fof(f49,plain,(
% 3.30/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f19])).
% 3.30/1.00  
% 3.30/1.00  cnf(c_25,negated_conjecture,
% 3.30/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.30/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1420,plain,
% 3.30/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_9,plain,
% 3.30/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.30/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1421,plain,
% 3.30/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.30/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2568,plain,
% 3.30/1.00      ( r1_tarski(sK2,u1_struct_0(sK1)) = iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_1420,c_1421]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_5,plain,
% 3.30/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.30/1.00      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 3.30/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8,plain,
% 3.30/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.30/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_218,plain,
% 3.30/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.30/1.00      inference(prop_impl,[status(thm)],[c_8]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_219,plain,
% 3.30/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.30/1.00      inference(renaming,[status(thm)],[c_218]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_271,plain,
% 3.30/1.00      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 3.30/1.00      inference(bin_hyper_res,[status(thm)],[c_5,c_219]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1419,plain,
% 3.30/1.00      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 3.30/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_271]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_4979,plain,
% 3.30/1.00      ( k3_subset_1(u1_struct_0(sK1),sK2) = k4_xboole_0(u1_struct_0(sK1),sK2) ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_2568,c_1419]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_24,negated_conjecture,
% 3.30/1.00      ( v3_pre_topc(sK2,sK1) | v4_pre_topc(sK2,sK1) ),
% 3.30/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_12,plain,
% 3.30/1.00      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 3.30/1.00      | v4_pre_topc(X1,X0)
% 3.30/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.30/1.00      | ~ l1_pre_topc(X0) ),
% 3.30/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_26,negated_conjecture,
% 3.30/1.00      ( l1_pre_topc(sK1) ),
% 3.30/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_744,plain,
% 3.30/1.00      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 3.30/1.00      | v4_pre_topc(X1,X0)
% 3.30/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.30/1.00      | sK1 != X0 ),
% 3.30/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_26]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_745,plain,
% 3.30/1.00      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),X0),sK1)
% 3.30/1.00      | v4_pre_topc(X0,sK1)
% 3.30/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.30/1.00      inference(unflattening,[status(thm)],[c_744]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_804,plain,
% 3.30/1.00      ( v4_pre_topc(X0,sK1)
% 3.30/1.00      | v4_pre_topc(sK2,sK1)
% 3.30/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.30/1.00      | k3_subset_1(u1_struct_0(sK1),X0) != sK2
% 3.30/1.00      | sK1 != sK1 ),
% 3.30/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_745]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_868,plain,
% 3.30/1.00      ( v4_pre_topc(X0,sK1)
% 3.30/1.00      | v4_pre_topc(sK2,sK1)
% 3.30/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.30/1.00      | k3_subset_1(u1_struct_0(sK1),X0) != sK2 ),
% 3.30/1.00      inference(equality_resolution_simp,[status(thm)],[c_804]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1413,plain,
% 3.30/1.00      ( k3_subset_1(u1_struct_0(sK1),X0) != sK2
% 3.30/1.00      | v4_pre_topc(X0,sK1) = iProver_top
% 3.30/1.00      | v4_pre_topc(sK2,sK1) = iProver_top
% 3.30/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_868]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_6027,plain,
% 3.30/1.00      ( k4_xboole_0(u1_struct_0(sK1),sK2) != sK2
% 3.30/1.00      | v4_pre_topc(sK2,sK1) = iProver_top
% 3.30/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_4979,c_1413]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_34,plain,
% 3.30/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2,plain,
% 3.30/1.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 3.30/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2128,plain,
% 3.30/1.00      ( r1_tarski(k4_xboole_0(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2129,plain,
% 3.30/1.00      ( r1_tarski(k4_xboole_0(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_2128]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_6,plain,
% 3.30/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.30/1.00      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.30/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_272,plain,
% 3.30/1.00      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.30/1.00      inference(bin_hyper_res,[status(thm)],[c_6,c_219]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1418,plain,
% 3.30/1.00      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 3.30/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_272]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_4719,plain,
% 3.30/1.00      ( k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK2)) = sK2 ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_2568,c_1418]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1422,plain,
% 3.30/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.30/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_20,plain,
% 3.30/1.00      ( v3_pre_topc(X0,X1)
% 3.30/1.00      | ~ v4_pre_topc(X0,X1)
% 3.30/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/1.00      | ~ v3_tdlat_3(X1)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X1) ),
% 3.30/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_28,negated_conjecture,
% 3.30/1.00      ( v2_pre_topc(sK1) ),
% 3.30/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_679,plain,
% 3.30/1.00      ( v3_pre_topc(X0,X1)
% 3.30/1.00      | ~ v4_pre_topc(X0,X1)
% 3.30/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/1.00      | ~ v3_tdlat_3(X1)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | sK1 != X1 ),
% 3.30/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_28]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_680,plain,
% 3.30/1.00      ( v3_pre_topc(X0,sK1)
% 3.30/1.00      | ~ v4_pre_topc(X0,sK1)
% 3.30/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.30/1.00      | ~ v3_tdlat_3(sK1)
% 3.30/1.00      | ~ l1_pre_topc(sK1) ),
% 3.30/1.00      inference(unflattening,[status(thm)],[c_679]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_27,negated_conjecture,
% 3.30/1.00      ( v3_tdlat_3(sK1) ),
% 3.30/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_684,plain,
% 3.30/1.00      ( v3_pre_topc(X0,sK1)
% 3.30/1.00      | ~ v4_pre_topc(X0,sK1)
% 3.30/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_680,c_27,c_26]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_825,plain,
% 3.30/1.00      ( ~ v4_pre_topc(X0,sK1)
% 3.30/1.00      | v4_pre_topc(X1,sK1)
% 3.30/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.30/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.30/1.00      | k3_subset_1(u1_struct_0(sK1),X1) != X0
% 3.30/1.00      | sK1 != sK1 ),
% 3.30/1.00      inference(resolution_lifted,[status(thm)],[c_684,c_745]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_826,plain,
% 3.30/1.00      ( v4_pre_topc(X0,sK1)
% 3.30/1.00      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK1),X0),sK1)
% 3.30/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.30/1.00      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.30/1.00      inference(unflattening,[status(thm)],[c_825]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1414,plain,
% 3.30/1.00      ( v4_pre_topc(X0,sK1) = iProver_top
% 3.30/1.00      | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),X0),sK1) != iProver_top
% 3.30/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.30/1.00      | m1_subset_1(k3_subset_1(u1_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_826]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2575,plain,
% 3.30/1.00      ( v4_pre_topc(X0,sK1) = iProver_top
% 3.30/1.00      | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),X0),sK1) != iProver_top
% 3.30/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.30/1.00      | r1_tarski(k3_subset_1(u1_struct_0(sK1),X0),u1_struct_0(sK1)) != iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_1422,c_1414]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_4765,plain,
% 3.30/1.00      ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK2)),sK1) != iProver_top
% 3.30/1.00      | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) = iProver_top
% 3.30/1.00      | m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.30/1.00      | r1_tarski(sK2,u1_struct_0(sK1)) != iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_4719,c_2575]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_4787,plain,
% 3.30/1.00      ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) = iProver_top
% 3.30/1.00      | v4_pre_topc(sK2,sK1) != iProver_top
% 3.30/1.00      | m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.30/1.00      | r1_tarski(sK2,u1_struct_0(sK1)) != iProver_top ),
% 3.30/1.00      inference(light_normalisation,[status(thm)],[c_4765,c_4719]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1071,plain,
% 3.30/1.00      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 3.30/1.00      theory(equality) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1079,plain,
% 3.30/1.00      ( u1_struct_0(sK1) = u1_struct_0(sK1) | sK1 != sK1 ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_1071]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1062,plain,( X0 = X0 ),theory(equality) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1081,plain,
% 3.30/1.00      ( sK1 = sK1 ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_1062]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1534,plain,
% 3.30/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.30/1.00      | r1_tarski(sK2,u1_struct_0(sK1)) ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1629,plain,
% 3.30/1.00      ( ~ r1_tarski(sK2,u1_struct_0(sK1))
% 3.30/1.00      | k3_subset_1(u1_struct_0(sK1),sK2) = k4_xboole_0(u1_struct_0(sK1),sK2) ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_271]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1065,plain,
% 3.30/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.30/1.00      theory(equality) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1610,plain,
% 3.30/1.00      ( r1_tarski(X0,X1)
% 3.30/1.00      | ~ r1_tarski(k4_xboole_0(X2,X3),X2)
% 3.30/1.00      | X1 != X2
% 3.30/1.00      | X0 != k4_xboole_0(X2,X3) ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_1065]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1883,plain,
% 3.30/1.00      ( r1_tarski(k3_subset_1(u1_struct_0(sK1),sK2),X0)
% 3.30/1.00      | ~ r1_tarski(k4_xboole_0(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 3.30/1.00      | X0 != u1_struct_0(sK1)
% 3.30/1.00      | k3_subset_1(u1_struct_0(sK1),sK2) != k4_xboole_0(u1_struct_0(sK1),sK2) ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_1610]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_3473,plain,
% 3.30/1.00      ( r1_tarski(k3_subset_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 3.30/1.00      | ~ r1_tarski(k4_xboole_0(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 3.30/1.00      | k3_subset_1(u1_struct_0(sK1),sK2) != k4_xboole_0(u1_struct_0(sK1),sK2)
% 3.30/1.00      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_1883]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_3474,plain,
% 3.30/1.00      ( k3_subset_1(u1_struct_0(sK1),sK2) != k4_xboole_0(u1_struct_0(sK1),sK2)
% 3.30/1.00      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 3.30/1.00      | r1_tarski(k3_subset_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
% 3.30/1.00      | r1_tarski(k4_xboole_0(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_3473]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_4320,plain,
% 3.30/1.00      ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
% 3.30/1.00      | v4_pre_topc(sK2,sK1)
% 3.30/1.00      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.30/1.00      | ~ r1_tarski(sK2,u1_struct_0(sK1)) ),
% 3.30/1.00      inference(resolution,[status(thm)],[c_272,c_868]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1628,plain,
% 3.30/1.00      ( ~ r1_tarski(sK2,u1_struct_0(sK1))
% 3.30/1.00      | k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK2)) = sK2 ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_272]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1706,plain,
% 3.30/1.00      ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
% 3.30/1.00      | v4_pre_topc(sK2,sK1)
% 3.30/1.00      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.30/1.00      | k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK2)) != sK2 ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_868]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_4516,plain,
% 3.30/1.00      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.30/1.00      | v4_pre_topc(sK2,sK1)
% 3.30/1.00      | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_4320,c_25,c_1534,c_1628,c_1706]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_4517,plain,
% 3.30/1.00      ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
% 3.30/1.00      | v4_pre_topc(sK2,sK1)
% 3.30/1.00      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.30/1.00      inference(renaming,[status(thm)],[c_4516]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_4766,plain,
% 3.30/1.00      ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK2)),sK1) != iProver_top
% 3.30/1.00      | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) = iProver_top
% 3.30/1.00      | m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.30/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_4719,c_1414]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_4778,plain,
% 3.30/1.00      ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) = iProver_top
% 3.30/1.00      | v4_pre_topc(sK2,sK1) != iProver_top
% 3.30/1.00      | m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.30/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.30/1.00      inference(light_normalisation,[status(thm)],[c_4766,c_4719]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_4793,plain,
% 3.30/1.00      ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
% 3.30/1.00      | ~ v4_pre_topc(sK2,sK1)
% 3.30/1.00      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.30/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.30/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_4778]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_4796,plain,
% 3.30/1.00      ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
% 3.30/1.00      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_4517,c_25,c_4793]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_4812,plain,
% 3.30/1.00      ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
% 3.30/1.00      | ~ r1_tarski(k3_subset_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
% 3.30/1.00      inference(resolution,[status(thm)],[c_4796,c_8]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_4813,plain,
% 3.30/1.00      ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) = iProver_top
% 3.30/1.00      | r1_tarski(k3_subset_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_4812]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_4970,plain,
% 3.30/1.00      ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) = iProver_top ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_4787,c_25,c_1079,c_1081,c_1534,c_1629,c_2129,c_3474,c_4813]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_6015,plain,
% 3.30/1.00      ( v4_pre_topc(k4_xboole_0(u1_struct_0(sK1),sK2),sK1) = iProver_top ),
% 3.30/1.00      inference(demodulation,[status(thm)],[c_4979,c_4970]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_6025,plain,
% 3.30/1.00      ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) != iProver_top
% 3.30/1.00      | v4_pre_topc(sK2,sK1) = iProver_top
% 3.30/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.30/1.00      | r1_tarski(k4_xboole_0(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_4979,c_2575]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_6047,plain,
% 3.30/1.00      ( v4_pre_topc(k4_xboole_0(u1_struct_0(sK1),sK2),sK1) != iProver_top
% 3.30/1.00      | v4_pre_topc(sK2,sK1) = iProver_top
% 3.30/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.30/1.00      | r1_tarski(k4_xboole_0(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top ),
% 3.30/1.00      inference(light_normalisation,[status(thm)],[c_6025,c_4979]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_6609,plain,
% 3.30/1.00      ( v4_pre_topc(sK2,sK1) = iProver_top ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_6027,c_34,c_2129,c_6015,c_6047]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_11,plain,
% 3.30/1.00      ( ~ v4_pre_topc(X0,X1)
% 3.30/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | k2_pre_topc(X1,X0) = X0 ),
% 3.30/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_759,plain,
% 3.30/1.00      ( ~ v4_pre_topc(X0,X1)
% 3.30/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/1.00      | k2_pre_topc(X1,X0) = X0
% 3.30/1.00      | sK1 != X1 ),
% 3.30/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_26]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_760,plain,
% 3.30/1.00      ( ~ v4_pre_topc(X0,sK1)
% 3.30/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.30/1.00      | k2_pre_topc(sK1,X0) = X0 ),
% 3.30/1.00      inference(unflattening,[status(thm)],[c_759]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1415,plain,
% 3.30/1.00      ( k2_pre_topc(sK1,X0) = X0
% 3.30/1.00      | v4_pre_topc(X0,sK1) != iProver_top
% 3.30/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_760]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1657,plain,
% 3.30/1.00      ( k2_pre_topc(sK1,sK2) = sK2 | v4_pre_topc(sK2,sK1) != iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_1420,c_1415]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_15,plain,
% 3.30/1.00      ( ~ v1_tops_1(X0,X1)
% 3.30/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
% 3.30/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_21,plain,
% 3.30/1.00      ( ~ v3_tex_2(X0,X1)
% 3.30/1.00      | v1_tops_1(X0,X1)
% 3.30/1.00      | ~ v3_pre_topc(X0,X1)
% 3.30/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X1) ),
% 3.30/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_23,negated_conjecture,
% 3.30/1.00      ( v3_tex_2(sK2,sK1) ),
% 3.30/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_446,plain,
% 3.30/1.00      ( v1_tops_1(X0,X1)
% 3.30/1.00      | ~ v3_pre_topc(X0,X1)
% 3.30/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/1.00      | v2_struct_0(X1)
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | ~ v2_pre_topc(X1)
% 3.30/1.00      | sK1 != X1
% 3.30/1.00      | sK2 != X0 ),
% 3.30/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_23]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_447,plain,
% 3.30/1.00      ( v1_tops_1(sK2,sK1)
% 3.30/1.00      | ~ v3_pre_topc(sK2,sK1)
% 3.30/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.30/1.00      | v2_struct_0(sK1)
% 3.30/1.00      | ~ l1_pre_topc(sK1)
% 3.30/1.00      | ~ v2_pre_topc(sK1) ),
% 3.30/1.00      inference(unflattening,[status(thm)],[c_446]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_29,negated_conjecture,
% 3.30/1.00      ( ~ v2_struct_0(sK1) ),
% 3.30/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_449,plain,
% 3.30/1.00      ( v1_tops_1(sK2,sK1) | ~ v3_pre_topc(sK2,sK1) ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_447,c_29,c_28,c_26,c_25]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_464,plain,
% 3.30/1.00      ( ~ v3_pre_topc(sK2,sK1)
% 3.30/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/1.00      | ~ l1_pre_topc(X1)
% 3.30/1.00      | k2_pre_topc(X1,X0) = u1_struct_0(X1)
% 3.30/1.00      | sK1 != X1
% 3.30/1.00      | sK2 != X0 ),
% 3.30/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_449]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_465,plain,
% 3.30/1.00      ( ~ v3_pre_topc(sK2,sK1)
% 3.30/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.30/1.00      | ~ l1_pre_topc(sK1)
% 3.30/1.00      | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
% 3.30/1.00      inference(unflattening,[status(thm)],[c_464]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_467,plain,
% 3.30/1.00      ( ~ v3_pre_topc(sK2,sK1) | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_465,c_26,c_25]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_796,plain,
% 3.30/1.00      ( ~ v4_pre_topc(X0,sK1)
% 3.30/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.30/1.00      | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1)
% 3.30/1.00      | sK1 != sK1
% 3.30/1.00      | sK2 != X0 ),
% 3.30/1.00      inference(resolution_lifted,[status(thm)],[c_467,c_684]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_797,plain,
% 3.30/1.00      ( ~ v4_pre_topc(sK2,sK1)
% 3.30/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.30/1.00      | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
% 3.30/1.00      inference(unflattening,[status(thm)],[c_796]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_786,plain,
% 3.30/1.00      ( v4_pre_topc(sK2,sK1) | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
% 3.30/1.00      inference(resolution,[status(thm)],[c_24,c_467]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_799,plain,
% 3.30/1.00      ( k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_797,c_25,c_786]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1658,plain,
% 3.30/1.00      ( u1_struct_0(sK1) = sK2 | v4_pre_topc(sK2,sK1) != iProver_top ),
% 3.30/1.00      inference(demodulation,[status(thm)],[c_1657,c_799]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_6614,plain,
% 3.30/1.00      ( u1_struct_0(sK1) = sK2 ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_6609,c_1658]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_216,plain,
% 3.30/1.00      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.30/1.00      inference(prop_impl,[status(thm)],[c_9]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_217,plain,
% 3.30/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.30/1.00      inference(renaming,[status(thm)],[c_216]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1,plain,
% 3.30/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.30/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_16,plain,
% 3.30/1.00      ( ~ v1_subset_1(X0,X1)
% 3.30/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.30/1.00      | v1_xboole_0(X1)
% 3.30/1.00      | ~ v1_xboole_0(k3_subset_1(X1,X0)) ),
% 3.30/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_7,plain,
% 3.30/1.00      ( ~ v1_subset_1(X0,X1)
% 3.30/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.30/1.00      | ~ v1_xboole_0(X1) ),
% 3.30/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_162,plain,
% 3.30/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.30/1.00      | ~ v1_subset_1(X0,X1)
% 3.30/1.00      | ~ v1_xboole_0(k3_subset_1(X1,X0)) ),
% 3.30/1.00      inference(global_propositional_subsumption,[status(thm)],[c_16,c_7]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_163,plain,
% 3.30/1.00      ( ~ v1_subset_1(X0,X1)
% 3.30/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.30/1.00      | ~ v1_xboole_0(k3_subset_1(X1,X0)) ),
% 3.30/1.00      inference(renaming,[status(thm)],[c_162]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_276,plain,
% 3.30/1.00      ( ~ v1_subset_1(X0,X1)
% 3.30/1.00      | ~ r1_tarski(X0,X1)
% 3.30/1.00      | ~ v1_xboole_0(k3_subset_1(X1,X0)) ),
% 3.30/1.00      inference(bin_hyper_res,[status(thm)],[c_163,c_219]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_399,plain,
% 3.30/1.00      ( ~ v1_subset_1(X0,X1)
% 3.30/1.00      | ~ r1_tarski(X0,X1)
% 3.30/1.00      | k3_subset_1(X1,X0) != k1_xboole_0 ),
% 3.30/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_276]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_22,negated_conjecture,
% 3.30/1.00      ( v1_subset_1(sK2,u1_struct_0(sK1)) ),
% 3.30/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_420,plain,
% 3.30/1.00      ( ~ r1_tarski(X0,X1)
% 3.30/1.00      | k3_subset_1(X1,X0) != k1_xboole_0
% 3.30/1.00      | u1_struct_0(sK1) != X1
% 3.30/1.00      | sK2 != X0 ),
% 3.30/1.00      inference(resolution_lifted,[status(thm)],[c_399,c_22]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_421,plain,
% 3.30/1.00      ( ~ r1_tarski(sK2,u1_struct_0(sK1))
% 3.30/1.00      | k3_subset_1(u1_struct_0(sK1),sK2) != k1_xboole_0 ),
% 3.30/1.00      inference(unflattening,[status(thm)],[c_420]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_557,plain,
% 3.30/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.30/1.00      | k3_subset_1(u1_struct_0(sK1),sK2) != k1_xboole_0
% 3.30/1.00      | u1_struct_0(sK1) != X1
% 3.30/1.00      | sK2 != X0 ),
% 3.30/1.00      inference(resolution_lifted,[status(thm)],[c_217,c_421]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_558,plain,
% 3.30/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.30/1.00      | k3_subset_1(u1_struct_0(sK1),sK2) != k1_xboole_0 ),
% 3.30/1.00      inference(unflattening,[status(thm)],[c_557]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_560,plain,
% 3.30/1.00      ( k3_subset_1(u1_struct_0(sK1),sK2) != k1_xboole_0 ),
% 3.30/1.00      inference(global_propositional_subsumption,[status(thm)],[c_558,c_25]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_6017,plain,
% 3.30/1.00      ( k4_xboole_0(u1_struct_0(sK1),sK2) != k1_xboole_0 ),
% 3.30/1.00      inference(demodulation,[status(thm)],[c_4979,c_560]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_6618,plain,
% 3.30/1.00      ( k4_xboole_0(sK2,sK2) != k1_xboole_0 ),
% 3.30/1.00      inference(demodulation,[status(thm)],[c_6614,c_6017]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_3,plain,
% 3.30/1.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.30/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_0,plain,
% 3.30/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.30/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1914,plain,
% 3.30/1.00      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1424,plain,
% 3.30/1.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2141,plain,
% 3.30/1.00      ( r1_tarski(k4_xboole_0(X0,X0),k1_xboole_0) = iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_1914,c_1424]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_4,plain,
% 3.30/1.00      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 3.30/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1423,plain,
% 3.30/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2341,plain,
% 3.30/1.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_2141,c_1423]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_6705,plain,
% 3.30/1.00      ( k1_xboole_0 != k1_xboole_0 ),
% 3.30/1.00      inference(demodulation,[status(thm)],[c_6618,c_2341]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_6706,plain,
% 3.30/1.00      ( $false ),
% 3.30/1.00      inference(equality_resolution_simp,[status(thm)],[c_6705]) ).
% 3.30/1.00  
% 3.30/1.00  
% 3.30/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.30/1.00  
% 3.30/1.00  ------                               Statistics
% 3.30/1.00  
% 3.30/1.00  ------ Selected
% 3.30/1.00  
% 3.30/1.00  total_time:                             0.172
% 3.30/1.00  
%------------------------------------------------------------------------------
