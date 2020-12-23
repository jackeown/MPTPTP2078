%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:12 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 835 expanded)
%              Number of clauses        :   97 ( 231 expanded)
%              Number of leaves         :   21 ( 183 expanded)
%              Depth                    :   27
%              Number of atoms          :  635 (4780 expanded)
%              Number of equality atoms :  143 ( 301 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f18,conjecture,(
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

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( v1_subset_1(sK2,u1_struct_0(X0))
          | ~ v3_tex_2(sK2,X0) )
        & ( ~ v1_subset_1(sK2,u1_struct_0(X0))
          | v3_tex_2(sK2,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
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
          ( ( v1_subset_1(X1,u1_struct_0(sK1))
            | ~ v3_tex_2(X1,sK1) )
          & ( ~ v1_subset_1(X1,u1_struct_0(sK1))
            | v3_tex_2(X1,sK1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v1_tdlat_3(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ( v1_subset_1(sK2,u1_struct_0(sK1))
      | ~ v3_tex_2(sK2,sK1) )
    & ( ~ v1_subset_1(sK2,u1_struct_0(sK1))
      | v3_tex_2(sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v1_tdlat_3(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f50,f52,f51])).

fof(f81,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f53])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f63,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f60,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f80,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK0(X0),X0)
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK0(X0),X0)
            & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f46,f47])).

fof(f71,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f78,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f79,plain,(
    v1_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | u1_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f83,plain,
    ( v1_subset_1(sK2,u1_struct_0(sK1))
    | ~ v3_tex_2(sK2,sK1) ),
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

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f17,axiom,(
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

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f66,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f77,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f67,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f82,plain,
    ( ~ v1_subset_1(sK2,u1_struct_0(sK1))
    | v3_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f53])).

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

fof(f36,plain,(
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

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1073,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1071,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_9,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_6,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_383,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_9,c_6])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_706,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_383,c_26])).

cnf(c_707,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_706])).

cnf(c_1082,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1071,c_707])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X1,X0) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1075,plain,
    ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1399,plain,
    ( k4_xboole_0(k2_struct_0(sK1),sK2) = k3_subset_1(k2_struct_0(sK1),sK2) ),
    inference(superposition,[status(thm)],[c_1082,c_1075])).

cnf(c_2,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1074,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1085,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1074,c_0])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1072,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1455,plain,
    ( k7_subset_1(X0,X0,X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1085,c_1072])).

cnf(c_19,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_717,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_26])).

cnf(c_718,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_tdlat_3(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_717])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_27,negated_conjecture,
    ( v1_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_722,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_718,c_28,c_27])).

cnf(c_7,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
    | v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_11,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_620,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X3)
    | X2 != X1
    | X3 != X0
    | k2_pre_topc(X3,X2) = X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_11])).

cnf(c_621,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | k2_pre_topc(X0,X1) = X1 ),
    inference(unflattening,[status(thm)],[c_620])).

cnf(c_691,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k2_pre_topc(X0,X1) = X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_621,c_26])).

cnf(c_692,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_691])).

cnf(c_800,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X1) != X0
    | k2_pre_topc(sK1,X1) = X1
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_722,c_692])).

cnf(c_801,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_800])).

cnf(c_1070,plain,
    ( k2_pre_topc(sK1,X0) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_801])).

cnf(c_1115,plain,
    ( k2_pre_topc(sK1,X0) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1070,c_707])).

cnf(c_1631,plain,
    ( k2_pre_topc(sK1,X0) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(k4_xboole_0(k2_struct_0(sK1),X0),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1455,c_1115])).

cnf(c_1640,plain,
    ( k2_pre_topc(sK1,sK2) = sK2
    | m1_subset_1(k3_subset_1(k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1399,c_1631])).

cnf(c_1717,plain,
    ( m1_subset_1(k3_subset_1(k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | k2_pre_topc(sK1,sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1640,c_1082])).

cnf(c_1718,plain,
    ( k2_pre_topc(sK1,sK2) = sK2
    | m1_subset_1(k3_subset_1(k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1717])).

cnf(c_1723,plain,
    ( k2_pre_topc(sK1,sK2) = sK2
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1073,c_1718])).

cnf(c_1827,plain,
    ( k2_pre_topc(sK1,sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1723,c_1082])).

cnf(c_13,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_750,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) != u1_struct_0(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_26])).

cnf(c_751,plain,
    ( v1_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,X0) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_750])).

cnf(c_5,plain,
    ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_23,negated_conjecture,
    ( ~ v3_tex_2(sK2,sK1)
    | v1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_224,plain,
    ( ~ v3_tex_2(sK2,sK1)
    | v1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(prop_impl,[status(thm)],[c_23])).

cnf(c_498,plain,
    ( ~ v3_tex_2(sK2,sK1)
    | u1_struct_0(sK1) != X0
    | k2_subset_1(X0) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_224])).

cnf(c_499,plain,
    ( ~ v3_tex_2(sK2,sK1)
    | k2_subset_1(u1_struct_0(sK1)) != sK2 ),
    inference(unflattening,[status(thm)],[c_498])).

cnf(c_20,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_22,plain,
    ( v3_tex_2(X0,X1)
    | ~ v2_tex_2(X0,X1)
    | ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_397,plain,
    ( v3_tex_2(X0,X1)
    | ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_20,c_22])).

cnf(c_12,plain,
    ( ~ v1_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_415,plain,
    ( v3_tex_2(X0,X1)
    | ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_397,c_12])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_432,plain,
    ( v3_tex_2(X0,X1)
    | ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_415,c_29])).

cnf(c_433,plain,
    ( v3_tex_2(X0,sK1)
    | ~ v1_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_432])).

cnf(c_437,plain,
    ( v3_tex_2(X0,sK1)
    | ~ v1_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_433,c_27,c_26])).

cnf(c_591,plain,
    ( ~ v1_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_subset_1(u1_struct_0(sK1)) != sK2
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_499,c_437])).

cnf(c_592,plain,
    ( ~ v1_tops_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_subset_1(u1_struct_0(sK1)) != sK2 ),
    inference(unflattening,[status(thm)],[c_591])).

cnf(c_594,plain,
    ( ~ v1_tops_1(sK2,sK1)
    | k2_subset_1(u1_struct_0(sK1)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_592,c_25])).

cnf(c_831,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,X0) != u1_struct_0(sK1)
    | k2_subset_1(u1_struct_0(sK1)) != sK2
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_751,c_594])).

cnf(c_832,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,sK2) != u1_struct_0(sK1)
    | k2_subset_1(u1_struct_0(sK1)) != sK2 ),
    inference(unflattening,[status(thm)],[c_831])).

cnf(c_834,plain,
    ( k2_pre_topc(sK1,sK2) != u1_struct_0(sK1)
    | k2_subset_1(u1_struct_0(sK1)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_832,c_25])).

cnf(c_1096,plain,
    ( k2_pre_topc(sK1,sK2) != k2_struct_0(sK1)
    | k2_subset_1(k2_struct_0(sK1)) != sK2 ),
    inference(light_normalisation,[status(thm)],[c_834,c_707])).

cnf(c_1097,plain,
    ( k2_pre_topc(sK1,sK2) != k2_struct_0(sK1)
    | k2_struct_0(sK1) != sK2 ),
    inference(demodulation,[status(thm)],[c_1096,c_0])).

cnf(c_1830,plain,
    ( k2_struct_0(sK1) != sK2 ),
    inference(demodulation,[status(thm)],[c_1827,c_1097])).

cnf(c_14,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_735,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = u1_struct_0(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_736,plain,
    ( ~ v1_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,X0) = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_735])).

cnf(c_15,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_24,negated_conjecture,
    ( v3_tex_2(sK2,sK1)
    | ~ v1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_222,plain,
    ( v3_tex_2(sK2,sK1)
    | ~ v1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(prop_impl,[status(thm)],[c_24])).

cnf(c_510,plain,
    ( v3_tex_2(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 = X0
    | u1_struct_0(sK1) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_222])).

cnf(c_511,plain,
    ( v3_tex_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_struct_0(sK1) = sK2 ),
    inference(unflattening,[status(thm)],[c_510])).

cnf(c_513,plain,
    ( v3_tex_2(sK2,sK1)
    | u1_struct_0(sK1) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_511,c_25])).

cnf(c_21,plain,
    ( ~ v3_tex_2(X0,X1)
    | v1_tops_1(X0,X1)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_453,plain,
    ( ~ v3_tex_2(X0,X1)
    | v1_tops_1(X0,X1)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_29])).

cnf(c_454,plain,
    ( ~ v3_tex_2(X0,sK1)
    | v1_tops_1(X0,sK1)
    | ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_453])).

cnf(c_458,plain,
    ( ~ v3_tex_2(X0,sK1)
    | v1_tops_1(X0,sK1)
    | ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_454,c_28,c_26])).

cnf(c_557,plain,
    ( v1_tops_1(X0,sK1)
    | ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_struct_0(sK1) = sK2
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_513,c_458])).

cnf(c_558,plain,
    ( v1_tops_1(sK2,sK1)
    | ~ v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_struct_0(sK1) = sK2 ),
    inference(unflattening,[status(thm)],[c_557])).

cnf(c_560,plain,
    ( ~ v3_pre_topc(sK2,sK1)
    | v1_tops_1(sK2,sK1)
    | u1_struct_0(sK1) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_558,c_25])).

cnf(c_561,plain,
    ( v1_tops_1(sK2,sK1)
    | ~ v3_pre_topc(sK2,sK1)
    | u1_struct_0(sK1) = sK2 ),
    inference(renaming,[status(thm)],[c_560])).

cnf(c_786,plain,
    ( v1_tops_1(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_struct_0(sK1) = sK2
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_722,c_561])).

cnf(c_787,plain,
    ( v1_tops_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_struct_0(sK1) = sK2 ),
    inference(unflattening,[status(thm)],[c_786])).

cnf(c_789,plain,
    ( v1_tops_1(sK2,sK1)
    | u1_struct_0(sK1) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_787,c_25])).

cnf(c_859,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,X0) = u1_struct_0(sK1)
    | u1_struct_0(sK1) = sK2
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_736,c_789])).

cnf(c_860,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1)
    | u1_struct_0(sK1) = sK2 ),
    inference(unflattening,[status(thm)],[c_859])).

cnf(c_862,plain,
    ( k2_pre_topc(sK1,sK2) = u1_struct_0(sK1)
    | u1_struct_0(sK1) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_860,c_25])).

cnf(c_1088,plain,
    ( k2_pre_topc(sK1,sK2) = k2_struct_0(sK1)
    | u1_struct_0(sK1) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_862,c_707])).

cnf(c_1089,plain,
    ( k2_pre_topc(sK1,sK2) = k2_struct_0(sK1)
    | k2_struct_0(sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_1088,c_707])).

cnf(c_1831,plain,
    ( k2_struct_0(sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_1827,c_1089])).

cnf(c_1834,plain,
    ( sK2 != sK2 ),
    inference(light_normalisation,[status(thm)],[c_1830,c_1831])).

cnf(c_1835,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_1834])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:08:57 EST 2020
% 0.21/0.34  % CPUTime    : 
% 0.21/0.34  % Running in FOF mode
% 2.45/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/0.98  
% 2.45/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.45/0.98  
% 2.45/0.98  ------  iProver source info
% 2.45/0.98  
% 2.45/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.45/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.45/0.98  git: non_committed_changes: false
% 2.45/0.98  git: last_make_outside_of_git: false
% 2.45/0.98  
% 2.45/0.98  ------ 
% 2.45/0.98  
% 2.45/0.98  ------ Input Options
% 2.45/0.98  
% 2.45/0.98  --out_options                           all
% 2.45/0.98  --tptp_safe_out                         true
% 2.45/0.98  --problem_path                          ""
% 2.45/0.98  --include_path                          ""
% 2.45/0.98  --clausifier                            res/vclausify_rel
% 2.45/0.98  --clausifier_options                    --mode clausify
% 2.45/0.98  --stdin                                 false
% 2.45/0.98  --stats_out                             all
% 2.45/0.98  
% 2.45/0.98  ------ General Options
% 2.45/0.98  
% 2.45/0.98  --fof                                   false
% 2.45/0.98  --time_out_real                         305.
% 2.45/0.98  --time_out_virtual                      -1.
% 2.45/0.98  --symbol_type_check                     false
% 2.45/0.98  --clausify_out                          false
% 2.45/0.98  --sig_cnt_out                           false
% 2.45/0.98  --trig_cnt_out                          false
% 2.45/0.98  --trig_cnt_out_tolerance                1.
% 2.45/0.98  --trig_cnt_out_sk_spl                   false
% 2.45/0.98  --abstr_cl_out                          false
% 2.45/0.98  
% 2.45/0.98  ------ Global Options
% 2.45/0.98  
% 2.45/0.98  --schedule                              default
% 2.45/0.98  --add_important_lit                     false
% 2.45/0.98  --prop_solver_per_cl                    1000
% 2.45/0.98  --min_unsat_core                        false
% 2.45/0.98  --soft_assumptions                      false
% 2.45/0.98  --soft_lemma_size                       3
% 2.45/0.98  --prop_impl_unit_size                   0
% 2.45/0.98  --prop_impl_unit                        []
% 2.45/0.98  --share_sel_clauses                     true
% 2.45/0.98  --reset_solvers                         false
% 2.45/0.98  --bc_imp_inh                            [conj_cone]
% 2.45/0.98  --conj_cone_tolerance                   3.
% 2.45/0.98  --extra_neg_conj                        none
% 2.45/0.98  --large_theory_mode                     true
% 2.45/0.98  --prolific_symb_bound                   200
% 2.45/0.98  --lt_threshold                          2000
% 2.45/0.98  --clause_weak_htbl                      true
% 2.45/0.98  --gc_record_bc_elim                     false
% 2.45/0.98  
% 2.45/0.98  ------ Preprocessing Options
% 2.45/0.98  
% 2.45/0.98  --preprocessing_flag                    true
% 2.45/0.98  --time_out_prep_mult                    0.1
% 2.45/0.98  --splitting_mode                        input
% 2.45/0.98  --splitting_grd                         true
% 2.45/0.98  --splitting_cvd                         false
% 2.45/0.98  --splitting_cvd_svl                     false
% 2.45/0.98  --splitting_nvd                         32
% 2.45/0.98  --sub_typing                            true
% 2.45/0.98  --prep_gs_sim                           true
% 2.45/0.98  --prep_unflatten                        true
% 2.45/0.98  --prep_res_sim                          true
% 2.45/0.98  --prep_upred                            true
% 2.45/0.98  --prep_sem_filter                       exhaustive
% 2.45/0.98  --prep_sem_filter_out                   false
% 2.45/0.98  --pred_elim                             true
% 2.45/0.98  --res_sim_input                         true
% 2.45/0.98  --eq_ax_congr_red                       true
% 2.45/0.98  --pure_diseq_elim                       true
% 2.45/0.98  --brand_transform                       false
% 2.45/0.98  --non_eq_to_eq                          false
% 2.45/0.98  --prep_def_merge                        true
% 2.45/0.98  --prep_def_merge_prop_impl              false
% 2.45/0.98  --prep_def_merge_mbd                    true
% 2.45/0.98  --prep_def_merge_tr_red                 false
% 2.45/0.98  --prep_def_merge_tr_cl                  false
% 2.45/0.98  --smt_preprocessing                     true
% 2.45/0.98  --smt_ac_axioms                         fast
% 2.45/0.98  --preprocessed_out                      false
% 2.45/0.98  --preprocessed_stats                    false
% 2.45/0.98  
% 2.45/0.98  ------ Abstraction refinement Options
% 2.45/0.98  
% 2.45/0.98  --abstr_ref                             []
% 2.45/0.98  --abstr_ref_prep                        false
% 2.45/0.98  --abstr_ref_until_sat                   false
% 2.45/0.98  --abstr_ref_sig_restrict                funpre
% 2.45/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.45/0.98  --abstr_ref_under                       []
% 2.45/0.98  
% 2.45/0.98  ------ SAT Options
% 2.45/0.98  
% 2.45/0.98  --sat_mode                              false
% 2.45/0.98  --sat_fm_restart_options                ""
% 2.45/0.98  --sat_gr_def                            false
% 2.45/0.98  --sat_epr_types                         true
% 2.45/0.98  --sat_non_cyclic_types                  false
% 2.45/0.98  --sat_finite_models                     false
% 2.45/0.98  --sat_fm_lemmas                         false
% 2.45/0.98  --sat_fm_prep                           false
% 2.45/0.98  --sat_fm_uc_incr                        true
% 2.45/0.98  --sat_out_model                         small
% 2.45/0.98  --sat_out_clauses                       false
% 2.45/0.98  
% 2.45/0.98  ------ QBF Options
% 2.45/0.98  
% 2.45/0.98  --qbf_mode                              false
% 2.45/0.98  --qbf_elim_univ                         false
% 2.45/0.98  --qbf_dom_inst                          none
% 2.45/0.98  --qbf_dom_pre_inst                      false
% 2.45/0.98  --qbf_sk_in                             false
% 2.45/0.98  --qbf_pred_elim                         true
% 2.45/0.98  --qbf_split                             512
% 2.45/0.98  
% 2.45/0.98  ------ BMC1 Options
% 2.45/0.98  
% 2.45/0.98  --bmc1_incremental                      false
% 2.45/0.98  --bmc1_axioms                           reachable_all
% 2.45/0.98  --bmc1_min_bound                        0
% 2.45/0.98  --bmc1_max_bound                        -1
% 2.45/0.98  --bmc1_max_bound_default                -1
% 2.45/0.98  --bmc1_symbol_reachability              true
% 2.45/0.98  --bmc1_property_lemmas                  false
% 2.45/0.98  --bmc1_k_induction                      false
% 2.45/0.98  --bmc1_non_equiv_states                 false
% 2.45/0.98  --bmc1_deadlock                         false
% 2.45/0.98  --bmc1_ucm                              false
% 2.45/0.98  --bmc1_add_unsat_core                   none
% 2.45/0.98  --bmc1_unsat_core_children              false
% 2.45/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.45/0.98  --bmc1_out_stat                         full
% 2.45/0.98  --bmc1_ground_init                      false
% 2.45/0.98  --bmc1_pre_inst_next_state              false
% 2.45/0.98  --bmc1_pre_inst_state                   false
% 2.45/0.98  --bmc1_pre_inst_reach_state             false
% 2.45/0.98  --bmc1_out_unsat_core                   false
% 2.45/0.98  --bmc1_aig_witness_out                  false
% 2.45/0.98  --bmc1_verbose                          false
% 2.45/0.98  --bmc1_dump_clauses_tptp                false
% 2.45/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.45/0.98  --bmc1_dump_file                        -
% 2.45/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.45/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.45/0.98  --bmc1_ucm_extend_mode                  1
% 2.45/0.98  --bmc1_ucm_init_mode                    2
% 2.45/0.98  --bmc1_ucm_cone_mode                    none
% 2.45/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.45/0.98  --bmc1_ucm_relax_model                  4
% 2.45/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.45/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.45/0.98  --bmc1_ucm_layered_model                none
% 2.45/0.98  --bmc1_ucm_max_lemma_size               10
% 2.45/0.98  
% 2.45/0.98  ------ AIG Options
% 2.45/0.98  
% 2.45/0.98  --aig_mode                              false
% 2.45/0.98  
% 2.45/0.98  ------ Instantiation Options
% 2.45/0.98  
% 2.45/0.98  --instantiation_flag                    true
% 2.45/0.98  --inst_sos_flag                         false
% 2.45/0.98  --inst_sos_phase                        true
% 2.45/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.45/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.45/0.98  --inst_lit_sel_side                     num_symb
% 2.45/0.98  --inst_solver_per_active                1400
% 2.45/0.98  --inst_solver_calls_frac                1.
% 2.45/0.98  --inst_passive_queue_type               priority_queues
% 2.45/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.45/0.98  --inst_passive_queues_freq              [25;2]
% 2.45/0.98  --inst_dismatching                      true
% 2.45/0.98  --inst_eager_unprocessed_to_passive     true
% 2.45/0.98  --inst_prop_sim_given                   true
% 2.45/0.98  --inst_prop_sim_new                     false
% 2.45/0.98  --inst_subs_new                         false
% 2.45/0.98  --inst_eq_res_simp                      false
% 2.45/0.98  --inst_subs_given                       false
% 2.45/0.98  --inst_orphan_elimination               true
% 2.45/0.98  --inst_learning_loop_flag               true
% 2.45/0.98  --inst_learning_start                   3000
% 2.45/0.98  --inst_learning_factor                  2
% 2.45/0.98  --inst_start_prop_sim_after_learn       3
% 2.45/0.98  --inst_sel_renew                        solver
% 2.45/0.98  --inst_lit_activity_flag                true
% 2.45/0.98  --inst_restr_to_given                   false
% 2.45/0.98  --inst_activity_threshold               500
% 2.45/0.98  --inst_out_proof                        true
% 2.45/0.98  
% 2.45/0.98  ------ Resolution Options
% 2.45/0.98  
% 2.45/0.98  --resolution_flag                       true
% 2.45/0.98  --res_lit_sel                           adaptive
% 2.45/0.98  --res_lit_sel_side                      none
% 2.45/0.98  --res_ordering                          kbo
% 2.45/0.98  --res_to_prop_solver                    active
% 2.45/0.98  --res_prop_simpl_new                    false
% 2.45/0.98  --res_prop_simpl_given                  true
% 2.45/0.98  --res_passive_queue_type                priority_queues
% 2.45/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.45/0.98  --res_passive_queues_freq               [15;5]
% 2.45/0.98  --res_forward_subs                      full
% 2.45/0.98  --res_backward_subs                     full
% 2.45/0.98  --res_forward_subs_resolution           true
% 2.45/0.98  --res_backward_subs_resolution          true
% 2.45/0.98  --res_orphan_elimination                true
% 2.45/0.98  --res_time_limit                        2.
% 2.45/0.98  --res_out_proof                         true
% 2.45/0.98  
% 2.45/0.98  ------ Superposition Options
% 2.45/0.98  
% 2.45/0.98  --superposition_flag                    true
% 2.45/0.98  --sup_passive_queue_type                priority_queues
% 2.45/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.45/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.45/0.98  --demod_completeness_check              fast
% 2.45/0.98  --demod_use_ground                      true
% 2.45/0.98  --sup_to_prop_solver                    passive
% 2.45/0.98  --sup_prop_simpl_new                    true
% 2.45/0.98  --sup_prop_simpl_given                  true
% 2.45/0.98  --sup_fun_splitting                     false
% 2.45/0.98  --sup_smt_interval                      50000
% 2.45/0.98  
% 2.45/0.98  ------ Superposition Simplification Setup
% 2.45/0.98  
% 2.45/0.98  --sup_indices_passive                   []
% 2.45/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.45/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/0.98  --sup_full_bw                           [BwDemod]
% 2.45/0.98  --sup_immed_triv                        [TrivRules]
% 2.45/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.45/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/0.98  --sup_immed_bw_main                     []
% 2.45/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.45/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/0.98  
% 2.45/0.98  ------ Combination Options
% 2.45/0.98  
% 2.45/0.98  --comb_res_mult                         3
% 2.45/0.98  --comb_sup_mult                         2
% 2.45/0.98  --comb_inst_mult                        10
% 2.45/0.98  
% 2.45/0.98  ------ Debug Options
% 2.45/0.98  
% 2.45/0.98  --dbg_backtrace                         false
% 2.45/0.98  --dbg_dump_prop_clauses                 false
% 2.45/0.98  --dbg_dump_prop_clauses_file            -
% 2.45/0.98  --dbg_out_stat                          false
% 2.45/0.98  ------ Parsing...
% 2.45/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.45/0.98  
% 2.45/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 2.45/0.98  
% 2.45/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.45/0.98  
% 2.45/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.45/0.98  ------ Proving...
% 2.45/0.98  ------ Problem Properties 
% 2.45/0.98  
% 2.45/0.98  
% 2.45/0.98  clauses                                 13
% 2.45/0.98  conjectures                             1
% 2.45/0.98  EPR                                     0
% 2.45/0.98  Horn                                    12
% 2.45/0.98  unary                                   5
% 2.45/0.98  binary                                  6
% 2.45/0.98  lits                                    23
% 2.45/0.98  lits eq                                 14
% 2.45/0.98  fd_pure                                 0
% 2.45/0.98  fd_pseudo                               0
% 2.45/0.98  fd_cond                                 0
% 2.45/0.98  fd_pseudo_cond                          0
% 2.45/0.98  AC symbols                              0
% 2.45/0.98  
% 2.45/0.98  ------ Schedule dynamic 5 is on 
% 2.45/0.98  
% 2.45/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.45/0.98  
% 2.45/0.98  
% 2.45/0.98  ------ 
% 2.45/0.98  Current options:
% 2.45/0.98  ------ 
% 2.45/0.98  
% 2.45/0.98  ------ Input Options
% 2.45/0.98  
% 2.45/0.98  --out_options                           all
% 2.45/0.98  --tptp_safe_out                         true
% 2.45/0.98  --problem_path                          ""
% 2.45/0.98  --include_path                          ""
% 2.45/0.98  --clausifier                            res/vclausify_rel
% 2.45/0.98  --clausifier_options                    --mode clausify
% 2.45/0.98  --stdin                                 false
% 2.45/0.98  --stats_out                             all
% 2.45/0.98  
% 2.45/0.98  ------ General Options
% 2.45/0.98  
% 2.45/0.98  --fof                                   false
% 2.45/0.98  --time_out_real                         305.
% 2.45/0.98  --time_out_virtual                      -1.
% 2.45/0.98  --symbol_type_check                     false
% 2.45/0.98  --clausify_out                          false
% 2.45/0.98  --sig_cnt_out                           false
% 2.45/0.98  --trig_cnt_out                          false
% 2.45/0.98  --trig_cnt_out_tolerance                1.
% 2.45/0.98  --trig_cnt_out_sk_spl                   false
% 2.45/0.98  --abstr_cl_out                          false
% 2.45/0.98  
% 2.45/0.98  ------ Global Options
% 2.45/0.98  
% 2.45/0.98  --schedule                              default
% 2.45/0.98  --add_important_lit                     false
% 2.45/0.98  --prop_solver_per_cl                    1000
% 2.45/0.98  --min_unsat_core                        false
% 2.45/0.98  --soft_assumptions                      false
% 2.45/0.98  --soft_lemma_size                       3
% 2.45/0.98  --prop_impl_unit_size                   0
% 2.45/0.98  --prop_impl_unit                        []
% 2.45/0.98  --share_sel_clauses                     true
% 2.45/0.98  --reset_solvers                         false
% 2.45/0.98  --bc_imp_inh                            [conj_cone]
% 2.45/0.98  --conj_cone_tolerance                   3.
% 2.45/0.98  --extra_neg_conj                        none
% 2.45/0.98  --large_theory_mode                     true
% 2.45/0.98  --prolific_symb_bound                   200
% 2.45/0.98  --lt_threshold                          2000
% 2.45/0.98  --clause_weak_htbl                      true
% 2.45/0.98  --gc_record_bc_elim                     false
% 2.45/0.98  
% 2.45/0.98  ------ Preprocessing Options
% 2.45/0.98  
% 2.45/0.98  --preprocessing_flag                    true
% 2.45/0.98  --time_out_prep_mult                    0.1
% 2.45/0.98  --splitting_mode                        input
% 2.45/0.98  --splitting_grd                         true
% 2.45/0.98  --splitting_cvd                         false
% 2.45/0.98  --splitting_cvd_svl                     false
% 2.45/0.98  --splitting_nvd                         32
% 2.45/0.98  --sub_typing                            true
% 2.45/0.98  --prep_gs_sim                           true
% 2.45/0.98  --prep_unflatten                        true
% 2.45/0.98  --prep_res_sim                          true
% 2.45/0.98  --prep_upred                            true
% 2.45/0.98  --prep_sem_filter                       exhaustive
% 2.45/0.98  --prep_sem_filter_out                   false
% 2.45/0.98  --pred_elim                             true
% 2.45/0.98  --res_sim_input                         true
% 2.45/0.98  --eq_ax_congr_red                       true
% 2.45/0.98  --pure_diseq_elim                       true
% 2.45/0.98  --brand_transform                       false
% 2.45/0.98  --non_eq_to_eq                          false
% 2.45/0.98  --prep_def_merge                        true
% 2.45/0.98  --prep_def_merge_prop_impl              false
% 2.45/0.98  --prep_def_merge_mbd                    true
% 2.45/0.98  --prep_def_merge_tr_red                 false
% 2.45/0.98  --prep_def_merge_tr_cl                  false
% 2.45/0.98  --smt_preprocessing                     true
% 2.45/0.98  --smt_ac_axioms                         fast
% 2.45/0.98  --preprocessed_out                      false
% 2.45/0.98  --preprocessed_stats                    false
% 2.45/0.98  
% 2.45/0.98  ------ Abstraction refinement Options
% 2.45/0.98  
% 2.45/0.98  --abstr_ref                             []
% 2.45/0.98  --abstr_ref_prep                        false
% 2.45/0.98  --abstr_ref_until_sat                   false
% 2.45/0.98  --abstr_ref_sig_restrict                funpre
% 2.45/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.45/0.98  --abstr_ref_under                       []
% 2.45/0.98  
% 2.45/0.98  ------ SAT Options
% 2.45/0.98  
% 2.45/0.98  --sat_mode                              false
% 2.45/0.98  --sat_fm_restart_options                ""
% 2.45/0.98  --sat_gr_def                            false
% 2.45/0.98  --sat_epr_types                         true
% 2.45/0.98  --sat_non_cyclic_types                  false
% 2.45/0.98  --sat_finite_models                     false
% 2.45/0.98  --sat_fm_lemmas                         false
% 2.45/0.98  --sat_fm_prep                           false
% 2.45/0.98  --sat_fm_uc_incr                        true
% 2.45/0.98  --sat_out_model                         small
% 2.45/0.98  --sat_out_clauses                       false
% 2.45/0.98  
% 2.45/0.98  ------ QBF Options
% 2.45/0.98  
% 2.45/0.98  --qbf_mode                              false
% 2.45/0.98  --qbf_elim_univ                         false
% 2.45/0.98  --qbf_dom_inst                          none
% 2.45/0.98  --qbf_dom_pre_inst                      false
% 2.45/0.98  --qbf_sk_in                             false
% 2.45/0.98  --qbf_pred_elim                         true
% 2.45/0.98  --qbf_split                             512
% 2.45/0.98  
% 2.45/0.98  ------ BMC1 Options
% 2.45/0.98  
% 2.45/0.98  --bmc1_incremental                      false
% 2.45/0.98  --bmc1_axioms                           reachable_all
% 2.45/0.98  --bmc1_min_bound                        0
% 2.45/0.98  --bmc1_max_bound                        -1
% 2.45/0.98  --bmc1_max_bound_default                -1
% 2.45/0.98  --bmc1_symbol_reachability              true
% 2.45/0.98  --bmc1_property_lemmas                  false
% 2.45/0.98  --bmc1_k_induction                      false
% 2.45/0.98  --bmc1_non_equiv_states                 false
% 2.45/0.98  --bmc1_deadlock                         false
% 2.45/0.98  --bmc1_ucm                              false
% 2.45/0.98  --bmc1_add_unsat_core                   none
% 2.45/0.98  --bmc1_unsat_core_children              false
% 2.45/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.45/0.98  --bmc1_out_stat                         full
% 2.45/0.98  --bmc1_ground_init                      false
% 2.45/0.98  --bmc1_pre_inst_next_state              false
% 2.45/0.98  --bmc1_pre_inst_state                   false
% 2.45/0.98  --bmc1_pre_inst_reach_state             false
% 2.45/0.98  --bmc1_out_unsat_core                   false
% 2.45/0.98  --bmc1_aig_witness_out                  false
% 2.45/0.98  --bmc1_verbose                          false
% 2.45/0.98  --bmc1_dump_clauses_tptp                false
% 2.45/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.45/0.98  --bmc1_dump_file                        -
% 2.45/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.45/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.45/0.98  --bmc1_ucm_extend_mode                  1
% 2.45/0.98  --bmc1_ucm_init_mode                    2
% 2.45/0.98  --bmc1_ucm_cone_mode                    none
% 2.45/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.45/0.98  --bmc1_ucm_relax_model                  4
% 2.45/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.45/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.45/0.98  --bmc1_ucm_layered_model                none
% 2.45/0.98  --bmc1_ucm_max_lemma_size               10
% 2.45/0.98  
% 2.45/0.98  ------ AIG Options
% 2.45/0.98  
% 2.45/0.98  --aig_mode                              false
% 2.45/0.98  
% 2.45/0.98  ------ Instantiation Options
% 2.45/0.98  
% 2.45/0.98  --instantiation_flag                    true
% 2.45/0.98  --inst_sos_flag                         false
% 2.45/0.98  --inst_sos_phase                        true
% 2.45/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.45/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.45/0.98  --inst_lit_sel_side                     none
% 2.45/0.98  --inst_solver_per_active                1400
% 2.45/0.98  --inst_solver_calls_frac                1.
% 2.45/0.98  --inst_passive_queue_type               priority_queues
% 2.45/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.45/0.98  --inst_passive_queues_freq              [25;2]
% 2.45/0.98  --inst_dismatching                      true
% 2.45/0.98  --inst_eager_unprocessed_to_passive     true
% 2.45/0.98  --inst_prop_sim_given                   true
% 2.45/0.98  --inst_prop_sim_new                     false
% 2.45/0.98  --inst_subs_new                         false
% 2.45/0.98  --inst_eq_res_simp                      false
% 2.45/0.98  --inst_subs_given                       false
% 2.45/0.98  --inst_orphan_elimination               true
% 2.45/0.98  --inst_learning_loop_flag               true
% 2.45/0.98  --inst_learning_start                   3000
% 2.45/0.98  --inst_learning_factor                  2
% 2.45/0.98  --inst_start_prop_sim_after_learn       3
% 2.45/0.98  --inst_sel_renew                        solver
% 2.45/0.98  --inst_lit_activity_flag                true
% 2.45/0.98  --inst_restr_to_given                   false
% 2.45/0.98  --inst_activity_threshold               500
% 2.45/0.98  --inst_out_proof                        true
% 2.45/0.98  
% 2.45/0.98  ------ Resolution Options
% 2.45/0.98  
% 2.45/0.98  --resolution_flag                       false
% 2.45/0.98  --res_lit_sel                           adaptive
% 2.45/0.98  --res_lit_sel_side                      none
% 2.45/0.98  --res_ordering                          kbo
% 2.45/0.98  --res_to_prop_solver                    active
% 2.45/0.98  --res_prop_simpl_new                    false
% 2.45/0.98  --res_prop_simpl_given                  true
% 2.45/0.98  --res_passive_queue_type                priority_queues
% 2.45/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.45/0.98  --res_passive_queues_freq               [15;5]
% 2.45/0.98  --res_forward_subs                      full
% 2.45/0.98  --res_backward_subs                     full
% 2.45/0.98  --res_forward_subs_resolution           true
% 2.45/0.98  --res_backward_subs_resolution          true
% 2.45/0.98  --res_orphan_elimination                true
% 2.45/0.98  --res_time_limit                        2.
% 2.45/0.98  --res_out_proof                         true
% 2.45/0.98  
% 2.45/0.98  ------ Superposition Options
% 2.45/0.98  
% 2.45/0.98  --superposition_flag                    true
% 2.45/0.98  --sup_passive_queue_type                priority_queues
% 2.45/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.45/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.45/0.98  --demod_completeness_check              fast
% 2.45/0.98  --demod_use_ground                      true
% 2.45/0.98  --sup_to_prop_solver                    passive
% 2.45/0.98  --sup_prop_simpl_new                    true
% 2.45/0.98  --sup_prop_simpl_given                  true
% 2.45/0.98  --sup_fun_splitting                     false
% 2.45/0.98  --sup_smt_interval                      50000
% 2.45/0.98  
% 2.45/0.98  ------ Superposition Simplification Setup
% 2.45/0.98  
% 2.45/0.98  --sup_indices_passive                   []
% 2.45/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.45/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/0.98  --sup_full_bw                           [BwDemod]
% 2.45/0.98  --sup_immed_triv                        [TrivRules]
% 2.45/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.45/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/0.98  --sup_immed_bw_main                     []
% 2.45/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.45/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/0.98  
% 2.45/0.98  ------ Combination Options
% 2.45/0.98  
% 2.45/0.98  --comb_res_mult                         3
% 2.45/0.98  --comb_sup_mult                         2
% 2.45/0.98  --comb_inst_mult                        10
% 2.45/0.98  
% 2.45/0.98  ------ Debug Options
% 2.45/0.98  
% 2.45/0.98  --dbg_backtrace                         false
% 2.45/0.98  --dbg_dump_prop_clauses                 false
% 2.45/0.98  --dbg_dump_prop_clauses_file            -
% 2.45/0.98  --dbg_out_stat                          false
% 2.45/0.98  
% 2.45/0.98  
% 2.45/0.98  
% 2.45/0.98  
% 2.45/0.98  ------ Proving...
% 2.45/0.98  
% 2.45/0.98  
% 2.45/0.98  % SZS status Theorem for theBenchmark.p
% 2.45/0.98  
% 2.45/0.98   Resolution empty clause
% 2.45/0.98  
% 2.45/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.45/0.98  
% 2.45/0.98  fof(f4,axiom,(
% 2.45/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f21,plain,(
% 2.45/0.98    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.45/0.98    inference(ennf_transformation,[],[f4])).
% 2.45/0.98  
% 2.45/0.98  fof(f57,plain,(
% 2.45/0.98    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.45/0.98    inference(cnf_transformation,[],[f21])).
% 2.45/0.98  
% 2.45/0.98  fof(f18,conjecture,(
% 2.45/0.98    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 2.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f19,negated_conjecture,(
% 2.45/0.98    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 2.45/0.98    inference(negated_conjecture,[],[f18])).
% 2.45/0.98  
% 2.45/0.98  fof(f40,plain,(
% 2.45/0.98    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.45/0.98    inference(ennf_transformation,[],[f19])).
% 2.45/0.98  
% 2.45/0.98  fof(f41,plain,(
% 2.45/0.98    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.45/0.98    inference(flattening,[],[f40])).
% 2.45/0.98  
% 2.45/0.98  fof(f49,plain,(
% 2.45/0.98    ? [X0] : (? [X1] : (((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.45/0.98    inference(nnf_transformation,[],[f41])).
% 2.45/0.98  
% 2.45/0.98  fof(f50,plain,(
% 2.45/0.98    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.45/0.98    inference(flattening,[],[f49])).
% 2.45/0.98  
% 2.45/0.98  fof(f52,plain,(
% 2.45/0.98    ( ! [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_subset_1(sK2,u1_struct_0(X0)) | ~v3_tex_2(sK2,X0)) & (~v1_subset_1(sK2,u1_struct_0(X0)) | v3_tex_2(sK2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.45/0.98    introduced(choice_axiom,[])).
% 2.45/0.98  
% 2.45/0.98  fof(f51,plain,(
% 2.45/0.98    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((v1_subset_1(X1,u1_struct_0(sK1)) | ~v3_tex_2(X1,sK1)) & (~v1_subset_1(X1,u1_struct_0(sK1)) | v3_tex_2(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v1_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.45/0.98    introduced(choice_axiom,[])).
% 2.45/0.98  
% 2.45/0.98  fof(f53,plain,(
% 2.45/0.98    ((v1_subset_1(sK2,u1_struct_0(sK1)) | ~v3_tex_2(sK2,sK1)) & (~v1_subset_1(sK2,u1_struct_0(sK1)) | v3_tex_2(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v1_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.45/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f50,f52,f51])).
% 2.45/0.98  
% 2.45/0.98  fof(f81,plain,(
% 2.45/0.98    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.45/0.98    inference(cnf_transformation,[],[f53])).
% 2.45/0.98  
% 2.45/0.98  fof(f9,axiom,(
% 2.45/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f25,plain,(
% 2.45/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.45/0.98    inference(ennf_transformation,[],[f9])).
% 2.45/0.98  
% 2.45/0.98  fof(f63,plain,(
% 2.45/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.45/0.98    inference(cnf_transformation,[],[f25])).
% 2.45/0.98  
% 2.45/0.98  fof(f7,axiom,(
% 2.45/0.98    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f23,plain,(
% 2.45/0.98    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.45/0.98    inference(ennf_transformation,[],[f7])).
% 2.45/0.98  
% 2.45/0.98  fof(f60,plain,(
% 2.45/0.98    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.45/0.98    inference(cnf_transformation,[],[f23])).
% 2.45/0.98  
% 2.45/0.98  fof(f80,plain,(
% 2.45/0.98    l1_pre_topc(sK1)),
% 2.45/0.98    inference(cnf_transformation,[],[f53])).
% 2.45/0.98  
% 2.45/0.98  fof(f2,axiom,(
% 2.45/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 2.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f20,plain,(
% 2.45/0.98    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.45/0.98    inference(ennf_transformation,[],[f2])).
% 2.45/0.98  
% 2.45/0.98  fof(f55,plain,(
% 2.45/0.98    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.45/0.98    inference(cnf_transformation,[],[f20])).
% 2.45/0.98  
% 2.45/0.98  fof(f3,axiom,(
% 2.45/0.98    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f56,plain,(
% 2.45/0.98    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.45/0.98    inference(cnf_transformation,[],[f3])).
% 2.45/0.98  
% 2.45/0.98  fof(f1,axiom,(
% 2.45/0.98    ! [X0] : k2_subset_1(X0) = X0),
% 2.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f54,plain,(
% 2.45/0.98    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.45/0.98    inference(cnf_transformation,[],[f1])).
% 2.45/0.98  
% 2.45/0.98  fof(f5,axiom,(
% 2.45/0.98    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 2.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f22,plain,(
% 2.45/0.98    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.45/0.98    inference(ennf_transformation,[],[f5])).
% 2.45/0.98  
% 2.45/0.98  fof(f58,plain,(
% 2.45/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.45/0.98    inference(cnf_transformation,[],[f22])).
% 2.45/0.98  
% 2.45/0.98  fof(f14,axiom,(
% 2.45/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 2.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f32,plain,(
% 2.45/0.98    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.45/0.98    inference(ennf_transformation,[],[f14])).
% 2.45/0.98  
% 2.45/0.98  fof(f33,plain,(
% 2.45/0.98    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.45/0.98    inference(flattening,[],[f32])).
% 2.45/0.98  
% 2.45/0.98  fof(f45,plain,(
% 2.45/0.98    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.45/0.98    inference(nnf_transformation,[],[f33])).
% 2.45/0.98  
% 2.45/0.98  fof(f46,plain,(
% 2.45/0.98    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.45/0.98    inference(rectify,[],[f45])).
% 2.45/0.98  
% 2.45/0.98  fof(f47,plain,(
% 2.45/0.98    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK0(X0),X0) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.45/0.98    introduced(choice_axiom,[])).
% 2.45/0.98  
% 2.45/0.98  fof(f48,plain,(
% 2.45/0.98    ! [X0] : (((v1_tdlat_3(X0) | (~v3_pre_topc(sK0(X0),X0) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.45/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f46,f47])).
% 2.45/0.98  
% 2.45/0.98  fof(f71,plain,(
% 2.45/0.98    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.45/0.98    inference(cnf_transformation,[],[f48])).
% 2.45/0.98  
% 2.45/0.98  fof(f78,plain,(
% 2.45/0.98    v2_pre_topc(sK1)),
% 2.45/0.98    inference(cnf_transformation,[],[f53])).
% 2.45/0.98  
% 2.45/0.98  fof(f79,plain,(
% 2.45/0.98    v1_tdlat_3(sK1)),
% 2.45/0.98    inference(cnf_transformation,[],[f53])).
% 2.45/0.98  
% 2.45/0.98  fof(f8,axiom,(
% 2.45/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0))))),
% 2.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f24,plain,(
% 2.45/0.98    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.45/0.98    inference(ennf_transformation,[],[f8])).
% 2.45/0.98  
% 2.45/0.98  fof(f42,plain,(
% 2.45/0.98    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) & (v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.45/0.98    inference(nnf_transformation,[],[f24])).
% 2.45/0.98  
% 2.45/0.98  fof(f62,plain,(
% 2.45/0.98    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.45/0.98    inference(cnf_transformation,[],[f42])).
% 2.45/0.98  
% 2.45/0.98  fof(f10,axiom,(
% 2.45/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f26,plain,(
% 2.45/0.98    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.45/0.98    inference(ennf_transformation,[],[f10])).
% 2.45/0.98  
% 2.45/0.98  fof(f27,plain,(
% 2.45/0.98    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.45/0.98    inference(flattening,[],[f26])).
% 2.45/0.98  
% 2.45/0.98  fof(f64,plain,(
% 2.45/0.98    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.45/0.98    inference(cnf_transformation,[],[f27])).
% 2.45/0.98  
% 2.45/0.98  fof(f12,axiom,(
% 2.45/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 2.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f30,plain,(
% 2.45/0.98    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.45/0.98    inference(ennf_transformation,[],[f12])).
% 2.45/0.98  
% 2.45/0.98  fof(f43,plain,(
% 2.45/0.98    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.45/0.98    inference(nnf_transformation,[],[f30])).
% 2.45/0.98  
% 2.45/0.98  fof(f68,plain,(
% 2.45/0.98    ( ! [X0,X1] : (v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.45/0.98    inference(cnf_transformation,[],[f43])).
% 2.45/0.98  
% 2.45/0.98  fof(f6,axiom,(
% 2.45/0.98    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 2.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f59,plain,(
% 2.45/0.98    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 2.45/0.98    inference(cnf_transformation,[],[f6])).
% 2.45/0.98  
% 2.45/0.98  fof(f83,plain,(
% 2.45/0.98    v1_subset_1(sK2,u1_struct_0(sK1)) | ~v3_tex_2(sK2,sK1)),
% 2.45/0.98    inference(cnf_transformation,[],[f53])).
% 2.45/0.98  
% 2.45/0.98  fof(f15,axiom,(
% 2.45/0.98    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 2.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f34,plain,(
% 2.45/0.98    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.45/0.98    inference(ennf_transformation,[],[f15])).
% 2.45/0.98  
% 2.45/0.98  fof(f35,plain,(
% 2.45/0.98    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.45/0.98    inference(flattening,[],[f34])).
% 2.45/0.98  
% 2.45/0.98  fof(f74,plain,(
% 2.45/0.98    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.45/0.98    inference(cnf_transformation,[],[f35])).
% 2.45/0.98  
% 2.45/0.98  fof(f17,axiom,(
% 2.45/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 2.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f38,plain,(
% 2.45/0.98    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) | (~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.45/0.98    inference(ennf_transformation,[],[f17])).
% 2.45/0.98  
% 2.45/0.98  fof(f39,plain,(
% 2.45/0.98    ! [X0] : (! [X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.45/0.98    inference(flattening,[],[f38])).
% 2.45/0.98  
% 2.45/0.98  fof(f76,plain,(
% 2.45/0.98    ( ! [X0,X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.45/0.98    inference(cnf_transformation,[],[f39])).
% 2.45/0.98  
% 2.45/0.98  fof(f11,axiom,(
% 2.45/0.98    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 2.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f28,plain,(
% 2.45/0.98    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 2.45/0.98    inference(ennf_transformation,[],[f11])).
% 2.45/0.98  
% 2.45/0.98  fof(f29,plain,(
% 2.45/0.98    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 2.45/0.98    inference(flattening,[],[f28])).
% 2.45/0.98  
% 2.45/0.98  fof(f66,plain,(
% 2.45/0.98    ( ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 2.45/0.98    inference(cnf_transformation,[],[f29])).
% 2.45/0.98  
% 2.45/0.98  fof(f77,plain,(
% 2.45/0.98    ~v2_struct_0(sK1)),
% 2.45/0.98    inference(cnf_transformation,[],[f53])).
% 2.45/0.98  
% 2.45/0.98  fof(f67,plain,(
% 2.45/0.98    ( ! [X0,X1] : (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.45/0.98    inference(cnf_transformation,[],[f43])).
% 2.45/0.98  
% 2.45/0.98  fof(f13,axiom,(
% 2.45/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 2.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f31,plain,(
% 2.45/0.98    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.45/0.98    inference(ennf_transformation,[],[f13])).
% 2.45/0.98  
% 2.45/0.98  fof(f44,plain,(
% 2.45/0.98    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.45/0.98    inference(nnf_transformation,[],[f31])).
% 2.45/0.98  
% 2.45/0.98  fof(f70,plain,(
% 2.45/0.98    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.45/0.98    inference(cnf_transformation,[],[f44])).
% 2.45/0.98  
% 2.45/0.98  fof(f82,plain,(
% 2.45/0.98    ~v1_subset_1(sK2,u1_struct_0(sK1)) | v3_tex_2(sK2,sK1)),
% 2.45/0.98    inference(cnf_transformation,[],[f53])).
% 2.45/0.98  
% 2.45/0.98  fof(f16,axiom,(
% 2.45/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 2.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/0.98  
% 2.45/0.98  fof(f36,plain,(
% 2.45/0.98    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.45/0.98    inference(ennf_transformation,[],[f16])).
% 2.45/0.98  
% 2.45/0.98  fof(f37,plain,(
% 2.45/0.98    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.45/0.98    inference(flattening,[],[f36])).
% 2.45/0.98  
% 2.45/0.98  fof(f75,plain,(
% 2.45/0.98    ( ! [X0,X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.45/0.98    inference(cnf_transformation,[],[f37])).
% 2.45/0.98  
% 2.45/0.98  cnf(c_3,plain,
% 2.45/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.45/0.98      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 2.45/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1073,plain,
% 2.45/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.45/0.98      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 2.45/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_25,negated_conjecture,
% 2.45/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.45/0.98      inference(cnf_transformation,[],[f81]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1071,plain,
% 2.45/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.45/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_9,plain,
% 2.45/0.98      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.45/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_6,plain,
% 2.45/0.98      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.45/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_383,plain,
% 2.45/0.98      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.45/0.98      inference(resolution,[status(thm)],[c_9,c_6]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_26,negated_conjecture,
% 2.45/0.98      ( l1_pre_topc(sK1) ),
% 2.45/0.98      inference(cnf_transformation,[],[f80]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_706,plain,
% 2.45/0.98      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.45/0.98      inference(resolution_lifted,[status(thm)],[c_383,c_26]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_707,plain,
% 2.45/0.98      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.45/0.98      inference(unflattening,[status(thm)],[c_706]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1082,plain,
% 2.45/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 2.45/0.98      inference(light_normalisation,[status(thm)],[c_1071,c_707]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1,plain,
% 2.45/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.45/0.98      | k4_xboole_0(X1,X0) = k3_subset_1(X1,X0) ),
% 2.45/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1075,plain,
% 2.45/0.98      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
% 2.45/0.98      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.45/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1399,plain,
% 2.45/0.98      ( k4_xboole_0(k2_struct_0(sK1),sK2) = k3_subset_1(k2_struct_0(sK1),sK2) ),
% 2.45/0.98      inference(superposition,[status(thm)],[c_1082,c_1075]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_2,plain,
% 2.45/0.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.45/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1074,plain,
% 2.45/0.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.45/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_0,plain,
% 2.45/0.98      ( k2_subset_1(X0) = X0 ),
% 2.45/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1085,plain,
% 2.45/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.45/0.98      inference(light_normalisation,[status(thm)],[c_1074,c_0]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_4,plain,
% 2.45/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.45/0.98      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 2.45/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1072,plain,
% 2.45/0.98      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 2.45/0.98      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.45/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1455,plain,
% 2.45/0.98      ( k7_subset_1(X0,X0,X1) = k4_xboole_0(X0,X1) ),
% 2.45/0.98      inference(superposition,[status(thm)],[c_1085,c_1072]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_19,plain,
% 2.45/0.98      ( v3_pre_topc(X0,X1)
% 2.45/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/0.98      | ~ v1_tdlat_3(X1)
% 2.45/0.98      | ~ v2_pre_topc(X1)
% 2.45/0.98      | ~ l1_pre_topc(X1) ),
% 2.45/0.98      inference(cnf_transformation,[],[f71]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_717,plain,
% 2.45/0.98      ( v3_pre_topc(X0,X1)
% 2.45/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/0.98      | ~ v1_tdlat_3(X1)
% 2.45/0.98      | ~ v2_pre_topc(X1)
% 2.45/0.98      | sK1 != X1 ),
% 2.45/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_26]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_718,plain,
% 2.45/0.98      ( v3_pre_topc(X0,sK1)
% 2.45/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.45/0.98      | ~ v1_tdlat_3(sK1)
% 2.45/0.98      | ~ v2_pre_topc(sK1) ),
% 2.45/0.98      inference(unflattening,[status(thm)],[c_717]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_28,negated_conjecture,
% 2.45/0.98      ( v2_pre_topc(sK1) ),
% 2.45/0.98      inference(cnf_transformation,[],[f78]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_27,negated_conjecture,
% 2.45/0.98      ( v1_tdlat_3(sK1) ),
% 2.45/0.98      inference(cnf_transformation,[],[f79]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_722,plain,
% 2.45/0.98      ( v3_pre_topc(X0,sK1) | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.45/0.98      inference(global_propositional_subsumption,
% 2.45/0.98                [status(thm)],
% 2.45/0.98                [c_718,c_28,c_27]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_7,plain,
% 2.45/0.98      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
% 2.45/0.98      | v4_pre_topc(X1,X0)
% 2.45/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.45/0.98      | ~ l1_pre_topc(X0) ),
% 2.45/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_11,plain,
% 2.45/0.98      ( ~ v4_pre_topc(X0,X1)
% 2.45/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/0.98      | ~ l1_pre_topc(X1)
% 2.45/0.98      | k2_pre_topc(X1,X0) = X0 ),
% 2.45/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_620,plain,
% 2.45/0.98      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
% 2.45/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.45/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.45/0.98      | ~ l1_pre_topc(X0)
% 2.45/0.98      | ~ l1_pre_topc(X3)
% 2.45/0.98      | X2 != X1
% 2.45/0.98      | X3 != X0
% 2.45/0.98      | k2_pre_topc(X3,X2) = X2 ),
% 2.45/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_11]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_621,plain,
% 2.45/0.98      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
% 2.45/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.45/0.98      | ~ l1_pre_topc(X0)
% 2.45/0.98      | k2_pre_topc(X0,X1) = X1 ),
% 2.45/0.98      inference(unflattening,[status(thm)],[c_620]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_691,plain,
% 2.45/0.98      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
% 2.45/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.45/0.98      | k2_pre_topc(X0,X1) = X1
% 2.45/0.98      | sK1 != X0 ),
% 2.45/0.98      inference(resolution_lifted,[status(thm)],[c_621,c_26]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_692,plain,
% 2.45/0.98      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0),sK1)
% 2.45/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.45/0.98      | k2_pre_topc(sK1,X0) = X0 ),
% 2.45/0.98      inference(unflattening,[status(thm)],[c_691]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_800,plain,
% 2.45/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.45/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.45/0.98      | k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X1) != X0
% 2.45/0.98      | k2_pre_topc(sK1,X1) = X1
% 2.45/0.98      | sK1 != sK1 ),
% 2.45/0.98      inference(resolution_lifted,[status(thm)],[c_722,c_692]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_801,plain,
% 2.45/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.45/0.98      | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.45/0.98      | k2_pre_topc(sK1,X0) = X0 ),
% 2.45/0.98      inference(unflattening,[status(thm)],[c_800]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1070,plain,
% 2.45/0.98      ( k2_pre_topc(sK1,X0) = X0
% 2.45/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.45/0.98      | m1_subset_1(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.45/0.98      inference(predicate_to_equality,[status(thm)],[c_801]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1115,plain,
% 2.45/0.98      ( k2_pre_topc(sK1,X0) = X0
% 2.45/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 2.45/0.98      | m1_subset_1(k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),X0),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 2.45/0.98      inference(light_normalisation,[status(thm)],[c_1070,c_707]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1631,plain,
% 2.45/0.98      ( k2_pre_topc(sK1,X0) = X0
% 2.45/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 2.45/0.98      | m1_subset_1(k4_xboole_0(k2_struct_0(sK1),X0),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 2.45/0.98      inference(demodulation,[status(thm)],[c_1455,c_1115]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1640,plain,
% 2.45/0.98      ( k2_pre_topc(sK1,sK2) = sK2
% 2.45/0.98      | m1_subset_1(k3_subset_1(k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 2.45/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 2.45/0.98      inference(superposition,[status(thm)],[c_1399,c_1631]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1717,plain,
% 2.45/0.98      ( m1_subset_1(k3_subset_1(k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 2.45/0.98      | k2_pre_topc(sK1,sK2) = sK2 ),
% 2.45/0.98      inference(global_propositional_subsumption,[status(thm)],[c_1640,c_1082]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1718,plain,
% 2.45/0.98      ( k2_pre_topc(sK1,sK2) = sK2
% 2.45/0.98      | m1_subset_1(k3_subset_1(k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 2.45/0.98      inference(renaming,[status(thm)],[c_1717]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1723,plain,
% 2.45/0.98      ( k2_pre_topc(sK1,sK2) = sK2
% 2.45/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 2.45/0.98      inference(superposition,[status(thm)],[c_1073,c_1718]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1827,plain,
% 2.45/0.98      ( k2_pre_topc(sK1,sK2) = sK2 ),
% 2.45/0.98      inference(global_propositional_subsumption,[status(thm)],[c_1723,c_1082]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_13,plain,
% 2.45/0.98      ( v1_tops_1(X0,X1)
% 2.45/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/0.98      | ~ l1_pre_topc(X1)
% 2.45/0.98      | k2_pre_topc(X1,X0) != u1_struct_0(X1) ),
% 2.45/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_750,plain,
% 2.45/0.98      ( v1_tops_1(X0,X1)
% 2.45/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/0.98      | k2_pre_topc(X1,X0) != u1_struct_0(X1)
% 2.45/0.98      | sK1 != X1 ),
% 2.45/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_26]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_751,plain,
% 2.45/0.98      ( v1_tops_1(X0,sK1)
% 2.45/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.45/0.98      | k2_pre_topc(sK1,X0) != u1_struct_0(sK1) ),
% 2.45/0.98      inference(unflattening,[status(thm)],[c_750]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_5,plain,
% 2.45/0.98      ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
% 2.45/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_23,negated_conjecture,
% 2.45/0.98      ( ~ v3_tex_2(sK2,sK1) | v1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.45/0.98      inference(cnf_transformation,[],[f83]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_224,plain,
% 2.45/0.98      ( ~ v3_tex_2(sK2,sK1) | v1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.45/0.98      inference(prop_impl,[status(thm)],[c_23]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_498,plain,
% 2.45/0.98      ( ~ v3_tex_2(sK2,sK1) | u1_struct_0(sK1) != X0 | k2_subset_1(X0) != sK2 ),
% 2.45/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_224]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_499,plain,
% 2.45/0.98      ( ~ v3_tex_2(sK2,sK1) | k2_subset_1(u1_struct_0(sK1)) != sK2 ),
% 2.45/0.98      inference(unflattening,[status(thm)],[c_498]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_20,plain,
% 2.45/0.98      ( v2_tex_2(X0,X1)
% 2.45/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/0.98      | v2_struct_0(X1)
% 2.45/0.98      | ~ v1_tdlat_3(X1)
% 2.45/0.98      | ~ v2_pre_topc(X1)
% 2.45/0.98      | ~ l1_pre_topc(X1) ),
% 2.45/0.98      inference(cnf_transformation,[],[f74]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_22,plain,
% 2.45/0.98      ( v3_tex_2(X0,X1)
% 2.45/0.98      | ~ v2_tex_2(X0,X1)
% 2.45/0.98      | ~ v1_tops_1(X0,X1)
% 2.45/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/0.98      | v2_struct_0(X1)
% 2.45/0.98      | ~ v2_pre_topc(X1)
% 2.45/0.98      | ~ l1_pre_topc(X1) ),
% 2.45/0.98      inference(cnf_transformation,[],[f76]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_397,plain,
% 2.45/0.98      ( v3_tex_2(X0,X1)
% 2.45/0.98      | ~ v1_tops_1(X0,X1)
% 2.45/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/0.98      | v2_struct_0(X1)
% 2.45/0.98      | ~ v1_tdlat_3(X1)
% 2.45/0.98      | ~ v2_pre_topc(X1)
% 2.45/0.98      | ~ l1_pre_topc(X1) ),
% 2.45/0.98      inference(resolution,[status(thm)],[c_20,c_22]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_12,plain,
% 2.45/0.98      ( ~ v1_tdlat_3(X0) | v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 2.45/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_415,plain,
% 2.45/0.98      ( v3_tex_2(X0,X1)
% 2.45/0.98      | ~ v1_tops_1(X0,X1)
% 2.45/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/0.98      | v2_struct_0(X1)
% 2.45/0.98      | ~ v1_tdlat_3(X1)
% 2.45/0.98      | ~ l1_pre_topc(X1) ),
% 2.45/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_397,c_12]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_29,negated_conjecture,
% 2.45/0.98      ( ~ v2_struct_0(sK1) ),
% 2.45/0.98      inference(cnf_transformation,[],[f77]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_432,plain,
% 2.45/0.98      ( v3_tex_2(X0,X1)
% 2.45/0.98      | ~ v1_tops_1(X0,X1)
% 2.45/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/0.98      | ~ v1_tdlat_3(X1)
% 2.45/0.98      | ~ l1_pre_topc(X1)
% 2.45/0.98      | sK1 != X1 ),
% 2.45/0.98      inference(resolution_lifted,[status(thm)],[c_415,c_29]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_433,plain,
% 2.45/0.98      ( v3_tex_2(X0,sK1)
% 2.45/0.98      | ~ v1_tops_1(X0,sK1)
% 2.45/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.45/0.98      | ~ v1_tdlat_3(sK1)
% 2.45/0.98      | ~ l1_pre_topc(sK1) ),
% 2.45/0.98      inference(unflattening,[status(thm)],[c_432]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_437,plain,
% 2.45/0.98      ( v3_tex_2(X0,sK1)
% 2.45/0.98      | ~ v1_tops_1(X0,sK1)
% 2.45/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.45/0.98      inference(global_propositional_subsumption,
% 2.45/0.98                [status(thm)],
% 2.45/0.98                [c_433,c_27,c_26]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_591,plain,
% 2.45/0.98      ( ~ v1_tops_1(X0,sK1)
% 2.45/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.45/0.98      | k2_subset_1(u1_struct_0(sK1)) != sK2
% 2.45/0.98      | sK1 != sK1
% 2.45/0.98      | sK2 != X0 ),
% 2.45/0.98      inference(resolution_lifted,[status(thm)],[c_499,c_437]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_592,plain,
% 2.45/0.98      ( ~ v1_tops_1(sK2,sK1)
% 2.45/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.45/0.98      | k2_subset_1(u1_struct_0(sK1)) != sK2 ),
% 2.45/0.98      inference(unflattening,[status(thm)],[c_591]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_594,plain,
% 2.45/0.98      ( ~ v1_tops_1(sK2,sK1) | k2_subset_1(u1_struct_0(sK1)) != sK2 ),
% 2.45/0.98      inference(global_propositional_subsumption,[status(thm)],[c_592,c_25]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_831,plain,
% 2.45/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.45/0.98      | k2_pre_topc(sK1,X0) != u1_struct_0(sK1)
% 2.45/0.98      | k2_subset_1(u1_struct_0(sK1)) != sK2
% 2.45/0.98      | sK1 != sK1
% 2.45/0.98      | sK2 != X0 ),
% 2.45/0.98      inference(resolution_lifted,[status(thm)],[c_751,c_594]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_832,plain,
% 2.45/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.45/0.98      | k2_pre_topc(sK1,sK2) != u1_struct_0(sK1)
% 2.45/0.98      | k2_subset_1(u1_struct_0(sK1)) != sK2 ),
% 2.45/0.98      inference(unflattening,[status(thm)],[c_831]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_834,plain,
% 2.45/0.98      ( k2_pre_topc(sK1,sK2) != u1_struct_0(sK1)
% 2.45/0.98      | k2_subset_1(u1_struct_0(sK1)) != sK2 ),
% 2.45/0.98      inference(global_propositional_subsumption,[status(thm)],[c_832,c_25]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1096,plain,
% 2.45/0.98      ( k2_pre_topc(sK1,sK2) != k2_struct_0(sK1)
% 2.45/0.98      | k2_subset_1(k2_struct_0(sK1)) != sK2 ),
% 2.45/0.98      inference(light_normalisation,[status(thm)],[c_834,c_707]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1097,plain,
% 2.45/0.98      ( k2_pre_topc(sK1,sK2) != k2_struct_0(sK1) | k2_struct_0(sK1) != sK2 ),
% 2.45/0.98      inference(demodulation,[status(thm)],[c_1096,c_0]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_1830,plain,
% 2.45/0.98      ( k2_struct_0(sK1) != sK2 ),
% 2.45/0.98      inference(demodulation,[status(thm)],[c_1827,c_1097]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_14,plain,
% 2.45/0.98      ( ~ v1_tops_1(X0,X1)
% 2.45/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/0.98      | ~ l1_pre_topc(X1)
% 2.45/0.98      | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
% 2.45/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_735,plain,
% 2.45/0.98      ( ~ v1_tops_1(X0,X1)
% 2.45/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/0.98      | k2_pre_topc(X1,X0) = u1_struct_0(X1)
% 2.45/0.98      | sK1 != X1 ),
% 2.45/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_26]) ).
% 2.45/0.98  
% 2.45/0.98  cnf(c_736,plain,
% 2.45/0.98      ( ~ v1_tops_1(X0,sK1)
% 2.45/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.45/0.99      | k2_pre_topc(sK1,X0) = u1_struct_0(sK1) ),
% 2.45/0.99      inference(unflattening,[status(thm)],[c_735]) ).
% 2.45/0.99  
% 2.45/0.99  cnf(c_15,plain,
% 2.45/0.99      ( v1_subset_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | X0 = X1 ),
% 2.45/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.45/0.99  
% 2.45/0.99  cnf(c_24,negated_conjecture,
% 2.45/0.99      ( v3_tex_2(sK2,sK1) | ~ v1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.45/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.45/0.99  
% 2.45/0.99  cnf(c_222,plain,
% 2.45/0.99      ( v3_tex_2(sK2,sK1) | ~ v1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.45/0.99      inference(prop_impl,[status(thm)],[c_24]) ).
% 2.45/0.99  
% 2.45/0.99  cnf(c_510,plain,
% 2.45/0.99      ( v3_tex_2(sK2,sK1)
% 2.45/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.45/0.99      | X1 = X0
% 2.45/0.99      | u1_struct_0(sK1) != X1
% 2.45/0.99      | sK2 != X0 ),
% 2.45/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_222]) ).
% 2.45/0.99  
% 2.45/0.99  cnf(c_511,plain,
% 2.45/0.99      ( v3_tex_2(sK2,sK1)
% 2.45/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.45/0.99      | u1_struct_0(sK1) = sK2 ),
% 2.45/0.99      inference(unflattening,[status(thm)],[c_510]) ).
% 2.45/0.99  
% 2.45/0.99  cnf(c_513,plain,
% 2.45/0.99      ( v3_tex_2(sK2,sK1) | u1_struct_0(sK1) = sK2 ),
% 2.45/0.99      inference(global_propositional_subsumption,[status(thm)],[c_511,c_25]) ).
% 2.45/0.99  
% 2.45/0.99  cnf(c_21,plain,
% 2.45/0.99      ( ~ v3_tex_2(X0,X1)
% 2.45/0.99      | v1_tops_1(X0,X1)
% 2.45/0.99      | ~ v3_pre_topc(X0,X1)
% 2.45/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/0.99      | v2_struct_0(X1)
% 2.45/0.99      | ~ v2_pre_topc(X1)
% 2.45/0.99      | ~ l1_pre_topc(X1) ),
% 2.45/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.45/0.99  
% 2.45/0.99  cnf(c_453,plain,
% 2.45/0.99      ( ~ v3_tex_2(X0,X1)
% 2.45/0.99      | v1_tops_1(X0,X1)
% 2.45/0.99      | ~ v3_pre_topc(X0,X1)
% 2.45/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/0.99      | ~ v2_pre_topc(X1)
% 2.45/0.99      | ~ l1_pre_topc(X1)
% 2.45/0.99      | sK1 != X1 ),
% 2.45/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_29]) ).
% 2.45/0.99  
% 2.45/0.99  cnf(c_454,plain,
% 2.45/0.99      ( ~ v3_tex_2(X0,sK1)
% 2.45/0.99      | v1_tops_1(X0,sK1)
% 2.45/0.99      | ~ v3_pre_topc(X0,sK1)
% 2.45/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.45/0.99      | ~ v2_pre_topc(sK1)
% 2.45/0.99      | ~ l1_pre_topc(sK1) ),
% 2.45/0.99      inference(unflattening,[status(thm)],[c_453]) ).
% 2.45/0.99  
% 2.45/0.99  cnf(c_458,plain,
% 2.45/0.99      ( ~ v3_tex_2(X0,sK1)
% 2.45/0.99      | v1_tops_1(X0,sK1)
% 2.45/0.99      | ~ v3_pre_topc(X0,sK1)
% 2.45/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.45/0.99      inference(global_propositional_subsumption,
% 2.45/0.99                [status(thm)],
% 2.45/0.99                [c_454,c_28,c_26]) ).
% 2.45/0.99  
% 2.45/0.99  cnf(c_557,plain,
% 2.45/0.99      ( v1_tops_1(X0,sK1)
% 2.45/0.99      | ~ v3_pre_topc(X0,sK1)
% 2.45/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.45/0.99      | u1_struct_0(sK1) = sK2
% 2.45/0.99      | sK1 != sK1
% 2.45/0.99      | sK2 != X0 ),
% 2.45/0.99      inference(resolution_lifted,[status(thm)],[c_513,c_458]) ).
% 2.45/0.99  
% 2.45/0.99  cnf(c_558,plain,
% 2.45/0.99      ( v1_tops_1(sK2,sK1)
% 2.45/0.99      | ~ v3_pre_topc(sK2,sK1)
% 2.45/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.45/0.99      | u1_struct_0(sK1) = sK2 ),
% 2.45/0.99      inference(unflattening,[status(thm)],[c_557]) ).
% 2.45/0.99  
% 2.45/0.99  cnf(c_560,plain,
% 2.45/0.99      ( ~ v3_pre_topc(sK2,sK1) | v1_tops_1(sK2,sK1) | u1_struct_0(sK1) = sK2 ),
% 2.45/0.99      inference(global_propositional_subsumption,[status(thm)],[c_558,c_25]) ).
% 2.45/0.99  
% 2.45/0.99  cnf(c_561,plain,
% 2.45/0.99      ( v1_tops_1(sK2,sK1) | ~ v3_pre_topc(sK2,sK1) | u1_struct_0(sK1) = sK2 ),
% 2.45/0.99      inference(renaming,[status(thm)],[c_560]) ).
% 2.45/0.99  
% 2.45/0.99  cnf(c_786,plain,
% 2.45/0.99      ( v1_tops_1(sK2,sK1)
% 2.45/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.45/0.99      | u1_struct_0(sK1) = sK2
% 2.45/0.99      | sK1 != sK1
% 2.45/0.99      | sK2 != X0 ),
% 2.45/0.99      inference(resolution_lifted,[status(thm)],[c_722,c_561]) ).
% 2.45/0.99  
% 2.45/0.99  cnf(c_787,plain,
% 2.45/0.99      ( v1_tops_1(sK2,sK1)
% 2.45/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.45/0.99      | u1_struct_0(sK1) = sK2 ),
% 2.45/0.99      inference(unflattening,[status(thm)],[c_786]) ).
% 2.45/0.99  
% 2.45/0.99  cnf(c_789,plain,
% 2.45/0.99      ( v1_tops_1(sK2,sK1) | u1_struct_0(sK1) = sK2 ),
% 2.45/0.99      inference(global_propositional_subsumption,[status(thm)],[c_787,c_25]) ).
% 2.45/0.99  
% 2.45/0.99  cnf(c_859,plain,
% 2.45/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.45/0.99      | k2_pre_topc(sK1,X0) = u1_struct_0(sK1)
% 2.45/0.99      | u1_struct_0(sK1) = sK2
% 2.45/0.99      | sK1 != sK1
% 2.45/0.99      | sK2 != X0 ),
% 2.45/0.99      inference(resolution_lifted,[status(thm)],[c_736,c_789]) ).
% 2.45/0.99  
% 2.45/0.99  cnf(c_860,plain,
% 2.45/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.45/0.99      | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1)
% 2.45/0.99      | u1_struct_0(sK1) = sK2 ),
% 2.45/0.99      inference(unflattening,[status(thm)],[c_859]) ).
% 2.45/0.99  
% 2.45/0.99  cnf(c_862,plain,
% 2.45/0.99      ( k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) | u1_struct_0(sK1) = sK2 ),
% 2.45/0.99      inference(global_propositional_subsumption,[status(thm)],[c_860,c_25]) ).
% 2.45/0.99  
% 2.45/0.99  cnf(c_1088,plain,
% 2.45/0.99      ( k2_pre_topc(sK1,sK2) = k2_struct_0(sK1) | u1_struct_0(sK1) = sK2 ),
% 2.45/0.99      inference(light_normalisation,[status(thm)],[c_862,c_707]) ).
% 2.45/0.99  
% 2.45/0.99  cnf(c_1089,plain,
% 2.45/0.99      ( k2_pre_topc(sK1,sK2) = k2_struct_0(sK1) | k2_struct_0(sK1) = sK2 ),
% 2.45/0.99      inference(demodulation,[status(thm)],[c_1088,c_707]) ).
% 2.45/0.99  
% 2.45/0.99  cnf(c_1831,plain,
% 2.45/0.99      ( k2_struct_0(sK1) = sK2 ),
% 2.45/0.99      inference(demodulation,[status(thm)],[c_1827,c_1089]) ).
% 2.45/0.99  
% 2.45/0.99  cnf(c_1834,plain,
% 2.45/0.99      ( sK2 != sK2 ),
% 2.45/0.99      inference(light_normalisation,[status(thm)],[c_1830,c_1831]) ).
% 2.45/0.99  
% 2.45/0.99  cnf(c_1835,plain,
% 2.45/0.99      ( $false ),
% 2.45/0.99      inference(equality_resolution_simp,[status(thm)],[c_1834]) ).
% 2.45/0.99  
% 2.45/0.99  
% 2.45/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.45/0.99  
% 2.45/0.99  ------                               Statistics
% 2.45/0.99  
% 2.45/0.99  ------ General
% 2.45/0.99  
% 2.45/0.99  abstr_ref_over_cycles:                  0
% 2.45/0.99  abstr_ref_under_cycles:                 0
% 2.45/0.99  gc_basic_clause_elim:                   0
% 2.45/0.99  forced_gc_time:                         0
% 2.45/0.99  parsing_time:                           0.021
% 2.45/0.99  unif_index_cands_time:                  0.
% 2.45/0.99  unif_index_add_time:                    0.
% 2.45/0.99  orderings_time:                         0.
% 2.45/0.99  out_proof_time:                         0.012
% 2.45/0.99  total_time:                             0.102
% 2.45/0.99  num_of_symbols:                         54
% 2.45/0.99  num_of_terms:                           1385
% 2.45/0.99  
% 2.45/0.99  ------ Preprocessing
% 2.45/0.99  
% 2.45/0.99  num_of_splits:                          0
% 2.45/0.99  num_of_split_atoms:                     0
% 2.45/0.99  num_of_reused_defs:                     0
% 2.45/0.99  num_eq_ax_congr_red:                    28
% 2.45/0.99  num_of_sem_filtered_clauses:            1
% 2.45/0.99  num_of_subtypes:                        0
% 2.45/0.99  monotx_restored_types:                  0
% 2.45/0.99  sat_num_of_epr_types:                   0
% 2.45/0.99  sat_num_of_non_cyclic_types:            0
% 2.45/0.99  sat_guarded_non_collapsed_types:        0
% 2.45/0.99  num_pure_diseq_elim:                    0
% 2.45/0.99  simp_replaced_by:                       0
% 2.45/0.99  res_preprocessed:                       88
% 2.45/0.99  prep_upred:                             0
% 2.45/0.99  prep_unflattend:                        31
% 2.45/0.99  smt_new_axioms:                         0
% 2.45/0.99  pred_elim_cands:                        1
% 2.45/0.99  pred_elim:                              11
% 2.45/0.99  pred_elim_cl:                           17
% 2.45/0.99  pred_elim_cycles:                       13
% 2.45/0.99  merged_defs:                            2
% 2.45/0.99  merged_defs_ncl:                        0
% 2.45/0.99  bin_hyper_res:                          2
% 2.45/0.99  prep_cycles:                            4
% 2.45/0.99  pred_elim_time:                         0.009
% 2.45/0.99  splitting_time:                         0.
% 2.45/0.99  sem_filter_time:                        0.
% 2.45/0.99  monotx_time:                            0.001
% 2.45/0.99  subtype_inf_time:                       0.
% 2.45/0.99  
% 2.45/0.99  ------ Problem properties
% 2.45/0.99  
% 2.45/0.99  clauses:                                13
% 2.45/0.99  conjectures:                            1
% 2.45/0.99  epr:                                    0
% 2.45/0.99  horn:                                   12
% 2.45/0.99  ground:                                 6
% 2.45/0.99  unary:                                  5
% 2.45/0.99  binary:                                 6
% 2.45/0.99  lits:                                   23
% 2.45/0.99  lits_eq:                                14
% 2.45/0.99  fd_pure:                                0
% 2.45/0.99  fd_pseudo:                              0
% 2.45/0.99  fd_cond:                                0
% 2.45/0.99  fd_pseudo_cond:                         0
% 2.45/0.99  ac_symbols:                             0
% 2.45/0.99  
% 2.45/0.99  ------ Propositional Solver
% 2.45/0.99  
% 2.45/0.99  prop_solver_calls:                      26
% 2.45/0.99  prop_fast_solver_calls:                 567
% 2.45/0.99  smt_solver_calls:                       0
% 2.45/0.99  smt_fast_solver_calls:                  0
% 2.45/0.99  prop_num_of_clauses:                    545
% 2.45/0.99  prop_preprocess_simplified:             2459
% 2.45/0.99  prop_fo_subsumed:                       22
% 2.45/0.99  prop_solver_time:                       0.
% 2.45/0.99  smt_solver_time:                        0.
% 2.45/0.99  smt_fast_solver_time:                   0.
% 2.45/0.99  prop_fast_solver_time:                  0.
% 2.45/0.99  prop_unsat_core_time:                   0.
% 2.45/0.99  
% 2.45/0.99  ------ QBF
% 2.45/0.99  
% 2.45/0.99  qbf_q_res:                              0
% 2.45/0.99  qbf_num_tautologies:                    0
% 2.45/0.99  qbf_prep_cycles:                        0
% 2.45/0.99  
% 2.45/0.99  ------ BMC1
% 2.45/0.99  
% 2.45/0.99  bmc1_current_bound:                     -1
% 2.45/0.99  bmc1_last_solved_bound:                 -1
% 2.45/0.99  bmc1_unsat_core_size:                   -1
% 2.45/0.99  bmc1_unsat_core_parents_size:           -1
% 2.45/0.99  bmc1_merge_next_fun:                    0
% 2.45/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.45/0.99  
% 2.45/0.99  ------ Instantiation
% 2.45/0.99  
% 2.45/0.99  inst_num_of_clauses:                    157
% 2.45/0.99  inst_num_in_passive:                    2
% 2.45/0.99  inst_num_in_active:                     95
% 2.45/0.99  inst_num_in_unprocessed:                60
% 2.45/0.99  inst_num_of_loops:                      100
% 2.45/0.99  inst_num_of_learning_restarts:          0
% 2.45/0.99  inst_num_moves_active_passive:          3
% 2.45/0.99  inst_lit_activity:                      0
% 2.45/0.99  inst_lit_activity_moves:                0
% 2.45/0.99  inst_num_tautologies:                   0
% 2.45/0.99  inst_num_prop_implied:                  0
% 2.45/0.99  inst_num_existing_simplified:           0
% 2.45/0.99  inst_num_eq_res_simplified:             0
% 2.45/0.99  inst_num_child_elim:                    0
% 2.45/0.99  inst_num_of_dismatching_blockings:      88
% 2.45/0.99  inst_num_of_non_proper_insts:           143
% 2.45/0.99  inst_num_of_duplicates:                 0
% 2.45/0.99  inst_inst_num_from_inst_to_res:         0
% 2.45/0.99  inst_dismatching_checking_time:         0.
% 2.45/0.99  
% 2.45/0.99  ------ Resolution
% 2.45/0.99  
% 2.45/0.99  res_num_of_clauses:                     0
% 2.45/0.99  res_num_in_passive:                     0
% 2.45/0.99  res_num_in_active:                      0
% 2.45/0.99  res_num_of_loops:                       92
% 2.45/0.99  res_forward_subset_subsumed:            25
% 2.45/0.99  res_backward_subset_subsumed:           0
% 2.45/0.99  res_forward_subsumed:                   1
% 2.45/0.99  res_backward_subsumed:                  0
% 2.45/0.99  res_forward_subsumption_resolution:     1
% 2.45/0.99  res_backward_subsumption_resolution:    0
% 2.45/0.99  res_clause_to_clause_subsumption:       69
% 2.45/0.99  res_orphan_elimination:                 0
% 2.45/0.99  res_tautology_del:                      26
% 2.45/0.99  res_num_eq_res_simplified:              0
% 2.45/0.99  res_num_sel_changes:                    0
% 2.45/0.99  res_moves_from_active_to_pass:          0
% 2.45/0.99  
% 2.45/0.99  ------ Superposition
% 2.45/0.99  
% 2.45/0.99  sup_time_total:                         0.
% 2.45/0.99  sup_time_generating:                    0.
% 2.45/0.99  sup_time_sim_full:                      0.
% 2.45/0.99  sup_time_sim_immed:                     0.
% 2.45/0.99  
% 2.45/0.99  sup_num_of_clauses:                     18
% 2.45/0.99  sup_num_in_active:                      14
% 2.45/0.99  sup_num_in_passive:                     4
% 2.45/0.99  sup_num_of_loops:                       18
% 2.45/0.99  sup_fw_superposition:                   10
% 2.45/0.99  sup_bw_superposition:                   0
% 2.45/0.99  sup_immediate_simplified:               0
% 2.45/0.99  sup_given_eliminated:                   0
% 2.45/0.99  comparisons_done:                       0
% 2.45/0.99  comparisons_avoided:                    0
% 2.45/0.99  
% 2.45/0.99  ------ Simplifications
% 2.45/0.99  
% 2.45/0.99  
% 2.45/0.99  sim_fw_subset_subsumed:                 0
% 2.45/0.99  sim_bw_subset_subsumed:                 1
% 2.45/0.99  sim_fw_subsumed:                        1
% 2.45/0.99  sim_bw_subsumed:                        0
% 2.45/0.99  sim_fw_subsumption_res:                 2
% 2.45/0.99  sim_bw_subsumption_res:                 0
% 2.45/0.99  sim_tautology_del:                      2
% 2.45/0.99  sim_eq_tautology_del:                   0
% 2.45/0.99  sim_eq_res_simp:                        0
% 2.45/0.99  sim_fw_demodulated:                     3
% 2.45/0.99  sim_bw_demodulated:                     3
% 2.45/0.99  sim_light_normalised:                   8
% 2.45/0.99  sim_joinable_taut:                      0
% 2.45/0.99  sim_joinable_simp:                      0
% 2.45/0.99  sim_ac_normalised:                      0
% 2.45/0.99  sim_smt_subsumption:                    0
% 2.45/0.99  
%------------------------------------------------------------------------------
