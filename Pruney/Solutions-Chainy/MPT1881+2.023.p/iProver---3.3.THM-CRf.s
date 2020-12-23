%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:14 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :  200 (2508 expanded)
%              Number of clauses        :  118 ( 721 expanded)
%              Number of leaves         :   22 ( 543 expanded)
%              Depth                    :   24
%              Number of atoms          :  751 (13640 expanded)
%              Number of equality atoms :  157 ( 741 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

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
    inference(ennf_transformation,[],[f18])).

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

fof(f56,plain,(
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

fof(f57,plain,(
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
    inference(flattening,[],[f56])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( v1_subset_1(sK4,u1_struct_0(X0))
          | ~ v3_tex_2(sK4,X0) )
        & ( ~ v1_subset_1(sK4,u1_struct_0(X0))
          | v3_tex_2(sK4,X0) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
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
          ( ( v1_subset_1(X1,u1_struct_0(sK3))
            | ~ v3_tex_2(X1,sK3) )
          & ( ~ v1_subset_1(X1,u1_struct_0(sK3))
            | v3_tex_2(X1,sK3) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) )
      & l1_pre_topc(sK3)
      & v1_tdlat_3(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( ( v1_subset_1(sK4,u1_struct_0(sK3))
      | ~ v3_tex_2(sK4,sK3) )
    & ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
      | v3_tex_2(sK4,sK3) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & l1_pre_topc(sK3)
    & v1_tdlat_3(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f57,f59,f58])).

fof(f92,plain,
    ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
    | v3_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f91,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f60])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK1(X0),X0)
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f49,f50])).

fof(f77,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

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

fof(f85,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f72,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f87,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f89,plain,(
    v1_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f90,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f67,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f66,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f73,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => v1_tops_1(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( v1_tops_1(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f70,plain,(
    ! [X0] :
      ( v1_tops_1(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_subset_1(sK0(X0),X0)
        & m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK0(X0),X0)
      & m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f2,f42])).

fof(f62,plain,(
    ! [X0] : m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f63,plain,(
    ! [X0] : ~ v1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f43])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X2,X1)
                 => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f52])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1)
        & r1_tarski(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1)
                & r1_tarski(sK2(X0,X1),X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f53,f54])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
      | ~ r1_tarski(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f88,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

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

fof(f84,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f93,plain,
    ( v1_subset_1(sK4,u1_struct_0(sK3))
    | ~ v3_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

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

fof(f86,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | u1_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_251,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_14,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_253,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_318,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_subset_1(X0,X1)
    | X0 = X1 ),
    inference(bin_hyper_res,[status(thm)],[c_14,c_253])).

cnf(c_27,negated_conjecture,
    ( v3_tex_2(sK4,sK3)
    | ~ v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_255,plain,
    ( v3_tex_2(sK4,sK3)
    | ~ v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(prop_impl,[status(thm)],[c_27])).

cnf(c_480,plain,
    ( v3_tex_2(sK4,sK3)
    | ~ r1_tarski(X0,X1)
    | X1 = X0
    | u1_struct_0(sK3) != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_318,c_255])).

cnf(c_481,plain,
    ( v3_tex_2(sK4,sK3)
    | ~ r1_tarski(sK4,u1_struct_0(sK3))
    | u1_struct_0(sK3) = sK4 ),
    inference(unflattening,[status(thm)],[c_480])).

cnf(c_834,plain,
    ( v3_tex_2(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | u1_struct_0(sK3) != X1
    | u1_struct_0(sK3) = sK4
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_251,c_481])).

cnf(c_835,plain,
    ( v3_tex_2(sK4,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | u1_struct_0(sK3) = sK4 ),
    inference(unflattening,[status(thm)],[c_834])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_837,plain,
    ( v3_tex_2(sK4,sK3)
    | u1_struct_0(sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_835,c_28])).

cnf(c_18,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_24,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ v3_pre_topc(X0,X1)
    | v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_520,plain,
    ( ~ v3_tex_2(X0,X1)
    | v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_18,c_24])).

cnf(c_11,plain,
    ( ~ v1_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_538,plain,
    ( ~ v3_tex_2(X0,X1)
    | v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_520,c_11])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_668,plain,
    ( ~ v3_tex_2(X0,X1)
    | v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_538,c_32])).

cnf(c_669,plain,
    ( ~ v3_tex_2(X0,sK3)
    | v1_tops_1(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_tdlat_3(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_668])).

cnf(c_30,negated_conjecture,
    ( v1_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_611,plain,
    ( ~ v3_tex_2(X0,X1)
    | v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_538,c_30])).

cnf(c_612,plain,
    ( ~ v3_tex_2(X0,sK3)
    | v1_tops_1(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_611])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_616,plain,
    ( ~ v3_tex_2(X0,sK3)
    | v1_tops_1(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_612,c_32,c_29])).

cnf(c_671,plain,
    ( ~ v3_tex_2(X0,sK3)
    | v1_tops_1(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_669,c_32,c_29,c_612])).

cnf(c_995,plain,
    ( v1_tops_1(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | u1_struct_0(sK3) = sK4
    | sK3 != sK3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_837,c_671])).

cnf(c_996,plain,
    ( v1_tops_1(sK4,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | u1_struct_0(sK3) = sK4 ),
    inference(unflattening,[status(thm)],[c_995])).

cnf(c_998,plain,
    ( v1_tops_1(sK4,sK3)
    | u1_struct_0(sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_996,c_28])).

cnf(c_1401,plain,
    ( u1_struct_0(sK3) = sK4
    | v1_tops_1(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_998])).

cnf(c_1410,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_8,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_930,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = k2_struct_0(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_29])).

cnf(c_931,plain,
    ( ~ v1_tops_1(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK3,X0) = k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_930])).

cnf(c_1403,plain,
    ( k2_pre_topc(sK3,X0) = k2_struct_0(sK3)
    | v1_tops_1(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_931])).

cnf(c_1621,plain,
    ( k2_pre_topc(sK3,sK4) = k2_struct_0(sK3)
    | v1_tops_1(sK4,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1410,c_1403])).

cnf(c_1833,plain,
    ( k2_pre_topc(sK3,sK4) = k2_struct_0(sK3)
    | u1_struct_0(sK3) = sK4 ),
    inference(superposition,[status(thm)],[c_1401,c_1621])).

cnf(c_6,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_5,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_441,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_6,c_5])).

cnf(c_867,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_441,c_29])).

cnf(c_868,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_867])).

cnf(c_1408,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_868])).

cnf(c_13,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_900,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = u1_struct_0(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_29])).

cnf(c_901,plain,
    ( ~ v1_tops_1(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK3,X0) = u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_900])).

cnf(c_1405,plain,
    ( k2_pre_topc(sK3,X0) = u1_struct_0(sK3)
    | v1_tops_1(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_901])).

cnf(c_1698,plain,
    ( k2_pre_topc(sK3,k2_struct_0(sK3)) = u1_struct_0(sK3)
    | v1_tops_1(k2_struct_0(sK3),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1408,c_1405])).

cnf(c_9,plain,
    ( v1_tops_1(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_81,plain,
    ( v1_tops_1(k2_struct_0(sK3),sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_90,plain,
    ( ~ l1_pre_topc(sK3)
    | l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_93,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1511,plain,
    ( ~ v1_tops_1(k2_struct_0(sK3),sK3)
    | ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK3,k2_struct_0(sK3)) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_901])).

cnf(c_2195,plain,
    ( k2_pre_topc(sK3,k2_struct_0(sK3)) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1698,c_29,c_81,c_90,c_93,c_1511])).

cnf(c_1622,plain,
    ( k2_pre_topc(sK3,k2_struct_0(sK3)) = k2_struct_0(sK3)
    | v1_tops_1(k2_struct_0(sK3),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1408,c_1403])).

cnf(c_1518,plain,
    ( ~ v1_tops_1(k2_struct_0(sK3),sK3)
    | ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK3,k2_struct_0(sK3)) = k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_931])).

cnf(c_2130,plain,
    ( k2_pre_topc(sK3,k2_struct_0(sK3)) = k2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1622,c_29,c_81,c_90,c_93,c_1518])).

cnf(c_2197,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(light_normalisation,[status(thm)],[c_2195,c_2130])).

cnf(c_2574,plain,
    ( k2_pre_topc(sK3,sK4) = k2_struct_0(sK3)
    | k2_struct_0(sK3) = sK4 ),
    inference(demodulation,[status(thm)],[c_1833,c_2197])).

cnf(c_2208,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2197,c_1410])).

cnf(c_2,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1411,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( ~ v1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_456,plain,
    ( ~ r1_tarski(X0,X1)
    | X1 != X2
    | X1 = X0
    | sK0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_318])).

cnf(c_457,plain,
    ( ~ r1_tarski(sK0(X0),X0)
    | X0 = sK0(X0) ),
    inference(unflattening,[status(thm)],[c_456])).

cnf(c_823,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X2 != X1
    | sK0(X2) != X0
    | sK0(X2) = X2 ),
    inference(resolution_lifted,[status(thm)],[c_251,c_457])).

cnf(c_824,plain,
    ( ~ m1_subset_1(sK0(X0),k1_zfmisc_1(X0))
    | sK0(X0) = X0 ),
    inference(unflattening,[status(thm)],[c_823])).

cnf(c_828,plain,
    ( sK0(X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_824,c_2])).

cnf(c_1419,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1411,c_828])).

cnf(c_22,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_720,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_32])).

cnf(c_721,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
    inference(unflattening,[status(thm)],[c_720])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_23,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_632,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_633,plain,
    ( v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_632])).

cnf(c_637,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_tex_2(X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_633,c_32,c_31,c_29])).

cnf(c_638,plain,
    ( v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(renaming,[status(thm)],[c_637])).

cnf(c_725,plain,
    ( ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_721,c_32,c_31,c_29,c_633])).

cnf(c_726,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k9_subset_1(u1_struct_0(sK3),X1,k2_pre_topc(sK3,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_725])).

cnf(c_774,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | k9_subset_1(u1_struct_0(sK3),X1,k2_pre_topc(sK3,X0)) = X0 ),
    inference(resolution,[status(thm)],[c_251,c_726])).

cnf(c_1409,plain,
    ( k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_774])).

cnf(c_2374,plain,
    ( k9_subset_1(k2_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1409,c_2197])).

cnf(c_2382,plain,
    ( k9_subset_1(k2_struct_0(sK3),k2_struct_0(sK3),k2_pre_topc(sK3,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1419,c_2374])).

cnf(c_2582,plain,
    ( k9_subset_1(k2_struct_0(sK3),k2_struct_0(sK3),k2_pre_topc(sK3,sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_2208,c_2382])).

cnf(c_2688,plain,
    ( k9_subset_1(k2_struct_0(sK3),k2_struct_0(sK3),k2_struct_0(sK3)) = sK4
    | k2_struct_0(sK3) = sK4 ),
    inference(superposition,[status(thm)],[c_2574,c_2582])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X2) = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1412,plain,
    ( k9_subset_1(X0,X1,X1) = X1
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1935,plain,
    ( k9_subset_1(X0,X1,X1) = X1 ),
    inference(superposition,[status(thm)],[c_1419,c_1412])).

cnf(c_2689,plain,
    ( k2_struct_0(sK3) = sK4 ),
    inference(demodulation,[status(thm)],[c_2688,c_1935])).

cnf(c_3282,plain,
    ( k2_pre_topc(sK3,sK4) = sK4 ),
    inference(demodulation,[status(thm)],[c_2689,c_2130])).

cnf(c_26,negated_conjecture,
    ( ~ v3_tex_2(sK4,sK3)
    | v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_257,plain,
    ( ~ v3_tex_2(sK4,sK3)
    | v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(prop_impl,[status(thm)],[c_26])).

cnf(c_468,plain,
    ( ~ v3_tex_2(sK4,sK3)
    | u1_struct_0(sK3) != X0
    | sK0(X0) != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_257])).

cnf(c_469,plain,
    ( ~ v3_tex_2(sK4,sK3)
    | sK0(u1_struct_0(sK3)) != sK4 ),
    inference(unflattening,[status(thm)],[c_468])).

cnf(c_25,plain,
    ( v3_tex_2(X0,X1)
    | ~ v2_tex_2(X0,X1)
    | ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_685,plain,
    ( v3_tex_2(X0,X1)
    | ~ v2_tex_2(X0,X1)
    | ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_32])).

cnf(c_686,plain,
    ( v3_tex_2(X0,sK3)
    | ~ v2_tex_2(X0,sK3)
    | ~ v1_tops_1(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_685])).

cnf(c_690,plain,
    ( v3_tex_2(X0,sK3)
    | ~ v1_tops_1(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_686,c_32,c_31,c_29,c_633])).

cnf(c_1026,plain,
    ( ~ v1_tops_1(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | sK0(u1_struct_0(sK3)) != sK4
    | sK3 != sK3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_469,c_690])).

cnf(c_1027,plain,
    ( ~ v1_tops_1(sK4,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | sK0(u1_struct_0(sK3)) != sK4 ),
    inference(unflattening,[status(thm)],[c_1026])).

cnf(c_1029,plain,
    ( ~ v1_tops_1(sK4,sK3)
    | sK0(u1_struct_0(sK3)) != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1027,c_28])).

cnf(c_1399,plain,
    ( sK0(u1_struct_0(sK3)) != sK4
    | v1_tops_1(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1029])).

cnf(c_1429,plain,
    ( u1_struct_0(sK3) != sK4
    | v1_tops_1(sK4,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1399,c_828])).

cnf(c_3138,plain,
    ( k2_struct_0(sK3) != sK4
    | v1_tops_1(sK4,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1429,c_2197])).

cnf(c_1152,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1613,plain,
    ( k2_pre_topc(sK3,sK4) != X0
    | k2_pre_topc(sK3,sK4) = u1_struct_0(sK3)
    | u1_struct_0(sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_1152])).

cnf(c_1713,plain,
    ( k2_pre_topc(sK3,sK4) = u1_struct_0(sK3)
    | k2_pre_topc(sK3,sK4) != sK4
    | u1_struct_0(sK3) != sK4 ),
    inference(instantiation,[status(thm)],[c_1613])).

cnf(c_12,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_915,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) != u1_struct_0(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_29])).

cnf(c_916,plain,
    ( v1_tops_1(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK3,X0) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_915])).

cnf(c_1514,plain,
    ( v1_tops_1(sK4,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK3,sK4) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_916])).

cnf(c_1515,plain,
    ( k2_pre_topc(sK3,sK4) != u1_struct_0(sK3)
    | v1_tops_1(sK4,sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1514])).

cnf(c_1000,plain,
    ( u1_struct_0(sK3) = sK4
    | v1_tops_1(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_998])).

cnf(c_37,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3282,c_3138,c_2689,c_1713,c_1515,c_1000,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:58:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.36/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/0.99  
% 2.36/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.36/0.99  
% 2.36/0.99  ------  iProver source info
% 2.36/0.99  
% 2.36/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.36/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.36/0.99  git: non_committed_changes: false
% 2.36/0.99  git: last_make_outside_of_git: false
% 2.36/0.99  
% 2.36/0.99  ------ 
% 2.36/0.99  
% 2.36/0.99  ------ Input Options
% 2.36/0.99  
% 2.36/0.99  --out_options                           all
% 2.36/0.99  --tptp_safe_out                         true
% 2.36/0.99  --problem_path                          ""
% 2.36/0.99  --include_path                          ""
% 2.36/0.99  --clausifier                            res/vclausify_rel
% 2.36/0.99  --clausifier_options                    --mode clausify
% 2.36/0.99  --stdin                                 false
% 2.36/0.99  --stats_out                             all
% 2.36/0.99  
% 2.36/0.99  ------ General Options
% 2.36/0.99  
% 2.36/0.99  --fof                                   false
% 2.36/0.99  --time_out_real                         305.
% 2.36/0.99  --time_out_virtual                      -1.
% 2.36/0.99  --symbol_type_check                     false
% 2.36/0.99  --clausify_out                          false
% 2.36/0.99  --sig_cnt_out                           false
% 2.36/0.99  --trig_cnt_out                          false
% 2.36/0.99  --trig_cnt_out_tolerance                1.
% 2.36/0.99  --trig_cnt_out_sk_spl                   false
% 2.36/0.99  --abstr_cl_out                          false
% 2.36/0.99  
% 2.36/0.99  ------ Global Options
% 2.36/0.99  
% 2.36/0.99  --schedule                              default
% 2.36/0.99  --add_important_lit                     false
% 2.36/0.99  --prop_solver_per_cl                    1000
% 2.36/0.99  --min_unsat_core                        false
% 2.36/0.99  --soft_assumptions                      false
% 2.36/0.99  --soft_lemma_size                       3
% 2.36/0.99  --prop_impl_unit_size                   0
% 2.36/0.99  --prop_impl_unit                        []
% 2.36/0.99  --share_sel_clauses                     true
% 2.36/0.99  --reset_solvers                         false
% 2.36/0.99  --bc_imp_inh                            [conj_cone]
% 2.36/0.99  --conj_cone_tolerance                   3.
% 2.36/0.99  --extra_neg_conj                        none
% 2.36/0.99  --large_theory_mode                     true
% 2.36/0.99  --prolific_symb_bound                   200
% 2.36/0.99  --lt_threshold                          2000
% 2.36/0.99  --clause_weak_htbl                      true
% 2.36/0.99  --gc_record_bc_elim                     false
% 2.36/0.99  
% 2.36/0.99  ------ Preprocessing Options
% 2.36/0.99  
% 2.36/0.99  --preprocessing_flag                    true
% 2.36/0.99  --time_out_prep_mult                    0.1
% 2.36/0.99  --splitting_mode                        input
% 2.36/0.99  --splitting_grd                         true
% 2.36/0.99  --splitting_cvd                         false
% 2.36/0.99  --splitting_cvd_svl                     false
% 2.36/0.99  --splitting_nvd                         32
% 2.36/0.99  --sub_typing                            true
% 2.36/0.99  --prep_gs_sim                           true
% 2.36/0.99  --prep_unflatten                        true
% 2.36/0.99  --prep_res_sim                          true
% 2.36/0.99  --prep_upred                            true
% 2.36/0.99  --prep_sem_filter                       exhaustive
% 2.36/0.99  --prep_sem_filter_out                   false
% 2.36/0.99  --pred_elim                             true
% 2.36/0.99  --res_sim_input                         true
% 2.36/0.99  --eq_ax_congr_red                       true
% 2.36/0.99  --pure_diseq_elim                       true
% 2.36/0.99  --brand_transform                       false
% 2.36/0.99  --non_eq_to_eq                          false
% 2.36/0.99  --prep_def_merge                        true
% 2.36/0.99  --prep_def_merge_prop_impl              false
% 2.36/0.99  --prep_def_merge_mbd                    true
% 2.36/0.99  --prep_def_merge_tr_red                 false
% 2.36/0.99  --prep_def_merge_tr_cl                  false
% 2.36/0.99  --smt_preprocessing                     true
% 2.36/0.99  --smt_ac_axioms                         fast
% 2.36/0.99  --preprocessed_out                      false
% 2.36/0.99  --preprocessed_stats                    false
% 2.36/0.99  
% 2.36/0.99  ------ Abstraction refinement Options
% 2.36/0.99  
% 2.36/0.99  --abstr_ref                             []
% 2.36/0.99  --abstr_ref_prep                        false
% 2.36/0.99  --abstr_ref_until_sat                   false
% 2.36/0.99  --abstr_ref_sig_restrict                funpre
% 2.36/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.36/0.99  --abstr_ref_under                       []
% 2.36/0.99  
% 2.36/0.99  ------ SAT Options
% 2.36/0.99  
% 2.36/0.99  --sat_mode                              false
% 2.36/0.99  --sat_fm_restart_options                ""
% 2.36/0.99  --sat_gr_def                            false
% 2.36/0.99  --sat_epr_types                         true
% 2.36/0.99  --sat_non_cyclic_types                  false
% 2.36/0.99  --sat_finite_models                     false
% 2.36/0.99  --sat_fm_lemmas                         false
% 2.36/0.99  --sat_fm_prep                           false
% 2.36/0.99  --sat_fm_uc_incr                        true
% 2.36/0.99  --sat_out_model                         small
% 2.36/0.99  --sat_out_clauses                       false
% 2.36/0.99  
% 2.36/0.99  ------ QBF Options
% 2.36/0.99  
% 2.36/0.99  --qbf_mode                              false
% 2.36/0.99  --qbf_elim_univ                         false
% 2.36/0.99  --qbf_dom_inst                          none
% 2.36/0.99  --qbf_dom_pre_inst                      false
% 2.36/0.99  --qbf_sk_in                             false
% 2.36/0.99  --qbf_pred_elim                         true
% 2.36/0.99  --qbf_split                             512
% 2.36/0.99  
% 2.36/0.99  ------ BMC1 Options
% 2.36/0.99  
% 2.36/0.99  --bmc1_incremental                      false
% 2.36/0.99  --bmc1_axioms                           reachable_all
% 2.36/0.99  --bmc1_min_bound                        0
% 2.36/0.99  --bmc1_max_bound                        -1
% 2.36/0.99  --bmc1_max_bound_default                -1
% 2.36/0.99  --bmc1_symbol_reachability              true
% 2.36/0.99  --bmc1_property_lemmas                  false
% 2.36/0.99  --bmc1_k_induction                      false
% 2.36/0.99  --bmc1_non_equiv_states                 false
% 2.36/0.99  --bmc1_deadlock                         false
% 2.36/0.99  --bmc1_ucm                              false
% 2.36/0.99  --bmc1_add_unsat_core                   none
% 2.36/0.99  --bmc1_unsat_core_children              false
% 2.36/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.36/0.99  --bmc1_out_stat                         full
% 2.36/0.99  --bmc1_ground_init                      false
% 2.36/0.99  --bmc1_pre_inst_next_state              false
% 2.36/0.99  --bmc1_pre_inst_state                   false
% 2.36/0.99  --bmc1_pre_inst_reach_state             false
% 2.36/0.99  --bmc1_out_unsat_core                   false
% 2.36/0.99  --bmc1_aig_witness_out                  false
% 2.36/0.99  --bmc1_verbose                          false
% 2.36/0.99  --bmc1_dump_clauses_tptp                false
% 2.36/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.36/0.99  --bmc1_dump_file                        -
% 2.36/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.36/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.36/0.99  --bmc1_ucm_extend_mode                  1
% 2.36/0.99  --bmc1_ucm_init_mode                    2
% 2.36/0.99  --bmc1_ucm_cone_mode                    none
% 2.36/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.36/0.99  --bmc1_ucm_relax_model                  4
% 2.36/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.36/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.36/0.99  --bmc1_ucm_layered_model                none
% 2.36/0.99  --bmc1_ucm_max_lemma_size               10
% 2.36/0.99  
% 2.36/0.99  ------ AIG Options
% 2.36/0.99  
% 2.36/0.99  --aig_mode                              false
% 2.36/0.99  
% 2.36/0.99  ------ Instantiation Options
% 2.36/0.99  
% 2.36/0.99  --instantiation_flag                    true
% 2.36/0.99  --inst_sos_flag                         false
% 2.36/0.99  --inst_sos_phase                        true
% 2.36/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.36/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.36/0.99  --inst_lit_sel_side                     num_symb
% 2.36/0.99  --inst_solver_per_active                1400
% 2.36/0.99  --inst_solver_calls_frac                1.
% 2.36/0.99  --inst_passive_queue_type               priority_queues
% 2.36/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.36/0.99  --inst_passive_queues_freq              [25;2]
% 2.36/0.99  --inst_dismatching                      true
% 2.36/0.99  --inst_eager_unprocessed_to_passive     true
% 2.36/0.99  --inst_prop_sim_given                   true
% 2.36/0.99  --inst_prop_sim_new                     false
% 2.36/0.99  --inst_subs_new                         false
% 2.36/0.99  --inst_eq_res_simp                      false
% 2.36/0.99  --inst_subs_given                       false
% 2.36/0.99  --inst_orphan_elimination               true
% 2.36/0.99  --inst_learning_loop_flag               true
% 2.36/0.99  --inst_learning_start                   3000
% 2.36/0.99  --inst_learning_factor                  2
% 2.36/0.99  --inst_start_prop_sim_after_learn       3
% 2.36/0.99  --inst_sel_renew                        solver
% 2.36/0.99  --inst_lit_activity_flag                true
% 2.36/0.99  --inst_restr_to_given                   false
% 2.36/0.99  --inst_activity_threshold               500
% 2.36/0.99  --inst_out_proof                        true
% 2.36/0.99  
% 2.36/0.99  ------ Resolution Options
% 2.36/0.99  
% 2.36/0.99  --resolution_flag                       true
% 2.36/0.99  --res_lit_sel                           adaptive
% 2.36/0.99  --res_lit_sel_side                      none
% 2.36/0.99  --res_ordering                          kbo
% 2.36/0.99  --res_to_prop_solver                    active
% 2.36/0.99  --res_prop_simpl_new                    false
% 2.36/0.99  --res_prop_simpl_given                  true
% 2.36/0.99  --res_passive_queue_type                priority_queues
% 2.36/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.36/0.99  --res_passive_queues_freq               [15;5]
% 2.36/0.99  --res_forward_subs                      full
% 2.36/0.99  --res_backward_subs                     full
% 2.36/0.99  --res_forward_subs_resolution           true
% 2.36/0.99  --res_backward_subs_resolution          true
% 2.36/0.99  --res_orphan_elimination                true
% 2.36/0.99  --res_time_limit                        2.
% 2.36/0.99  --res_out_proof                         true
% 2.36/0.99  
% 2.36/0.99  ------ Superposition Options
% 2.36/0.99  
% 2.36/0.99  --superposition_flag                    true
% 2.36/0.99  --sup_passive_queue_type                priority_queues
% 2.36/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.36/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.36/0.99  --demod_completeness_check              fast
% 2.36/0.99  --demod_use_ground                      true
% 2.36/0.99  --sup_to_prop_solver                    passive
% 2.36/0.99  --sup_prop_simpl_new                    true
% 2.36/0.99  --sup_prop_simpl_given                  true
% 2.36/0.99  --sup_fun_splitting                     false
% 2.36/0.99  --sup_smt_interval                      50000
% 2.36/0.99  
% 2.36/0.99  ------ Superposition Simplification Setup
% 2.36/0.99  
% 2.36/0.99  --sup_indices_passive                   []
% 2.36/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.36/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.99  --sup_full_bw                           [BwDemod]
% 2.36/0.99  --sup_immed_triv                        [TrivRules]
% 2.36/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.36/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.99  --sup_immed_bw_main                     []
% 2.36/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.36/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/0.99  
% 2.36/0.99  ------ Combination Options
% 2.36/0.99  
% 2.36/0.99  --comb_res_mult                         3
% 2.36/0.99  --comb_sup_mult                         2
% 2.36/0.99  --comb_inst_mult                        10
% 2.36/0.99  
% 2.36/0.99  ------ Debug Options
% 2.36/0.99  
% 2.36/0.99  --dbg_backtrace                         false
% 2.36/0.99  --dbg_dump_prop_clauses                 false
% 2.36/0.99  --dbg_dump_prop_clauses_file            -
% 2.36/0.99  --dbg_out_stat                          false
% 2.36/0.99  ------ Parsing...
% 2.36/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.36/0.99  
% 2.36/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 2.36/0.99  
% 2.36/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.36/0.99  
% 2.36/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.36/0.99  ------ Proving...
% 2.36/0.99  ------ Problem Properties 
% 2.36/0.99  
% 2.36/0.99  
% 2.36/0.99  clauses                                 16
% 2.36/0.99  conjectures                             1
% 2.36/0.99  EPR                                     0
% 2.36/0.99  Horn                                    15
% 2.36/0.99  unary                                   5
% 2.36/0.99  binary                                  4
% 2.36/0.99  lits                                    37
% 2.36/0.99  lits eq                                 12
% 2.36/0.99  fd_pure                                 0
% 2.36/0.99  fd_pseudo                               0
% 2.36/0.99  fd_cond                                 0
% 2.36/0.99  fd_pseudo_cond                          0
% 2.36/0.99  AC symbols                              0
% 2.36/0.99  
% 2.36/0.99  ------ Schedule dynamic 5 is on 
% 2.36/0.99  
% 2.36/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.36/0.99  
% 2.36/0.99  
% 2.36/0.99  ------ 
% 2.36/0.99  Current options:
% 2.36/0.99  ------ 
% 2.36/0.99  
% 2.36/0.99  ------ Input Options
% 2.36/0.99  
% 2.36/0.99  --out_options                           all
% 2.36/0.99  --tptp_safe_out                         true
% 2.36/0.99  --problem_path                          ""
% 2.36/0.99  --include_path                          ""
% 2.36/0.99  --clausifier                            res/vclausify_rel
% 2.36/0.99  --clausifier_options                    --mode clausify
% 2.36/0.99  --stdin                                 false
% 2.36/0.99  --stats_out                             all
% 2.36/0.99  
% 2.36/0.99  ------ General Options
% 2.36/0.99  
% 2.36/0.99  --fof                                   false
% 2.36/0.99  --time_out_real                         305.
% 2.36/0.99  --time_out_virtual                      -1.
% 2.36/0.99  --symbol_type_check                     false
% 2.36/0.99  --clausify_out                          false
% 2.36/0.99  --sig_cnt_out                           false
% 2.36/0.99  --trig_cnt_out                          false
% 2.36/0.99  --trig_cnt_out_tolerance                1.
% 2.36/0.99  --trig_cnt_out_sk_spl                   false
% 2.36/0.99  --abstr_cl_out                          false
% 2.36/0.99  
% 2.36/0.99  ------ Global Options
% 2.36/0.99  
% 2.36/0.99  --schedule                              default
% 2.36/0.99  --add_important_lit                     false
% 2.36/0.99  --prop_solver_per_cl                    1000
% 2.36/0.99  --min_unsat_core                        false
% 2.36/0.99  --soft_assumptions                      false
% 2.36/0.99  --soft_lemma_size                       3
% 2.36/0.99  --prop_impl_unit_size                   0
% 2.36/0.99  --prop_impl_unit                        []
% 2.36/0.99  --share_sel_clauses                     true
% 2.36/0.99  --reset_solvers                         false
% 2.36/0.99  --bc_imp_inh                            [conj_cone]
% 2.36/0.99  --conj_cone_tolerance                   3.
% 2.36/0.99  --extra_neg_conj                        none
% 2.36/0.99  --large_theory_mode                     true
% 2.36/0.99  --prolific_symb_bound                   200
% 2.36/0.99  --lt_threshold                          2000
% 2.36/0.99  --clause_weak_htbl                      true
% 2.36/0.99  --gc_record_bc_elim                     false
% 2.36/0.99  
% 2.36/0.99  ------ Preprocessing Options
% 2.36/0.99  
% 2.36/0.99  --preprocessing_flag                    true
% 2.36/0.99  --time_out_prep_mult                    0.1
% 2.36/0.99  --splitting_mode                        input
% 2.36/0.99  --splitting_grd                         true
% 2.36/0.99  --splitting_cvd                         false
% 2.36/0.99  --splitting_cvd_svl                     false
% 2.36/0.99  --splitting_nvd                         32
% 2.36/0.99  --sub_typing                            true
% 2.36/0.99  --prep_gs_sim                           true
% 2.36/0.99  --prep_unflatten                        true
% 2.36/0.99  --prep_res_sim                          true
% 2.36/0.99  --prep_upred                            true
% 2.36/0.99  --prep_sem_filter                       exhaustive
% 2.36/0.99  --prep_sem_filter_out                   false
% 2.36/0.99  --pred_elim                             true
% 2.36/0.99  --res_sim_input                         true
% 2.36/0.99  --eq_ax_congr_red                       true
% 2.36/0.99  --pure_diseq_elim                       true
% 2.36/0.99  --brand_transform                       false
% 2.36/0.99  --non_eq_to_eq                          false
% 2.36/0.99  --prep_def_merge                        true
% 2.36/0.99  --prep_def_merge_prop_impl              false
% 2.36/0.99  --prep_def_merge_mbd                    true
% 2.36/0.99  --prep_def_merge_tr_red                 false
% 2.36/0.99  --prep_def_merge_tr_cl                  false
% 2.36/0.99  --smt_preprocessing                     true
% 2.36/0.99  --smt_ac_axioms                         fast
% 2.36/0.99  --preprocessed_out                      false
% 2.36/0.99  --preprocessed_stats                    false
% 2.36/0.99  
% 2.36/0.99  ------ Abstraction refinement Options
% 2.36/0.99  
% 2.36/0.99  --abstr_ref                             []
% 2.36/0.99  --abstr_ref_prep                        false
% 2.36/0.99  --abstr_ref_until_sat                   false
% 2.36/0.99  --abstr_ref_sig_restrict                funpre
% 2.36/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.36/0.99  --abstr_ref_under                       []
% 2.36/0.99  
% 2.36/0.99  ------ SAT Options
% 2.36/0.99  
% 2.36/0.99  --sat_mode                              false
% 2.36/0.99  --sat_fm_restart_options                ""
% 2.36/0.99  --sat_gr_def                            false
% 2.36/0.99  --sat_epr_types                         true
% 2.36/0.99  --sat_non_cyclic_types                  false
% 2.36/0.99  --sat_finite_models                     false
% 2.36/0.99  --sat_fm_lemmas                         false
% 2.36/0.99  --sat_fm_prep                           false
% 2.36/0.99  --sat_fm_uc_incr                        true
% 2.36/0.99  --sat_out_model                         small
% 2.36/0.99  --sat_out_clauses                       false
% 2.36/0.99  
% 2.36/0.99  ------ QBF Options
% 2.36/0.99  
% 2.36/0.99  --qbf_mode                              false
% 2.36/0.99  --qbf_elim_univ                         false
% 2.36/0.99  --qbf_dom_inst                          none
% 2.36/0.99  --qbf_dom_pre_inst                      false
% 2.36/0.99  --qbf_sk_in                             false
% 2.36/0.99  --qbf_pred_elim                         true
% 2.36/0.99  --qbf_split                             512
% 2.36/0.99  
% 2.36/0.99  ------ BMC1 Options
% 2.36/0.99  
% 2.36/0.99  --bmc1_incremental                      false
% 2.36/0.99  --bmc1_axioms                           reachable_all
% 2.36/0.99  --bmc1_min_bound                        0
% 2.36/0.99  --bmc1_max_bound                        -1
% 2.36/0.99  --bmc1_max_bound_default                -1
% 2.36/1.00  --bmc1_symbol_reachability              true
% 2.36/1.00  --bmc1_property_lemmas                  false
% 2.36/1.00  --bmc1_k_induction                      false
% 2.36/1.00  --bmc1_non_equiv_states                 false
% 2.36/1.00  --bmc1_deadlock                         false
% 2.36/1.00  --bmc1_ucm                              false
% 2.36/1.00  --bmc1_add_unsat_core                   none
% 2.36/1.00  --bmc1_unsat_core_children              false
% 2.36/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.36/1.00  --bmc1_out_stat                         full
% 2.36/1.00  --bmc1_ground_init                      false
% 2.36/1.00  --bmc1_pre_inst_next_state              false
% 2.36/1.00  --bmc1_pre_inst_state                   false
% 2.36/1.00  --bmc1_pre_inst_reach_state             false
% 2.36/1.00  --bmc1_out_unsat_core                   false
% 2.36/1.00  --bmc1_aig_witness_out                  false
% 2.36/1.00  --bmc1_verbose                          false
% 2.36/1.00  --bmc1_dump_clauses_tptp                false
% 2.36/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.36/1.00  --bmc1_dump_file                        -
% 2.36/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.36/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.36/1.00  --bmc1_ucm_extend_mode                  1
% 2.36/1.00  --bmc1_ucm_init_mode                    2
% 2.36/1.00  --bmc1_ucm_cone_mode                    none
% 2.36/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.36/1.00  --bmc1_ucm_relax_model                  4
% 2.36/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.36/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.36/1.00  --bmc1_ucm_layered_model                none
% 2.36/1.00  --bmc1_ucm_max_lemma_size               10
% 2.36/1.00  
% 2.36/1.00  ------ AIG Options
% 2.36/1.00  
% 2.36/1.00  --aig_mode                              false
% 2.36/1.00  
% 2.36/1.00  ------ Instantiation Options
% 2.36/1.00  
% 2.36/1.00  --instantiation_flag                    true
% 2.36/1.00  --inst_sos_flag                         false
% 2.36/1.00  --inst_sos_phase                        true
% 2.36/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.36/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.36/1.00  --inst_lit_sel_side                     none
% 2.36/1.00  --inst_solver_per_active                1400
% 2.36/1.00  --inst_solver_calls_frac                1.
% 2.36/1.00  --inst_passive_queue_type               priority_queues
% 2.36/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.36/1.00  --inst_passive_queues_freq              [25;2]
% 2.36/1.00  --inst_dismatching                      true
% 2.36/1.00  --inst_eager_unprocessed_to_passive     true
% 2.36/1.00  --inst_prop_sim_given                   true
% 2.36/1.00  --inst_prop_sim_new                     false
% 2.36/1.00  --inst_subs_new                         false
% 2.36/1.00  --inst_eq_res_simp                      false
% 2.36/1.00  --inst_subs_given                       false
% 2.36/1.00  --inst_orphan_elimination               true
% 2.36/1.00  --inst_learning_loop_flag               true
% 2.36/1.00  --inst_learning_start                   3000
% 2.36/1.00  --inst_learning_factor                  2
% 2.36/1.00  --inst_start_prop_sim_after_learn       3
% 2.36/1.00  --inst_sel_renew                        solver
% 2.36/1.00  --inst_lit_activity_flag                true
% 2.36/1.00  --inst_restr_to_given                   false
% 2.36/1.00  --inst_activity_threshold               500
% 2.36/1.00  --inst_out_proof                        true
% 2.36/1.00  
% 2.36/1.00  ------ Resolution Options
% 2.36/1.00  
% 2.36/1.00  --resolution_flag                       false
% 2.36/1.00  --res_lit_sel                           adaptive
% 2.36/1.00  --res_lit_sel_side                      none
% 2.36/1.00  --res_ordering                          kbo
% 2.36/1.00  --res_to_prop_solver                    active
% 2.36/1.00  --res_prop_simpl_new                    false
% 2.36/1.00  --res_prop_simpl_given                  true
% 2.36/1.00  --res_passive_queue_type                priority_queues
% 2.36/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.36/1.00  --res_passive_queues_freq               [15;5]
% 2.36/1.00  --res_forward_subs                      full
% 2.36/1.00  --res_backward_subs                     full
% 2.36/1.00  --res_forward_subs_resolution           true
% 2.36/1.00  --res_backward_subs_resolution          true
% 2.36/1.00  --res_orphan_elimination                true
% 2.36/1.00  --res_time_limit                        2.
% 2.36/1.00  --res_out_proof                         true
% 2.36/1.00  
% 2.36/1.00  ------ Superposition Options
% 2.36/1.00  
% 2.36/1.00  --superposition_flag                    true
% 2.36/1.00  --sup_passive_queue_type                priority_queues
% 2.36/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.36/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.36/1.00  --demod_completeness_check              fast
% 2.36/1.00  --demod_use_ground                      true
% 2.36/1.00  --sup_to_prop_solver                    passive
% 2.36/1.00  --sup_prop_simpl_new                    true
% 2.36/1.00  --sup_prop_simpl_given                  true
% 2.36/1.00  --sup_fun_splitting                     false
% 2.36/1.00  --sup_smt_interval                      50000
% 2.36/1.00  
% 2.36/1.00  ------ Superposition Simplification Setup
% 2.36/1.00  
% 2.36/1.00  --sup_indices_passive                   []
% 2.36/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.36/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/1.00  --sup_full_bw                           [BwDemod]
% 2.36/1.00  --sup_immed_triv                        [TrivRules]
% 2.36/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.36/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/1.00  --sup_immed_bw_main                     []
% 2.36/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.36/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/1.00  
% 2.36/1.00  ------ Combination Options
% 2.36/1.00  
% 2.36/1.00  --comb_res_mult                         3
% 2.36/1.00  --comb_sup_mult                         2
% 2.36/1.00  --comb_inst_mult                        10
% 2.36/1.00  
% 2.36/1.00  ------ Debug Options
% 2.36/1.00  
% 2.36/1.00  --dbg_backtrace                         false
% 2.36/1.00  --dbg_dump_prop_clauses                 false
% 2.36/1.00  --dbg_dump_prop_clauses_file            -
% 2.36/1.00  --dbg_out_stat                          false
% 2.36/1.00  
% 2.36/1.00  
% 2.36/1.00  
% 2.36/1.00  
% 2.36/1.00  ------ Proving...
% 2.36/1.00  
% 2.36/1.00  
% 2.36/1.00  % SZS status Theorem for theBenchmark.p
% 2.36/1.00  
% 2.36/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.36/1.00  
% 2.36/1.00  fof(f3,axiom,(
% 2.36/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f44,plain,(
% 2.36/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.36/1.00    inference(nnf_transformation,[],[f3])).
% 2.36/1.00  
% 2.36/1.00  fof(f64,plain,(
% 2.36/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.36/1.00    inference(cnf_transformation,[],[f44])).
% 2.36/1.00  
% 2.36/1.00  fof(f11,axiom,(
% 2.36/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 2.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f29,plain,(
% 2.36/1.00    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.36/1.00    inference(ennf_transformation,[],[f11])).
% 2.36/1.00  
% 2.36/1.00  fof(f47,plain,(
% 2.36/1.00    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.36/1.00    inference(nnf_transformation,[],[f29])).
% 2.36/1.00  
% 2.36/1.00  fof(f76,plain,(
% 2.36/1.00    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.36/1.00    inference(cnf_transformation,[],[f47])).
% 2.36/1.00  
% 2.36/1.00  fof(f65,plain,(
% 2.36/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.36/1.00    inference(cnf_transformation,[],[f44])).
% 2.36/1.00  
% 2.36/1.00  fof(f17,conjecture,(
% 2.36/1.00    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 2.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f18,negated_conjecture,(
% 2.36/1.00    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 2.36/1.00    inference(negated_conjecture,[],[f17])).
% 2.36/1.00  
% 2.36/1.00  fof(f40,plain,(
% 2.36/1.00    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.36/1.00    inference(ennf_transformation,[],[f18])).
% 2.36/1.00  
% 2.36/1.00  fof(f41,plain,(
% 2.36/1.00    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.36/1.00    inference(flattening,[],[f40])).
% 2.36/1.00  
% 2.36/1.00  fof(f56,plain,(
% 2.36/1.00    ? [X0] : (? [X1] : (((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.36/1.00    inference(nnf_transformation,[],[f41])).
% 2.36/1.00  
% 2.36/1.00  fof(f57,plain,(
% 2.36/1.00    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.36/1.00    inference(flattening,[],[f56])).
% 2.36/1.00  
% 2.36/1.00  fof(f59,plain,(
% 2.36/1.00    ( ! [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_subset_1(sK4,u1_struct_0(X0)) | ~v3_tex_2(sK4,X0)) & (~v1_subset_1(sK4,u1_struct_0(X0)) | v3_tex_2(sK4,X0)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.36/1.00    introduced(choice_axiom,[])).
% 2.36/1.00  
% 2.36/1.00  fof(f58,plain,(
% 2.36/1.00    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((v1_subset_1(X1,u1_struct_0(sK3)) | ~v3_tex_2(X1,sK3)) & (~v1_subset_1(X1,u1_struct_0(sK3)) | v3_tex_2(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v1_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 2.36/1.00    introduced(choice_axiom,[])).
% 2.36/1.00  
% 2.36/1.00  fof(f60,plain,(
% 2.36/1.00    ((v1_subset_1(sK4,u1_struct_0(sK3)) | ~v3_tex_2(sK4,sK3)) & (~v1_subset_1(sK4,u1_struct_0(sK3)) | v3_tex_2(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v1_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 2.36/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f57,f59,f58])).
% 2.36/1.00  
% 2.36/1.00  fof(f92,plain,(
% 2.36/1.00    ~v1_subset_1(sK4,u1_struct_0(sK3)) | v3_tex_2(sK4,sK3)),
% 2.36/1.00    inference(cnf_transformation,[],[f60])).
% 2.36/1.00  
% 2.36/1.00  fof(f91,plain,(
% 2.36/1.00    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 2.36/1.00    inference(cnf_transformation,[],[f60])).
% 2.36/1.00  
% 2.36/1.00  fof(f12,axiom,(
% 2.36/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 2.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f30,plain,(
% 2.36/1.00    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.36/1.00    inference(ennf_transformation,[],[f12])).
% 2.36/1.00  
% 2.36/1.00  fof(f31,plain,(
% 2.36/1.00    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.36/1.00    inference(flattening,[],[f30])).
% 2.36/1.00  
% 2.36/1.00  fof(f48,plain,(
% 2.36/1.00    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.36/1.00    inference(nnf_transformation,[],[f31])).
% 2.36/1.00  
% 2.36/1.00  fof(f49,plain,(
% 2.36/1.00    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.36/1.00    inference(rectify,[],[f48])).
% 2.36/1.00  
% 2.36/1.00  fof(f50,plain,(
% 2.36/1.00    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK1(X0),X0) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.36/1.00    introduced(choice_axiom,[])).
% 2.36/1.00  
% 2.36/1.00  fof(f51,plain,(
% 2.36/1.00    ! [X0] : (((v1_tdlat_3(X0) | (~v3_pre_topc(sK1(X0),X0) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.36/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f49,f50])).
% 2.36/1.00  
% 2.36/1.00  fof(f77,plain,(
% 2.36/1.00    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.36/1.00    inference(cnf_transformation,[],[f51])).
% 2.36/1.00  
% 2.36/1.00  fof(f15,axiom,(
% 2.36/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 2.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f36,plain,(
% 2.36/1.00    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.36/1.00    inference(ennf_transformation,[],[f15])).
% 2.36/1.00  
% 2.36/1.00  fof(f37,plain,(
% 2.36/1.00    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.36/1.00    inference(flattening,[],[f36])).
% 2.36/1.00  
% 2.36/1.00  fof(f85,plain,(
% 2.36/1.00    ( ! [X0,X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.36/1.00    inference(cnf_transformation,[],[f37])).
% 2.36/1.00  
% 2.36/1.00  fof(f9,axiom,(
% 2.36/1.00    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 2.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f26,plain,(
% 2.36/1.00    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 2.36/1.00    inference(ennf_transformation,[],[f9])).
% 2.36/1.00  
% 2.36/1.00  fof(f27,plain,(
% 2.36/1.00    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 2.36/1.00    inference(flattening,[],[f26])).
% 2.36/1.00  
% 2.36/1.00  fof(f72,plain,(
% 2.36/1.00    ( ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 2.36/1.00    inference(cnf_transformation,[],[f27])).
% 2.36/1.00  
% 2.36/1.00  fof(f87,plain,(
% 2.36/1.00    ~v2_struct_0(sK3)),
% 2.36/1.00    inference(cnf_transformation,[],[f60])).
% 2.36/1.00  
% 2.36/1.00  fof(f89,plain,(
% 2.36/1.00    v1_tdlat_3(sK3)),
% 2.36/1.00    inference(cnf_transformation,[],[f60])).
% 2.36/1.00  
% 2.36/1.00  fof(f90,plain,(
% 2.36/1.00    l1_pre_topc(sK3)),
% 2.36/1.00    inference(cnf_transformation,[],[f60])).
% 2.36/1.00  
% 2.36/1.00  fof(f6,axiom,(
% 2.36/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 2.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f22,plain,(
% 2.36/1.00    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.36/1.00    inference(ennf_transformation,[],[f6])).
% 2.36/1.00  
% 2.36/1.00  fof(f45,plain,(
% 2.36/1.00    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.36/1.00    inference(nnf_transformation,[],[f22])).
% 2.36/1.00  
% 2.36/1.00  fof(f68,plain,(
% 2.36/1.00    ( ! [X0,X1] : (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.36/1.00    inference(cnf_transformation,[],[f45])).
% 2.36/1.00  
% 2.36/1.00  fof(f5,axiom,(
% 2.36/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f21,plain,(
% 2.36/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.36/1.00    inference(ennf_transformation,[],[f5])).
% 2.36/1.00  
% 2.36/1.00  fof(f67,plain,(
% 2.36/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.36/1.00    inference(cnf_transformation,[],[f21])).
% 2.36/1.00  
% 2.36/1.00  fof(f4,axiom,(
% 2.36/1.00    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f20,plain,(
% 2.36/1.00    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 2.36/1.00    inference(ennf_transformation,[],[f4])).
% 2.36/1.00  
% 2.36/1.00  fof(f66,plain,(
% 2.36/1.00    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 2.36/1.00    inference(cnf_transformation,[],[f20])).
% 2.36/1.00  
% 2.36/1.00  fof(f10,axiom,(
% 2.36/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 2.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f28,plain,(
% 2.36/1.00    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.36/1.00    inference(ennf_transformation,[],[f10])).
% 2.36/1.00  
% 2.36/1.00  fof(f46,plain,(
% 2.36/1.00    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.36/1.00    inference(nnf_transformation,[],[f28])).
% 2.36/1.00  
% 2.36/1.00  fof(f73,plain,(
% 2.36/1.00    ( ! [X0,X1] : (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.36/1.00    inference(cnf_transformation,[],[f46])).
% 2.36/1.00  
% 2.36/1.00  fof(f7,axiom,(
% 2.36/1.00    ! [X0] : (l1_pre_topc(X0) => v1_tops_1(k2_struct_0(X0),X0))),
% 2.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f23,plain,(
% 2.36/1.00    ! [X0] : (v1_tops_1(k2_struct_0(X0),X0) | ~l1_pre_topc(X0))),
% 2.36/1.00    inference(ennf_transformation,[],[f7])).
% 2.36/1.00  
% 2.36/1.00  fof(f70,plain,(
% 2.36/1.00    ( ! [X0] : (v1_tops_1(k2_struct_0(X0),X0) | ~l1_pre_topc(X0)) )),
% 2.36/1.00    inference(cnf_transformation,[],[f23])).
% 2.36/1.00  
% 2.36/1.00  fof(f2,axiom,(
% 2.36/1.00    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f42,plain,(
% 2.36/1.00    ! [X0] : (? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (~v1_subset_1(sK0(X0),X0) & m1_subset_1(sK0(X0),k1_zfmisc_1(X0))))),
% 2.36/1.00    introduced(choice_axiom,[])).
% 2.36/1.00  
% 2.36/1.00  fof(f43,plain,(
% 2.36/1.00    ! [X0] : (~v1_subset_1(sK0(X0),X0) & m1_subset_1(sK0(X0),k1_zfmisc_1(X0)))),
% 2.36/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f2,f42])).
% 2.36/1.00  
% 2.36/1.00  fof(f62,plain,(
% 2.36/1.00    ( ! [X0] : (m1_subset_1(sK0(X0),k1_zfmisc_1(X0))) )),
% 2.36/1.00    inference(cnf_transformation,[],[f43])).
% 2.36/1.00  
% 2.36/1.00  fof(f63,plain,(
% 2.36/1.00    ( ! [X0] : (~v1_subset_1(sK0(X0),X0)) )),
% 2.36/1.00    inference(cnf_transformation,[],[f43])).
% 2.36/1.00  
% 2.36/1.00  fof(f13,axiom,(
% 2.36/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 2.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f32,plain,(
% 2.36/1.00    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.36/1.00    inference(ennf_transformation,[],[f13])).
% 2.36/1.00  
% 2.36/1.00  fof(f33,plain,(
% 2.36/1.00    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.36/1.00    inference(flattening,[],[f32])).
% 2.36/1.00  
% 2.36/1.00  fof(f52,plain,(
% 2.36/1.00    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.36/1.00    inference(nnf_transformation,[],[f33])).
% 2.36/1.00  
% 2.36/1.00  fof(f53,plain,(
% 2.36/1.00    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.36/1.00    inference(rectify,[],[f52])).
% 2.36/1.00  
% 2.36/1.00  fof(f54,plain,(
% 2.36/1.00    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.36/1.00    introduced(choice_axiom,[])).
% 2.36/1.00  
% 2.36/1.00  fof(f55,plain,(
% 2.36/1.00    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.36/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f53,f54])).
% 2.36/1.00  
% 2.36/1.00  fof(f80,plain,(
% 2.36/1.00    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.36/1.00    inference(cnf_transformation,[],[f55])).
% 2.36/1.00  
% 2.36/1.00  fof(f88,plain,(
% 2.36/1.00    v2_pre_topc(sK3)),
% 2.36/1.00    inference(cnf_transformation,[],[f60])).
% 2.36/1.00  
% 2.36/1.00  fof(f14,axiom,(
% 2.36/1.00    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 2.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f34,plain,(
% 2.36/1.00    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.36/1.00    inference(ennf_transformation,[],[f14])).
% 2.36/1.00  
% 2.36/1.00  fof(f35,plain,(
% 2.36/1.00    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.36/1.00    inference(flattening,[],[f34])).
% 2.36/1.00  
% 2.36/1.00  fof(f84,plain,(
% 2.36/1.00    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.36/1.00    inference(cnf_transformation,[],[f35])).
% 2.36/1.00  
% 2.36/1.00  fof(f1,axiom,(
% 2.36/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 2.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f19,plain,(
% 2.36/1.00    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.36/1.00    inference(ennf_transformation,[],[f1])).
% 2.36/1.00  
% 2.36/1.00  fof(f61,plain,(
% 2.36/1.00    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.36/1.00    inference(cnf_transformation,[],[f19])).
% 2.36/1.00  
% 2.36/1.00  fof(f93,plain,(
% 2.36/1.00    v1_subset_1(sK4,u1_struct_0(sK3)) | ~v3_tex_2(sK4,sK3)),
% 2.36/1.00    inference(cnf_transformation,[],[f60])).
% 2.36/1.00  
% 2.36/1.00  fof(f16,axiom,(
% 2.36/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 2.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f38,plain,(
% 2.36/1.00    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) | (~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.36/1.00    inference(ennf_transformation,[],[f16])).
% 2.36/1.00  
% 2.36/1.00  fof(f39,plain,(
% 2.36/1.00    ! [X0] : (! [X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.36/1.00    inference(flattening,[],[f38])).
% 2.36/1.00  
% 2.36/1.00  fof(f86,plain,(
% 2.36/1.00    ( ! [X0,X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.36/1.00    inference(cnf_transformation,[],[f39])).
% 2.36/1.00  
% 2.36/1.00  fof(f74,plain,(
% 2.36/1.00    ( ! [X0,X1] : (v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.36/1.00    inference(cnf_transformation,[],[f46])).
% 2.36/1.00  
% 2.36/1.00  cnf(c_4,plain,
% 2.36/1.00      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.36/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_251,plain,
% 2.36/1.00      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.36/1.00      inference(prop_impl,[status(thm)],[c_4]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_14,plain,
% 2.36/1.00      ( v1_subset_1(X0,X1)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.36/1.00      | X0 = X1 ),
% 2.36/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_3,plain,
% 2.36/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.36/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_253,plain,
% 2.36/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.36/1.00      inference(prop_impl,[status(thm)],[c_3]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_318,plain,
% 2.36/1.00      ( ~ r1_tarski(X0,X1) | v1_subset_1(X0,X1) | X0 = X1 ),
% 2.36/1.00      inference(bin_hyper_res,[status(thm)],[c_14,c_253]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_27,negated_conjecture,
% 2.36/1.00      ( v3_tex_2(sK4,sK3) | ~ v1_subset_1(sK4,u1_struct_0(sK3)) ),
% 2.36/1.00      inference(cnf_transformation,[],[f92]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_255,plain,
% 2.36/1.00      ( v3_tex_2(sK4,sK3) | ~ v1_subset_1(sK4,u1_struct_0(sK3)) ),
% 2.36/1.00      inference(prop_impl,[status(thm)],[c_27]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_480,plain,
% 2.36/1.00      ( v3_tex_2(sK4,sK3)
% 2.36/1.00      | ~ r1_tarski(X0,X1)
% 2.36/1.00      | X1 = X0
% 2.36/1.00      | u1_struct_0(sK3) != X1
% 2.36/1.00      | sK4 != X0 ),
% 2.36/1.00      inference(resolution_lifted,[status(thm)],[c_318,c_255]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_481,plain,
% 2.36/1.00      ( v3_tex_2(sK4,sK3)
% 2.36/1.00      | ~ r1_tarski(sK4,u1_struct_0(sK3))
% 2.36/1.00      | u1_struct_0(sK3) = sK4 ),
% 2.36/1.00      inference(unflattening,[status(thm)],[c_480]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_834,plain,
% 2.36/1.00      ( v3_tex_2(sK4,sK3)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.36/1.00      | u1_struct_0(sK3) != X1
% 2.36/1.00      | u1_struct_0(sK3) = sK4
% 2.36/1.00      | sK4 != X0 ),
% 2.36/1.00      inference(resolution_lifted,[status(thm)],[c_251,c_481]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_835,plain,
% 2.36/1.00      ( v3_tex_2(sK4,sK3)
% 2.36/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.36/1.00      | u1_struct_0(sK3) = sK4 ),
% 2.36/1.00      inference(unflattening,[status(thm)],[c_834]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_28,negated_conjecture,
% 2.36/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.36/1.00      inference(cnf_transformation,[],[f91]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_837,plain,
% 2.36/1.00      ( v3_tex_2(sK4,sK3) | u1_struct_0(sK3) = sK4 ),
% 2.36/1.00      inference(global_propositional_subsumption,
% 2.36/1.00                [status(thm)],
% 2.36/1.00                [c_835,c_28]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_18,plain,
% 2.36/1.00      ( v3_pre_topc(X0,X1)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.36/1.00      | ~ v1_tdlat_3(X1)
% 2.36/1.00      | ~ v2_pre_topc(X1)
% 2.36/1.00      | ~ l1_pre_topc(X1) ),
% 2.36/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_24,plain,
% 2.36/1.00      ( ~ v3_tex_2(X0,X1)
% 2.36/1.00      | ~ v3_pre_topc(X0,X1)
% 2.36/1.00      | v1_tops_1(X0,X1)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.36/1.00      | v2_struct_0(X1)
% 2.36/1.00      | ~ v2_pre_topc(X1)
% 2.36/1.00      | ~ l1_pre_topc(X1) ),
% 2.36/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_520,plain,
% 2.36/1.00      ( ~ v3_tex_2(X0,X1)
% 2.36/1.00      | v1_tops_1(X0,X1)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.36/1.00      | v2_struct_0(X1)
% 2.36/1.00      | ~ v1_tdlat_3(X1)
% 2.36/1.00      | ~ v2_pre_topc(X1)
% 2.36/1.00      | ~ l1_pre_topc(X1) ),
% 2.36/1.00      inference(resolution,[status(thm)],[c_18,c_24]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_11,plain,
% 2.36/1.00      ( ~ v1_tdlat_3(X0) | v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 2.36/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_538,plain,
% 2.36/1.00      ( ~ v3_tex_2(X0,X1)
% 2.36/1.00      | v1_tops_1(X0,X1)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.36/1.00      | v2_struct_0(X1)
% 2.36/1.00      | ~ v1_tdlat_3(X1)
% 2.36/1.00      | ~ l1_pre_topc(X1) ),
% 2.36/1.00      inference(forward_subsumption_resolution,
% 2.36/1.00                [status(thm)],
% 2.36/1.00                [c_520,c_11]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_32,negated_conjecture,
% 2.36/1.00      ( ~ v2_struct_0(sK3) ),
% 2.36/1.00      inference(cnf_transformation,[],[f87]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_668,plain,
% 2.36/1.00      ( ~ v3_tex_2(X0,X1)
% 2.36/1.00      | v1_tops_1(X0,X1)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.36/1.00      | ~ v1_tdlat_3(X1)
% 2.36/1.00      | ~ l1_pre_topc(X1)
% 2.36/1.00      | sK3 != X1 ),
% 2.36/1.00      inference(resolution_lifted,[status(thm)],[c_538,c_32]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_669,plain,
% 2.36/1.00      ( ~ v3_tex_2(X0,sK3)
% 2.36/1.00      | v1_tops_1(X0,sK3)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.36/1.00      | ~ v1_tdlat_3(sK3)
% 2.36/1.00      | ~ l1_pre_topc(sK3) ),
% 2.36/1.00      inference(unflattening,[status(thm)],[c_668]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_30,negated_conjecture,
% 2.36/1.00      ( v1_tdlat_3(sK3) ),
% 2.36/1.00      inference(cnf_transformation,[],[f89]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_611,plain,
% 2.36/1.00      ( ~ v3_tex_2(X0,X1)
% 2.36/1.00      | v1_tops_1(X0,X1)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.36/1.00      | v2_struct_0(X1)
% 2.36/1.00      | ~ l1_pre_topc(X1)
% 2.36/1.00      | sK3 != X1 ),
% 2.36/1.00      inference(resolution_lifted,[status(thm)],[c_538,c_30]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_612,plain,
% 2.36/1.00      ( ~ v3_tex_2(X0,sK3)
% 2.36/1.00      | v1_tops_1(X0,sK3)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.36/1.00      | v2_struct_0(sK3)
% 2.36/1.00      | ~ l1_pre_topc(sK3) ),
% 2.36/1.00      inference(unflattening,[status(thm)],[c_611]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_29,negated_conjecture,
% 2.36/1.00      ( l1_pre_topc(sK3) ),
% 2.36/1.00      inference(cnf_transformation,[],[f90]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_616,plain,
% 2.36/1.00      ( ~ v3_tex_2(X0,sK3)
% 2.36/1.00      | v1_tops_1(X0,sK3)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.36/1.00      inference(global_propositional_subsumption,
% 2.36/1.00                [status(thm)],
% 2.36/1.00                [c_612,c_32,c_29]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_671,plain,
% 2.36/1.00      ( ~ v3_tex_2(X0,sK3)
% 2.36/1.00      | v1_tops_1(X0,sK3)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.36/1.00      inference(global_propositional_subsumption,
% 2.36/1.00                [status(thm)],
% 2.36/1.00                [c_669,c_32,c_29,c_612]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_995,plain,
% 2.36/1.00      ( v1_tops_1(X0,sK3)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.36/1.00      | u1_struct_0(sK3) = sK4
% 2.36/1.00      | sK3 != sK3
% 2.36/1.00      | sK4 != X0 ),
% 2.36/1.00      inference(resolution_lifted,[status(thm)],[c_837,c_671]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_996,plain,
% 2.36/1.00      ( v1_tops_1(sK4,sK3)
% 2.36/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.36/1.00      | u1_struct_0(sK3) = sK4 ),
% 2.36/1.00      inference(unflattening,[status(thm)],[c_995]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_998,plain,
% 2.36/1.00      ( v1_tops_1(sK4,sK3) | u1_struct_0(sK3) = sK4 ),
% 2.36/1.00      inference(global_propositional_subsumption,
% 2.36/1.00                [status(thm)],
% 2.36/1.00                [c_996,c_28]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1401,plain,
% 2.36/1.00      ( u1_struct_0(sK3) = sK4 | v1_tops_1(sK4,sK3) = iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_998]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1410,plain,
% 2.36/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_8,plain,
% 2.36/1.00      ( ~ v1_tops_1(X0,X1)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.36/1.00      | ~ l1_pre_topc(X1)
% 2.36/1.00      | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
% 2.36/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_930,plain,
% 2.36/1.00      ( ~ v1_tops_1(X0,X1)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.36/1.00      | k2_pre_topc(X1,X0) = k2_struct_0(X1)
% 2.36/1.00      | sK3 != X1 ),
% 2.36/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_29]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_931,plain,
% 2.36/1.00      ( ~ v1_tops_1(X0,sK3)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.36/1.00      | k2_pre_topc(sK3,X0) = k2_struct_0(sK3) ),
% 2.36/1.00      inference(unflattening,[status(thm)],[c_930]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1403,plain,
% 2.36/1.00      ( k2_pre_topc(sK3,X0) = k2_struct_0(sK3)
% 2.36/1.00      | v1_tops_1(X0,sK3) != iProver_top
% 2.36/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_931]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1621,plain,
% 2.36/1.00      ( k2_pre_topc(sK3,sK4) = k2_struct_0(sK3)
% 2.36/1.00      | v1_tops_1(sK4,sK3) != iProver_top ),
% 2.36/1.00      inference(superposition,[status(thm)],[c_1410,c_1403]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1833,plain,
% 2.36/1.00      ( k2_pre_topc(sK3,sK4) = k2_struct_0(sK3)
% 2.36/1.00      | u1_struct_0(sK3) = sK4 ),
% 2.36/1.00      inference(superposition,[status(thm)],[c_1401,c_1621]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_6,plain,
% 2.36/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.36/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_5,plain,
% 2.36/1.00      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.36/1.00      | ~ l1_struct_0(X0) ),
% 2.36/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_441,plain,
% 2.36/1.00      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.36/1.00      | ~ l1_pre_topc(X0) ),
% 2.36/1.00      inference(resolution,[status(thm)],[c_6,c_5]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_867,plain,
% 2.36/1.00      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.36/1.00      | sK3 != X0 ),
% 2.36/1.00      inference(resolution_lifted,[status(thm)],[c_441,c_29]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_868,plain,
% 2.36/1.00      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.36/1.00      inference(unflattening,[status(thm)],[c_867]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1408,plain,
% 2.36/1.00      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_868]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_13,plain,
% 2.36/1.00      ( ~ v1_tops_1(X0,X1)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.36/1.00      | ~ l1_pre_topc(X1)
% 2.36/1.00      | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
% 2.36/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_900,plain,
% 2.36/1.00      ( ~ v1_tops_1(X0,X1)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.36/1.00      | k2_pre_topc(X1,X0) = u1_struct_0(X1)
% 2.36/1.00      | sK3 != X1 ),
% 2.36/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_29]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_901,plain,
% 2.36/1.00      ( ~ v1_tops_1(X0,sK3)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.36/1.00      | k2_pre_topc(sK3,X0) = u1_struct_0(sK3) ),
% 2.36/1.00      inference(unflattening,[status(thm)],[c_900]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1405,plain,
% 2.36/1.00      ( k2_pre_topc(sK3,X0) = u1_struct_0(sK3)
% 2.36/1.00      | v1_tops_1(X0,sK3) != iProver_top
% 2.36/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_901]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1698,plain,
% 2.36/1.00      ( k2_pre_topc(sK3,k2_struct_0(sK3)) = u1_struct_0(sK3)
% 2.36/1.00      | v1_tops_1(k2_struct_0(sK3),sK3) != iProver_top ),
% 2.36/1.00      inference(superposition,[status(thm)],[c_1408,c_1405]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_9,plain,
% 2.36/1.00      ( v1_tops_1(k2_struct_0(X0),X0) | ~ l1_pre_topc(X0) ),
% 2.36/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_81,plain,
% 2.36/1.00      ( v1_tops_1(k2_struct_0(sK3),sK3) | ~ l1_pre_topc(sK3) ),
% 2.36/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_90,plain,
% 2.36/1.00      ( ~ l1_pre_topc(sK3) | l1_struct_0(sK3) ),
% 2.36/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_93,plain,
% 2.36/1.00      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.36/1.00      | ~ l1_struct_0(sK3) ),
% 2.36/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1511,plain,
% 2.36/1.00      ( ~ v1_tops_1(k2_struct_0(sK3),sK3)
% 2.36/1.00      | ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.36/1.00      | k2_pre_topc(sK3,k2_struct_0(sK3)) = u1_struct_0(sK3) ),
% 2.36/1.00      inference(instantiation,[status(thm)],[c_901]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2195,plain,
% 2.36/1.00      ( k2_pre_topc(sK3,k2_struct_0(sK3)) = u1_struct_0(sK3) ),
% 2.36/1.00      inference(global_propositional_subsumption,
% 2.36/1.00                [status(thm)],
% 2.36/1.00                [c_1698,c_29,c_81,c_90,c_93,c_1511]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1622,plain,
% 2.36/1.00      ( k2_pre_topc(sK3,k2_struct_0(sK3)) = k2_struct_0(sK3)
% 2.36/1.00      | v1_tops_1(k2_struct_0(sK3),sK3) != iProver_top ),
% 2.36/1.00      inference(superposition,[status(thm)],[c_1408,c_1403]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1518,plain,
% 2.36/1.00      ( ~ v1_tops_1(k2_struct_0(sK3),sK3)
% 2.36/1.00      | ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.36/1.00      | k2_pre_topc(sK3,k2_struct_0(sK3)) = k2_struct_0(sK3) ),
% 2.36/1.00      inference(instantiation,[status(thm)],[c_931]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2130,plain,
% 2.36/1.00      ( k2_pre_topc(sK3,k2_struct_0(sK3)) = k2_struct_0(sK3) ),
% 2.36/1.00      inference(global_propositional_subsumption,
% 2.36/1.00                [status(thm)],
% 2.36/1.00                [c_1622,c_29,c_81,c_90,c_93,c_1518]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2197,plain,
% 2.36/1.00      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 2.36/1.00      inference(light_normalisation,[status(thm)],[c_2195,c_2130]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2574,plain,
% 2.36/1.00      ( k2_pre_topc(sK3,sK4) = k2_struct_0(sK3)
% 2.36/1.00      | k2_struct_0(sK3) = sK4 ),
% 2.36/1.00      inference(demodulation,[status(thm)],[c_1833,c_2197]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2208,plain,
% 2.36/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
% 2.36/1.00      inference(demodulation,[status(thm)],[c_2197,c_1410]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2,plain,
% 2.36/1.00      ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ),
% 2.36/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1411,plain,
% 2.36/1.00      ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1,plain,
% 2.36/1.00      ( ~ v1_subset_1(sK0(X0),X0) ),
% 2.36/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_456,plain,
% 2.36/1.00      ( ~ r1_tarski(X0,X1) | X1 != X2 | X1 = X0 | sK0(X2) != X0 ),
% 2.36/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_318]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_457,plain,
% 2.36/1.00      ( ~ r1_tarski(sK0(X0),X0) | X0 = sK0(X0) ),
% 2.36/1.00      inference(unflattening,[status(thm)],[c_456]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_823,plain,
% 2.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.36/1.00      | X2 != X1
% 2.36/1.00      | sK0(X2) != X0
% 2.36/1.00      | sK0(X2) = X2 ),
% 2.36/1.00      inference(resolution_lifted,[status(thm)],[c_251,c_457]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_824,plain,
% 2.36/1.00      ( ~ m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) | sK0(X0) = X0 ),
% 2.36/1.00      inference(unflattening,[status(thm)],[c_823]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_828,plain,
% 2.36/1.00      ( sK0(X0) = X0 ),
% 2.36/1.00      inference(global_propositional_subsumption,
% 2.36/1.00                [status(thm)],
% 2.36/1.00                [c_824,c_2]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1419,plain,
% 2.36/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.36/1.00      inference(light_normalisation,[status(thm)],[c_1411,c_828]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_22,plain,
% 2.36/1.00      ( ~ v2_tex_2(X0,X1)
% 2.36/1.00      | ~ r1_tarski(X2,X0)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.36/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.36/1.00      | v2_struct_0(X1)
% 2.36/1.00      | ~ v2_pre_topc(X1)
% 2.36/1.00      | ~ l1_pre_topc(X1)
% 2.36/1.00      | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2 ),
% 2.36/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_720,plain,
% 2.36/1.00      ( ~ v2_tex_2(X0,X1)
% 2.36/1.00      | ~ r1_tarski(X2,X0)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.36/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.36/1.00      | ~ v2_pre_topc(X1)
% 2.36/1.00      | ~ l1_pre_topc(X1)
% 2.36/1.00      | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2
% 2.36/1.00      | sK3 != X1 ),
% 2.36/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_32]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_721,plain,
% 2.36/1.00      ( ~ v2_tex_2(X0,sK3)
% 2.36/1.00      | ~ r1_tarski(X1,X0)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.36/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.36/1.00      | ~ v2_pre_topc(sK3)
% 2.36/1.00      | ~ l1_pre_topc(sK3)
% 2.36/1.00      | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
% 2.36/1.00      inference(unflattening,[status(thm)],[c_720]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_31,negated_conjecture,
% 2.36/1.00      ( v2_pre_topc(sK3) ),
% 2.36/1.00      inference(cnf_transformation,[],[f88]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_23,plain,
% 2.36/1.00      ( v2_tex_2(X0,X1)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.36/1.00      | v2_struct_0(X1)
% 2.36/1.00      | ~ v1_tdlat_3(X1)
% 2.36/1.00      | ~ v2_pre_topc(X1)
% 2.36/1.00      | ~ l1_pre_topc(X1) ),
% 2.36/1.00      inference(cnf_transformation,[],[f84]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_632,plain,
% 2.36/1.00      ( v2_tex_2(X0,X1)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.36/1.00      | v2_struct_0(X1)
% 2.36/1.00      | ~ v2_pre_topc(X1)
% 2.36/1.00      | ~ l1_pre_topc(X1)
% 2.36/1.00      | sK3 != X1 ),
% 2.36/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_30]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_633,plain,
% 2.36/1.00      ( v2_tex_2(X0,sK3)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.36/1.00      | v2_struct_0(sK3)
% 2.36/1.00      | ~ v2_pre_topc(sK3)
% 2.36/1.00      | ~ l1_pre_topc(sK3) ),
% 2.36/1.00      inference(unflattening,[status(thm)],[c_632]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_637,plain,
% 2.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.36/1.00      | v2_tex_2(X0,sK3) ),
% 2.36/1.00      inference(global_propositional_subsumption,
% 2.36/1.00                [status(thm)],
% 2.36/1.00                [c_633,c_32,c_31,c_29]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_638,plain,
% 2.36/1.00      ( v2_tex_2(X0,sK3)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.36/1.00      inference(renaming,[status(thm)],[c_637]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_725,plain,
% 2.36/1.00      ( ~ r1_tarski(X1,X0)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.36/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.36/1.00      | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
% 2.36/1.00      inference(global_propositional_subsumption,
% 2.36/1.00                [status(thm)],
% 2.36/1.00                [c_721,c_32,c_31,c_29,c_633]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_726,plain,
% 2.36/1.00      ( ~ r1_tarski(X0,X1)
% 2.36/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.36/1.00      | k9_subset_1(u1_struct_0(sK3),X1,k2_pre_topc(sK3,X0)) = X0 ),
% 2.36/1.00      inference(renaming,[status(thm)],[c_725]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_774,plain,
% 2.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.36/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.36/1.00      | k9_subset_1(u1_struct_0(sK3),X1,k2_pre_topc(sK3,X0)) = X0 ),
% 2.36/1.00      inference(resolution,[status(thm)],[c_251,c_726]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1409,plain,
% 2.36/1.00      ( k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1
% 2.36/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 2.36/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.36/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_774]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2374,plain,
% 2.36/1.00      ( k9_subset_1(k2_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1
% 2.36/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 2.36/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 2.36/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.36/1.00      inference(light_normalisation,[status(thm)],[c_1409,c_2197]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2382,plain,
% 2.36/1.00      ( k9_subset_1(k2_struct_0(sK3),k2_struct_0(sK3),k2_pre_topc(sK3,X0)) = X0
% 2.36/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.36/1.00      inference(superposition,[status(thm)],[c_1419,c_2374]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2582,plain,
% 2.36/1.00      ( k9_subset_1(k2_struct_0(sK3),k2_struct_0(sK3),k2_pre_topc(sK3,sK4)) = sK4 ),
% 2.36/1.00      inference(superposition,[status(thm)],[c_2208,c_2382]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2688,plain,
% 2.36/1.00      ( k9_subset_1(k2_struct_0(sK3),k2_struct_0(sK3),k2_struct_0(sK3)) = sK4
% 2.36/1.00      | k2_struct_0(sK3) = sK4 ),
% 2.36/1.00      inference(superposition,[status(thm)],[c_2574,c_2582]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_0,plain,
% 2.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | k9_subset_1(X1,X2,X2) = X2 ),
% 2.36/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1412,plain,
% 2.36/1.00      ( k9_subset_1(X0,X1,X1) = X1
% 2.36/1.00      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1935,plain,
% 2.36/1.00      ( k9_subset_1(X0,X1,X1) = X1 ),
% 2.36/1.00      inference(superposition,[status(thm)],[c_1419,c_1412]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2689,plain,
% 2.36/1.00      ( k2_struct_0(sK3) = sK4 ),
% 2.36/1.00      inference(demodulation,[status(thm)],[c_2688,c_1935]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_3282,plain,
% 2.36/1.00      ( k2_pre_topc(sK3,sK4) = sK4 ),
% 2.36/1.00      inference(demodulation,[status(thm)],[c_2689,c_2130]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_26,negated_conjecture,
% 2.36/1.00      ( ~ v3_tex_2(sK4,sK3) | v1_subset_1(sK4,u1_struct_0(sK3)) ),
% 2.36/1.00      inference(cnf_transformation,[],[f93]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_257,plain,
% 2.36/1.00      ( ~ v3_tex_2(sK4,sK3) | v1_subset_1(sK4,u1_struct_0(sK3)) ),
% 2.36/1.00      inference(prop_impl,[status(thm)],[c_26]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_468,plain,
% 2.36/1.00      ( ~ v3_tex_2(sK4,sK3) | u1_struct_0(sK3) != X0 | sK0(X0) != sK4 ),
% 2.36/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_257]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_469,plain,
% 2.36/1.00      ( ~ v3_tex_2(sK4,sK3) | sK0(u1_struct_0(sK3)) != sK4 ),
% 2.36/1.00      inference(unflattening,[status(thm)],[c_468]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_25,plain,
% 2.36/1.00      ( v3_tex_2(X0,X1)
% 2.36/1.00      | ~ v2_tex_2(X0,X1)
% 2.36/1.00      | ~ v1_tops_1(X0,X1)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.36/1.00      | v2_struct_0(X1)
% 2.36/1.00      | ~ v2_pre_topc(X1)
% 2.36/1.00      | ~ l1_pre_topc(X1) ),
% 2.36/1.00      inference(cnf_transformation,[],[f86]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_685,plain,
% 2.36/1.00      ( v3_tex_2(X0,X1)
% 2.36/1.00      | ~ v2_tex_2(X0,X1)
% 2.36/1.00      | ~ v1_tops_1(X0,X1)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.36/1.00      | ~ v2_pre_topc(X1)
% 2.36/1.00      | ~ l1_pre_topc(X1)
% 2.36/1.00      | sK3 != X1 ),
% 2.36/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_32]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_686,plain,
% 2.36/1.00      ( v3_tex_2(X0,sK3)
% 2.36/1.00      | ~ v2_tex_2(X0,sK3)
% 2.36/1.00      | ~ v1_tops_1(X0,sK3)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.36/1.00      | ~ v2_pre_topc(sK3)
% 2.36/1.00      | ~ l1_pre_topc(sK3) ),
% 2.36/1.00      inference(unflattening,[status(thm)],[c_685]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_690,plain,
% 2.36/1.00      ( v3_tex_2(X0,sK3)
% 2.36/1.00      | ~ v1_tops_1(X0,sK3)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.36/1.00      inference(global_propositional_subsumption,
% 2.36/1.00                [status(thm)],
% 2.36/1.00                [c_686,c_32,c_31,c_29,c_633]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1026,plain,
% 2.36/1.00      ( ~ v1_tops_1(X0,sK3)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.36/1.00      | sK0(u1_struct_0(sK3)) != sK4
% 2.36/1.00      | sK3 != sK3
% 2.36/1.00      | sK4 != X0 ),
% 2.36/1.00      inference(resolution_lifted,[status(thm)],[c_469,c_690]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1027,plain,
% 2.36/1.00      ( ~ v1_tops_1(sK4,sK3)
% 2.36/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.36/1.00      | sK0(u1_struct_0(sK3)) != sK4 ),
% 2.36/1.00      inference(unflattening,[status(thm)],[c_1026]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1029,plain,
% 2.36/1.00      ( ~ v1_tops_1(sK4,sK3) | sK0(u1_struct_0(sK3)) != sK4 ),
% 2.36/1.00      inference(global_propositional_subsumption,
% 2.36/1.00                [status(thm)],
% 2.36/1.00                [c_1027,c_28]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1399,plain,
% 2.36/1.00      ( sK0(u1_struct_0(sK3)) != sK4
% 2.36/1.00      | v1_tops_1(sK4,sK3) != iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_1029]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1429,plain,
% 2.36/1.00      ( u1_struct_0(sK3) != sK4 | v1_tops_1(sK4,sK3) != iProver_top ),
% 2.36/1.00      inference(demodulation,[status(thm)],[c_1399,c_828]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_3138,plain,
% 2.36/1.00      ( k2_struct_0(sK3) != sK4 | v1_tops_1(sK4,sK3) != iProver_top ),
% 2.36/1.00      inference(light_normalisation,[status(thm)],[c_1429,c_2197]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1152,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1613,plain,
% 2.36/1.00      ( k2_pre_topc(sK3,sK4) != X0
% 2.36/1.00      | k2_pre_topc(sK3,sK4) = u1_struct_0(sK3)
% 2.36/1.00      | u1_struct_0(sK3) != X0 ),
% 2.36/1.00      inference(instantiation,[status(thm)],[c_1152]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1713,plain,
% 2.36/1.00      ( k2_pre_topc(sK3,sK4) = u1_struct_0(sK3)
% 2.36/1.00      | k2_pre_topc(sK3,sK4) != sK4
% 2.36/1.00      | u1_struct_0(sK3) != sK4 ),
% 2.36/1.00      inference(instantiation,[status(thm)],[c_1613]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_12,plain,
% 2.36/1.00      ( v1_tops_1(X0,X1)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.36/1.00      | ~ l1_pre_topc(X1)
% 2.36/1.00      | k2_pre_topc(X1,X0) != u1_struct_0(X1) ),
% 2.36/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_915,plain,
% 2.36/1.00      ( v1_tops_1(X0,X1)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.36/1.00      | k2_pre_topc(X1,X0) != u1_struct_0(X1)
% 2.36/1.00      | sK3 != X1 ),
% 2.36/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_29]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_916,plain,
% 2.36/1.00      ( v1_tops_1(X0,sK3)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.36/1.00      | k2_pre_topc(sK3,X0) != u1_struct_0(sK3) ),
% 2.36/1.00      inference(unflattening,[status(thm)],[c_915]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1514,plain,
% 2.36/1.00      ( v1_tops_1(sK4,sK3)
% 2.36/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.36/1.00      | k2_pre_topc(sK3,sK4) != u1_struct_0(sK3) ),
% 2.36/1.00      inference(instantiation,[status(thm)],[c_916]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1515,plain,
% 2.36/1.00      ( k2_pre_topc(sK3,sK4) != u1_struct_0(sK3)
% 2.36/1.00      | v1_tops_1(sK4,sK3) = iProver_top
% 2.36/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_1514]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1000,plain,
% 2.36/1.00      ( u1_struct_0(sK3) = sK4 | v1_tops_1(sK4,sK3) = iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_998]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_37,plain,
% 2.36/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(contradiction,plain,
% 2.36/1.00      ( $false ),
% 2.36/1.00      inference(minisat,
% 2.36/1.00                [status(thm)],
% 2.36/1.00                [c_3282,c_3138,c_2689,c_1713,c_1515,c_1000,c_37]) ).
% 2.36/1.00  
% 2.36/1.00  
% 2.36/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.36/1.00  
% 2.36/1.00  ------                               Statistics
% 2.36/1.00  
% 2.36/1.00  ------ General
% 2.36/1.00  
% 2.36/1.00  abstr_ref_over_cycles:                  0
% 2.36/1.00  abstr_ref_under_cycles:                 0
% 2.36/1.00  gc_basic_clause_elim:                   0
% 2.36/1.00  forced_gc_time:                         0
% 2.36/1.00  parsing_time:                           0.009
% 2.36/1.00  unif_index_cands_time:                  0.
% 2.36/1.00  unif_index_add_time:                    0.
% 2.36/1.00  orderings_time:                         0.
% 2.36/1.00  out_proof_time:                         0.012
% 2.36/1.00  total_time:                             0.146
% 2.36/1.00  num_of_symbols:                         53
% 2.36/1.00  num_of_terms:                           2294
% 2.36/1.00  
% 2.36/1.00  ------ Preprocessing
% 2.36/1.00  
% 2.36/1.00  num_of_splits:                          0
% 2.36/1.00  num_of_split_atoms:                     0
% 2.36/1.00  num_of_reused_defs:                     0
% 2.36/1.00  num_eq_ax_congr_red:                    17
% 2.36/1.00  num_of_sem_filtered_clauses:            1
% 2.36/1.00  num_of_subtypes:                        0
% 2.36/1.00  monotx_restored_types:                  0
% 2.36/1.00  sat_num_of_epr_types:                   0
% 2.36/1.00  sat_num_of_non_cyclic_types:            0
% 2.36/1.00  sat_guarded_non_collapsed_types:        0
% 2.36/1.00  num_pure_diseq_elim:                    0
% 2.36/1.00  simp_replaced_by:                       0
% 2.36/1.00  res_preprocessed:                       102
% 2.36/1.00  prep_upred:                             0
% 2.36/1.00  prep_unflattend:                        39
% 2.36/1.00  smt_new_axioms:                         0
% 2.36/1.00  pred_elim_cands:                        2
% 2.36/1.00  pred_elim:                              10
% 2.36/1.00  pred_elim_cl:                           17
% 2.36/1.00  pred_elim_cycles:                       13
% 2.36/1.00  merged_defs:                            4
% 2.36/1.00  merged_defs_ncl:                        0
% 2.36/1.00  bin_hyper_res:                          6
% 2.36/1.00  prep_cycles:                            4
% 2.36/1.00  pred_elim_time:                         0.025
% 2.36/1.00  splitting_time:                         0.
% 2.36/1.00  sem_filter_time:                        0.
% 2.36/1.00  monotx_time:                            0.
% 2.36/1.00  subtype_inf_time:                       0.
% 2.36/1.00  
% 2.36/1.00  ------ Problem properties
% 2.36/1.00  
% 2.36/1.00  clauses:                                16
% 2.36/1.00  conjectures:                            1
% 2.36/1.00  epr:                                    0
% 2.36/1.00  horn:                                   15
% 2.36/1.00  ground:                                 7
% 2.36/1.00  unary:                                  5
% 2.36/1.00  binary:                                 4
% 2.36/1.00  lits:                                   37
% 2.36/1.00  lits_eq:                                12
% 2.36/1.00  fd_pure:                                0
% 2.36/1.00  fd_pseudo:                              0
% 2.36/1.00  fd_cond:                                0
% 2.36/1.00  fd_pseudo_cond:                         0
% 2.36/1.00  ac_symbols:                             0
% 2.36/1.00  
% 2.36/1.00  ------ Propositional Solver
% 2.36/1.00  
% 2.36/1.00  prop_solver_calls:                      27
% 2.36/1.00  prop_fast_solver_calls:                 798
% 2.36/1.00  smt_solver_calls:                       0
% 2.36/1.00  smt_fast_solver_calls:                  0
% 2.36/1.00  prop_num_of_clauses:                    1080
% 2.36/1.00  prop_preprocess_simplified:             3930
% 2.36/1.00  prop_fo_subsumed:                       32
% 2.36/1.00  prop_solver_time:                       0.
% 2.36/1.00  smt_solver_time:                        0.
% 2.36/1.00  smt_fast_solver_time:                   0.
% 2.36/1.00  prop_fast_solver_time:                  0.
% 2.36/1.00  prop_unsat_core_time:                   0.
% 2.36/1.00  
% 2.36/1.00  ------ QBF
% 2.36/1.00  
% 2.36/1.00  qbf_q_res:                              0
% 2.36/1.00  qbf_num_tautologies:                    0
% 2.36/1.00  qbf_prep_cycles:                        0
% 2.36/1.00  
% 2.36/1.00  ------ BMC1
% 2.36/1.00  
% 2.36/1.00  bmc1_current_bound:                     -1
% 2.36/1.00  bmc1_last_solved_bound:                 -1
% 2.36/1.00  bmc1_unsat_core_size:                   -1
% 2.36/1.00  bmc1_unsat_core_parents_size:           -1
% 2.36/1.00  bmc1_merge_next_fun:                    0
% 2.36/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.36/1.00  
% 2.36/1.00  ------ Instantiation
% 2.36/1.00  
% 2.36/1.00  inst_num_of_clauses:                    300
% 2.36/1.00  inst_num_in_passive:                    99
% 2.36/1.00  inst_num_in_active:                     151
% 2.36/1.00  inst_num_in_unprocessed:                50
% 2.36/1.00  inst_num_of_loops:                      160
% 2.36/1.00  inst_num_of_learning_restarts:          0
% 2.36/1.00  inst_num_moves_active_passive:          7
% 2.36/1.00  inst_lit_activity:                      0
% 2.36/1.00  inst_lit_activity_moves:                0
% 2.36/1.00  inst_num_tautologies:                   0
% 2.36/1.00  inst_num_prop_implied:                  0
% 2.36/1.00  inst_num_existing_simplified:           0
% 2.36/1.00  inst_num_eq_res_simplified:             0
% 2.36/1.00  inst_num_child_elim:                    0
% 2.36/1.00  inst_num_of_dismatching_blockings:      67
% 2.36/1.00  inst_num_of_non_proper_insts:           270
% 2.36/1.00  inst_num_of_duplicates:                 0
% 2.36/1.00  inst_inst_num_from_inst_to_res:         0
% 2.36/1.00  inst_dismatching_checking_time:         0.
% 2.36/1.00  
% 2.36/1.00  ------ Resolution
% 2.36/1.00  
% 2.36/1.00  res_num_of_clauses:                     0
% 2.36/1.00  res_num_in_passive:                     0
% 2.36/1.00  res_num_in_active:                      0
% 2.36/1.00  res_num_of_loops:                       106
% 2.36/1.00  res_forward_subset_subsumed:            35
% 2.36/1.00  res_backward_subset_subsumed:           0
% 2.36/1.00  res_forward_subsumed:                   1
% 2.36/1.00  res_backward_subsumed:                  0
% 2.36/1.00  res_forward_subsumption_resolution:     1
% 2.36/1.00  res_backward_subsumption_resolution:    0
% 2.36/1.00  res_clause_to_clause_subsumption:       132
% 2.36/1.00  res_orphan_elimination:                 0
% 2.36/1.00  res_tautology_del:                      35
% 2.36/1.00  res_num_eq_res_simplified:              0
% 2.36/1.00  res_num_sel_changes:                    0
% 2.36/1.00  res_moves_from_active_to_pass:          0
% 2.36/1.00  
% 2.36/1.00  ------ Superposition
% 2.36/1.00  
% 2.36/1.00  sup_time_total:                         0.
% 2.36/1.00  sup_time_generating:                    0.
% 2.36/1.00  sup_time_sim_full:                      0.
% 2.36/1.00  sup_time_sim_immed:                     0.
% 2.36/1.00  
% 2.36/1.00  sup_num_of_clauses:                     17
% 2.36/1.00  sup_num_in_active:                      4
% 2.36/1.00  sup_num_in_passive:                     13
% 2.36/1.00  sup_num_of_loops:                       30
% 2.36/1.00  sup_fw_superposition:                   28
% 2.36/1.00  sup_bw_superposition:                   6
% 2.36/1.00  sup_immediate_simplified:               13
% 2.36/1.00  sup_given_eliminated:                   0
% 2.36/1.00  comparisons_done:                       0
% 2.36/1.00  comparisons_avoided:                    0
% 2.36/1.00  
% 2.36/1.00  ------ Simplifications
% 2.36/1.00  
% 2.36/1.00  
% 2.36/1.00  sim_fw_subset_subsumed:                 9
% 2.36/1.00  sim_bw_subset_subsumed:                 2
% 2.36/1.00  sim_fw_subsumed:                        5
% 2.36/1.00  sim_bw_subsumed:                        0
% 2.36/1.00  sim_fw_subsumption_res:                 1
% 2.36/1.00  sim_bw_subsumption_res:                 0
% 2.36/1.00  sim_tautology_del:                      3
% 2.36/1.00  sim_eq_tautology_del:                   3
% 2.36/1.00  sim_eq_res_simp:                        0
% 2.36/1.00  sim_fw_demodulated:                     4
% 2.36/1.00  sim_bw_demodulated:                     25
% 2.36/1.00  sim_light_normalised:                   12
% 2.36/1.00  sim_joinable_taut:                      0
% 2.36/1.00  sim_joinable_simp:                      0
% 2.36/1.00  sim_ac_normalised:                      0
% 2.36/1.00  sim_smt_subsumption:                    0
% 2.36/1.00  
%------------------------------------------------------------------------------
