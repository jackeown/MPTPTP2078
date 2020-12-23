%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:15 EST 2020

% Result     : Theorem 0.95s
% Output     : CNFRefutation 0.95s
% Verified   : 
% Statistics : Number of formulae       :  139 (1212 expanded)
%              Number of clauses        :   77 ( 284 expanded)
%              Number of leaves         :   14 ( 270 expanded)
%              Depth                    :   28
%              Number of atoms          :  582 (8037 expanded)
%              Number of equality atoms :   99 ( 291 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | u1_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f66,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f42,plain,
    ( ( v1_subset_1(sK2,u1_struct_0(sK1))
      | ~ v3_tex_2(sK2,sK1) )
    & ( ~ v1_subset_1(sK2,u1_struct_0(sK1))
      | v3_tex_2(sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v1_tdlat_3(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f39,f41,f40])).

fof(f65,plain,
    ( v1_subset_1(sK2,u1_struct_0(sK1))
    | ~ v3_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_tex_2(X1,X0)
              & v1_tops_1(X1,X0) )
           => v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f48,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f59,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f61,plain,(
    v1_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f62,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f63,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK0(X0),X0)
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).

fof(f53,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f60,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f64,plain,
    ( ~ v1_subset_1(sK2,u1_struct_0(sK1))
    | v3_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tex_2(X1,X0)
              & v3_pre_topc(X1,X0) )
           => v1_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_6,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_9,plain,
    ( ~ v1_subset_1(X0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_16,negated_conjecture,
    ( ~ v3_tex_2(sK2,sK1)
    | v1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_170,plain,
    ( ~ v3_tex_2(sK2,sK1)
    | v1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_320,plain,
    ( ~ v3_tex_2(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X0))
    | u1_struct_0(sK1) != X0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_170])).

cnf(c_321,plain,
    ( ~ v3_tex_2(sK2,sK1)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK2 != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_320])).

cnf(c_13,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_15,plain,
    ( v3_tex_2(X0,X1)
    | ~ v2_tex_2(X0,X1)
    | ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_340,plain,
    ( v3_tex_2(X0,X1)
    | ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_13,c_15])).

cnf(c_5,plain,
    ( ~ v1_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_358,plain,
    ( v3_tex_2(X0,X1)
    | ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_340,c_5])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_375,plain,
    ( v3_tex_2(X0,X1)
    | ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_358,c_22])).

cnf(c_376,plain,
    ( v3_tex_2(X0,sK1)
    | ~ v1_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_20,negated_conjecture,
    ( v1_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_380,plain,
    ( v3_tex_2(X0,sK1)
    | ~ v1_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_376,c_20,c_19])).

cnf(c_448,plain,
    ( ~ v1_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_struct_0(sK1) != sK2
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_321,c_380])).

cnf(c_449,plain,
    ( ~ v1_tops_1(sK2,sK1)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_struct_0(sK1) != sK2 ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_451,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_tops_1(sK2,sK1)
    | u1_struct_0(sK1) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_449,c_18])).

cnf(c_452,plain,
    ( ~ v1_tops_1(sK2,sK1)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_struct_0(sK1) != sK2 ),
    inference(renaming,[status(thm)],[c_451])).

cnf(c_475,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != u1_struct_0(X1)
    | u1_struct_0(sK1) != sK2
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_452])).

cnf(c_476,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k2_pre_topc(sK1,sK2) != u1_struct_0(sK1)
    | u1_struct_0(sK1) != sK2 ),
    inference(unflattening,[status(thm)],[c_475])).

cnf(c_478,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,sK2) != u1_struct_0(sK1)
    | u1_struct_0(sK1) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_476,c_19,c_18])).

cnf(c_703,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,sK2) != u1_struct_0(sK1)
    | u1_struct_0(sK1) != sK2 ),
    inference(subtyping,[status(esa)],[c_478])).

cnf(c_798,plain,
    ( k2_pre_topc(sK1,sK2) != u1_struct_0(sK1)
    | u1_struct_0(sK1) != sK2
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_703])).

cnf(c_723,plain,
    ( k2_pre_topc(sK1,sK2) != u1_struct_0(sK1)
    | u1_struct_0(sK1) != sK2
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_703])).

cnf(c_704,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_797,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_704])).

cnf(c_12,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_553,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_554,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_tdlat_3(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_553])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_558,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_554,c_21,c_20])).

cnf(c_3,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_538,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_19])).

cnf(c_539,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),X0),sK1)
    | v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_538])).

cnf(c_638,plain,
    ( v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_subset_1(u1_struct_0(sK1),X0) != X1
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_558,c_539])).

cnf(c_639,plain,
    ( v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_638])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_649,plain,
    ( v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_639,c_0])).

cnf(c_2,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_571,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_19])).

cnf(c_572,plain,
    ( ~ v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_571])).

cnf(c_663,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,X0) = X0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_649,c_572])).

cnf(c_701,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,X0_46) = X0_46 ),
    inference(subtyping,[status(esa)],[c_663])).

cnf(c_799,plain,
    ( k2_pre_topc(sK1,X0_46) = X0_46
    | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_701])).

cnf(c_892,plain,
    ( k2_pre_topc(sK1,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_797,c_799])).

cnf(c_7,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_8,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_17,negated_conjecture,
    ( v3_tex_2(sK2,sK1)
    | ~ v1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_168,plain,
    ( v3_tex_2(sK2,sK1)
    | ~ v1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_306,plain,
    ( v3_tex_2(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 = X0
    | u1_struct_0(sK1) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_168])).

cnf(c_307,plain,
    ( v3_tex_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_struct_0(sK1) = sK2 ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_309,plain,
    ( v3_tex_2(sK2,sK1)
    | u1_struct_0(sK1) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_307,c_18])).

cnf(c_14,plain,
    ( ~ v3_tex_2(X0,X1)
    | v1_tops_1(X0,X1)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_396,plain,
    ( ~ v3_tex_2(X0,X1)
    | v1_tops_1(X0,X1)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_397,plain,
    ( ~ v3_tex_2(X0,sK1)
    | v1_tops_1(X0,sK1)
    | ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_401,plain,
    ( ~ v3_tex_2(X0,sK1)
    | v1_tops_1(X0,sK1)
    | ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_397,c_21,c_19])).

cnf(c_431,plain,
    ( v1_tops_1(X0,sK1)
    | ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_struct_0(sK1) = sK2
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_309,c_401])).

cnf(c_432,plain,
    ( v1_tops_1(sK2,sK1)
    | ~ v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_struct_0(sK1) = sK2 ),
    inference(unflattening,[status(thm)],[c_431])).

cnf(c_434,plain,
    ( ~ v3_pre_topc(sK2,sK1)
    | v1_tops_1(sK2,sK1)
    | u1_struct_0(sK1) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_432,c_18])).

cnf(c_435,plain,
    ( v1_tops_1(sK2,sK1)
    | ~ v3_pre_topc(sK2,sK1)
    | u1_struct_0(sK1) = sK2 ),
    inference(renaming,[status(thm)],[c_434])).

cnf(c_492,plain,
    ( ~ v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1)
    | u1_struct_0(sK1) = sK2
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_435])).

cnf(c_493,plain,
    ( ~ v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1)
    | u1_struct_0(sK1) = sK2 ),
    inference(unflattening,[status(thm)],[c_492])).

cnf(c_495,plain,
    ( ~ v3_pre_topc(sK2,sK1)
    | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1)
    | u1_struct_0(sK1) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_493,c_19,c_18])).

cnf(c_627,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1)
    | u1_struct_0(sK1) = sK2
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_558,c_495])).

cnf(c_628,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1)
    | u1_struct_0(sK1) = sK2 ),
    inference(unflattening,[status(thm)],[c_627])).

cnf(c_630,plain,
    ( k2_pre_topc(sK1,sK2) = u1_struct_0(sK1)
    | u1_struct_0(sK1) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_628,c_18])).

cnf(c_702,plain,
    ( k2_pre_topc(sK1,sK2) = u1_struct_0(sK1)
    | u1_struct_0(sK1) = sK2 ),
    inference(subtyping,[status(esa)],[c_630])).

cnf(c_894,plain,
    ( u1_struct_0(sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_892,c_702])).

cnf(c_1015,plain,
    ( k2_pre_topc(sK1,sK2) != u1_struct_0(sK1)
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_798,c_723,c_894])).

cnf(c_1019,plain,
    ( sK2 != sK2
    | m1_subset_1(sK2,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1015,c_892,c_894])).

cnf(c_1020,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1019])).

cnf(c_926,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_894,c_797])).

cnf(c_1022,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1020,c_926])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:36:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.95/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.95/0.99  
% 0.95/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.95/0.99  
% 0.95/0.99  ------  iProver source info
% 0.95/0.99  
% 0.95/0.99  git: date: 2020-06-30 10:37:57 +0100
% 0.95/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.95/0.99  git: non_committed_changes: false
% 0.95/0.99  git: last_make_outside_of_git: false
% 0.95/0.99  
% 0.95/0.99  ------ 
% 0.95/0.99  
% 0.95/0.99  ------ Input Options
% 0.95/0.99  
% 0.95/0.99  --out_options                           all
% 0.95/0.99  --tptp_safe_out                         true
% 0.95/0.99  --problem_path                          ""
% 0.95/0.99  --include_path                          ""
% 0.95/0.99  --clausifier                            res/vclausify_rel
% 0.95/0.99  --clausifier_options                    --mode clausify
% 0.95/0.99  --stdin                                 false
% 0.95/0.99  --stats_out                             all
% 0.95/0.99  
% 0.95/0.99  ------ General Options
% 0.95/0.99  
% 0.95/0.99  --fof                                   false
% 0.95/0.99  --time_out_real                         305.
% 0.95/0.99  --time_out_virtual                      -1.
% 0.95/0.99  --symbol_type_check                     false
% 0.95/0.99  --clausify_out                          false
% 0.95/0.99  --sig_cnt_out                           false
% 0.95/0.99  --trig_cnt_out                          false
% 0.95/0.99  --trig_cnt_out_tolerance                1.
% 0.95/0.99  --trig_cnt_out_sk_spl                   false
% 0.95/0.99  --abstr_cl_out                          false
% 0.95/0.99  
% 0.95/0.99  ------ Global Options
% 0.95/0.99  
% 0.95/0.99  --schedule                              default
% 0.95/0.99  --add_important_lit                     false
% 0.95/0.99  --prop_solver_per_cl                    1000
% 0.95/0.99  --min_unsat_core                        false
% 0.95/0.99  --soft_assumptions                      false
% 0.95/0.99  --soft_lemma_size                       3
% 0.95/0.99  --prop_impl_unit_size                   0
% 0.95/0.99  --prop_impl_unit                        []
% 0.95/0.99  --share_sel_clauses                     true
% 0.95/0.99  --reset_solvers                         false
% 0.95/0.99  --bc_imp_inh                            [conj_cone]
% 0.95/0.99  --conj_cone_tolerance                   3.
% 0.95/0.99  --extra_neg_conj                        none
% 0.95/0.99  --large_theory_mode                     true
% 0.95/0.99  --prolific_symb_bound                   200
% 0.95/0.99  --lt_threshold                          2000
% 0.95/0.99  --clause_weak_htbl                      true
% 0.95/0.99  --gc_record_bc_elim                     false
% 0.95/0.99  
% 0.95/0.99  ------ Preprocessing Options
% 0.95/0.99  
% 0.95/0.99  --preprocessing_flag                    true
% 0.95/0.99  --time_out_prep_mult                    0.1
% 0.95/0.99  --splitting_mode                        input
% 0.95/0.99  --splitting_grd                         true
% 0.95/0.99  --splitting_cvd                         false
% 0.95/0.99  --splitting_cvd_svl                     false
% 0.95/0.99  --splitting_nvd                         32
% 0.95/0.99  --sub_typing                            true
% 0.95/0.99  --prep_gs_sim                           true
% 0.95/0.99  --prep_unflatten                        true
% 0.95/0.99  --prep_res_sim                          true
% 0.95/0.99  --prep_upred                            true
% 0.95/0.99  --prep_sem_filter                       exhaustive
% 0.95/0.99  --prep_sem_filter_out                   false
% 0.95/0.99  --pred_elim                             true
% 0.95/0.99  --res_sim_input                         true
% 0.95/0.99  --eq_ax_congr_red                       true
% 0.95/0.99  --pure_diseq_elim                       true
% 0.95/0.99  --brand_transform                       false
% 0.95/0.99  --non_eq_to_eq                          false
% 0.95/0.99  --prep_def_merge                        true
% 0.95/0.99  --prep_def_merge_prop_impl              false
% 0.95/0.99  --prep_def_merge_mbd                    true
% 0.95/0.99  --prep_def_merge_tr_red                 false
% 0.95/0.99  --prep_def_merge_tr_cl                  false
% 0.95/0.99  --smt_preprocessing                     true
% 0.95/0.99  --smt_ac_axioms                         fast
% 0.95/0.99  --preprocessed_out                      false
% 0.95/0.99  --preprocessed_stats                    false
% 0.95/0.99  
% 0.95/0.99  ------ Abstraction refinement Options
% 0.95/0.99  
% 0.95/0.99  --abstr_ref                             []
% 0.95/0.99  --abstr_ref_prep                        false
% 0.95/0.99  --abstr_ref_until_sat                   false
% 0.95/0.99  --abstr_ref_sig_restrict                funpre
% 0.95/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 0.95/0.99  --abstr_ref_under                       []
% 0.95/0.99  
% 0.95/0.99  ------ SAT Options
% 0.95/0.99  
% 0.95/0.99  --sat_mode                              false
% 0.95/0.99  --sat_fm_restart_options                ""
% 0.95/0.99  --sat_gr_def                            false
% 0.95/0.99  --sat_epr_types                         true
% 0.95/0.99  --sat_non_cyclic_types                  false
% 0.95/0.99  --sat_finite_models                     false
% 0.95/0.99  --sat_fm_lemmas                         false
% 0.95/0.99  --sat_fm_prep                           false
% 0.95/0.99  --sat_fm_uc_incr                        true
% 0.95/0.99  --sat_out_model                         small
% 0.95/0.99  --sat_out_clauses                       false
% 0.95/0.99  
% 0.95/0.99  ------ QBF Options
% 0.95/0.99  
% 0.95/0.99  --qbf_mode                              false
% 0.95/0.99  --qbf_elim_univ                         false
% 0.95/0.99  --qbf_dom_inst                          none
% 0.95/0.99  --qbf_dom_pre_inst                      false
% 0.95/0.99  --qbf_sk_in                             false
% 0.95/0.99  --qbf_pred_elim                         true
% 0.95/0.99  --qbf_split                             512
% 0.95/0.99  
% 0.95/0.99  ------ BMC1 Options
% 0.95/0.99  
% 0.95/0.99  --bmc1_incremental                      false
% 0.95/0.99  --bmc1_axioms                           reachable_all
% 0.95/0.99  --bmc1_min_bound                        0
% 0.95/0.99  --bmc1_max_bound                        -1
% 0.95/0.99  --bmc1_max_bound_default                -1
% 0.95/0.99  --bmc1_symbol_reachability              true
% 0.95/0.99  --bmc1_property_lemmas                  false
% 0.95/0.99  --bmc1_k_induction                      false
% 0.95/0.99  --bmc1_non_equiv_states                 false
% 0.95/0.99  --bmc1_deadlock                         false
% 0.95/0.99  --bmc1_ucm                              false
% 0.95/0.99  --bmc1_add_unsat_core                   none
% 0.95/0.99  --bmc1_unsat_core_children              false
% 0.95/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 0.95/0.99  --bmc1_out_stat                         full
% 0.95/0.99  --bmc1_ground_init                      false
% 0.95/0.99  --bmc1_pre_inst_next_state              false
% 0.95/0.99  --bmc1_pre_inst_state                   false
% 0.95/0.99  --bmc1_pre_inst_reach_state             false
% 0.95/0.99  --bmc1_out_unsat_core                   false
% 0.95/0.99  --bmc1_aig_witness_out                  false
% 0.95/0.99  --bmc1_verbose                          false
% 0.95/0.99  --bmc1_dump_clauses_tptp                false
% 0.95/0.99  --bmc1_dump_unsat_core_tptp             false
% 0.95/0.99  --bmc1_dump_file                        -
% 0.95/0.99  --bmc1_ucm_expand_uc_limit              128
% 0.95/0.99  --bmc1_ucm_n_expand_iterations          6
% 0.95/0.99  --bmc1_ucm_extend_mode                  1
% 0.95/0.99  --bmc1_ucm_init_mode                    2
% 0.95/0.99  --bmc1_ucm_cone_mode                    none
% 0.95/0.99  --bmc1_ucm_reduced_relation_type        0
% 0.95/0.99  --bmc1_ucm_relax_model                  4
% 0.95/0.99  --bmc1_ucm_full_tr_after_sat            true
% 0.95/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 0.95/0.99  --bmc1_ucm_layered_model                none
% 0.95/0.99  --bmc1_ucm_max_lemma_size               10
% 0.95/0.99  
% 0.95/0.99  ------ AIG Options
% 0.95/0.99  
% 0.95/0.99  --aig_mode                              false
% 0.95/0.99  
% 0.95/0.99  ------ Instantiation Options
% 0.95/0.99  
% 0.95/0.99  --instantiation_flag                    true
% 0.95/0.99  --inst_sos_flag                         false
% 0.95/0.99  --inst_sos_phase                        true
% 0.95/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.95/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.95/0.99  --inst_lit_sel_side                     num_symb
% 0.95/0.99  --inst_solver_per_active                1400
% 0.95/0.99  --inst_solver_calls_frac                1.
% 0.95/0.99  --inst_passive_queue_type               priority_queues
% 0.95/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.95/0.99  --inst_passive_queues_freq              [25;2]
% 0.95/0.99  --inst_dismatching                      true
% 0.95/0.99  --inst_eager_unprocessed_to_passive     true
% 0.95/0.99  --inst_prop_sim_given                   true
% 0.95/0.99  --inst_prop_sim_new                     false
% 0.95/0.99  --inst_subs_new                         false
% 0.95/0.99  --inst_eq_res_simp                      false
% 0.95/0.99  --inst_subs_given                       false
% 0.95/0.99  --inst_orphan_elimination               true
% 0.95/0.99  --inst_learning_loop_flag               true
% 0.95/0.99  --inst_learning_start                   3000
% 0.95/0.99  --inst_learning_factor                  2
% 0.95/0.99  --inst_start_prop_sim_after_learn       3
% 0.95/0.99  --inst_sel_renew                        solver
% 0.95/0.99  --inst_lit_activity_flag                true
% 0.95/0.99  --inst_restr_to_given                   false
% 0.95/0.99  --inst_activity_threshold               500
% 0.95/0.99  --inst_out_proof                        true
% 0.95/0.99  
% 0.95/0.99  ------ Resolution Options
% 0.95/0.99  
% 0.95/0.99  --resolution_flag                       true
% 0.95/0.99  --res_lit_sel                           adaptive
% 0.95/0.99  --res_lit_sel_side                      none
% 0.95/0.99  --res_ordering                          kbo
% 0.95/0.99  --res_to_prop_solver                    active
% 0.95/0.99  --res_prop_simpl_new                    false
% 0.95/0.99  --res_prop_simpl_given                  true
% 0.95/0.99  --res_passive_queue_type                priority_queues
% 0.95/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.95/0.99  --res_passive_queues_freq               [15;5]
% 0.95/0.99  --res_forward_subs                      full
% 0.95/0.99  --res_backward_subs                     full
% 0.95/0.99  --res_forward_subs_resolution           true
% 0.95/0.99  --res_backward_subs_resolution          true
% 0.95/0.99  --res_orphan_elimination                true
% 0.95/0.99  --res_time_limit                        2.
% 0.95/0.99  --res_out_proof                         true
% 0.95/0.99  
% 0.95/0.99  ------ Superposition Options
% 0.95/0.99  
% 0.95/0.99  --superposition_flag                    true
% 0.95/0.99  --sup_passive_queue_type                priority_queues
% 0.95/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.95/0.99  --sup_passive_queues_freq               [8;1;4]
% 0.95/0.99  --demod_completeness_check              fast
% 0.95/0.99  --demod_use_ground                      true
% 0.95/0.99  --sup_to_prop_solver                    passive
% 0.95/0.99  --sup_prop_simpl_new                    true
% 0.95/0.99  --sup_prop_simpl_given                  true
% 0.95/0.99  --sup_fun_splitting                     false
% 0.95/0.99  --sup_smt_interval                      50000
% 0.95/0.99  
% 0.95/0.99  ------ Superposition Simplification Setup
% 0.95/0.99  
% 0.95/0.99  --sup_indices_passive                   []
% 0.95/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.95/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.95/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.95/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 0.95/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.95/0.99  --sup_full_bw                           [BwDemod]
% 0.95/0.99  --sup_immed_triv                        [TrivRules]
% 0.95/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.95/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.95/0.99  --sup_immed_bw_main                     []
% 0.95/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.95/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 0.95/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.95/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.95/0.99  
% 0.95/0.99  ------ Combination Options
% 0.95/0.99  
% 0.95/0.99  --comb_res_mult                         3
% 0.95/0.99  --comb_sup_mult                         2
% 0.95/0.99  --comb_inst_mult                        10
% 0.95/0.99  
% 0.95/0.99  ------ Debug Options
% 0.95/0.99  
% 0.95/0.99  --dbg_backtrace                         false
% 0.95/0.99  --dbg_dump_prop_clauses                 false
% 0.95/0.99  --dbg_dump_prop_clauses_file            -
% 0.95/0.99  --dbg_out_stat                          false
% 0.95/0.99  ------ Parsing...
% 0.95/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.95/0.99  
% 0.95/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 0.95/0.99  
% 0.95/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.95/0.99  
% 0.95/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.95/0.99  ------ Proving...
% 0.95/0.99  ------ Problem Properties 
% 0.95/0.99  
% 0.95/0.99  
% 0.95/0.99  clauses                                 5
% 0.95/0.99  conjectures                             1
% 0.95/0.99  EPR                                     0
% 0.95/0.99  Horn                                    4
% 0.95/0.99  unary                                   1
% 0.95/0.99  binary                                  3
% 0.95/0.99  lits                                    10
% 0.95/0.99  lits eq                                 5
% 0.95/0.99  fd_pure                                 0
% 0.95/0.99  fd_pseudo                               0
% 0.95/0.99  fd_cond                                 0
% 0.95/0.99  fd_pseudo_cond                          0
% 0.95/0.99  AC symbols                              0
% 0.95/0.99  
% 0.95/0.99  ------ Schedule dynamic 5 is on 
% 0.95/0.99  
% 0.95/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.95/0.99  
% 0.95/0.99  
% 0.95/0.99  ------ 
% 0.95/0.99  Current options:
% 0.95/0.99  ------ 
% 0.95/0.99  
% 0.95/0.99  ------ Input Options
% 0.95/0.99  
% 0.95/0.99  --out_options                           all
% 0.95/0.99  --tptp_safe_out                         true
% 0.95/0.99  --problem_path                          ""
% 0.95/0.99  --include_path                          ""
% 0.95/0.99  --clausifier                            res/vclausify_rel
% 0.95/0.99  --clausifier_options                    --mode clausify
% 0.95/0.99  --stdin                                 false
% 0.95/0.99  --stats_out                             all
% 0.95/0.99  
% 0.95/0.99  ------ General Options
% 0.95/0.99  
% 0.95/0.99  --fof                                   false
% 0.95/0.99  --time_out_real                         305.
% 0.95/0.99  --time_out_virtual                      -1.
% 0.95/0.99  --symbol_type_check                     false
% 0.95/0.99  --clausify_out                          false
% 0.95/0.99  --sig_cnt_out                           false
% 0.95/0.99  --trig_cnt_out                          false
% 0.95/0.99  --trig_cnt_out_tolerance                1.
% 0.95/0.99  --trig_cnt_out_sk_spl                   false
% 0.95/0.99  --abstr_cl_out                          false
% 0.95/0.99  
% 0.95/0.99  ------ Global Options
% 0.95/0.99  
% 0.95/0.99  --schedule                              default
% 0.95/0.99  --add_important_lit                     false
% 0.95/0.99  --prop_solver_per_cl                    1000
% 0.95/0.99  --min_unsat_core                        false
% 0.95/0.99  --soft_assumptions                      false
% 0.95/0.99  --soft_lemma_size                       3
% 0.95/0.99  --prop_impl_unit_size                   0
% 0.95/0.99  --prop_impl_unit                        []
% 0.95/0.99  --share_sel_clauses                     true
% 0.95/0.99  --reset_solvers                         false
% 0.95/0.99  --bc_imp_inh                            [conj_cone]
% 0.95/0.99  --conj_cone_tolerance                   3.
% 0.95/0.99  --extra_neg_conj                        none
% 0.95/0.99  --large_theory_mode                     true
% 0.95/0.99  --prolific_symb_bound                   200
% 0.95/0.99  --lt_threshold                          2000
% 0.95/0.99  --clause_weak_htbl                      true
% 0.95/0.99  --gc_record_bc_elim                     false
% 0.95/0.99  
% 0.95/0.99  ------ Preprocessing Options
% 0.95/0.99  
% 0.95/0.99  --preprocessing_flag                    true
% 0.95/0.99  --time_out_prep_mult                    0.1
% 0.95/0.99  --splitting_mode                        input
% 0.95/0.99  --splitting_grd                         true
% 0.95/0.99  --splitting_cvd                         false
% 0.95/0.99  --splitting_cvd_svl                     false
% 0.95/0.99  --splitting_nvd                         32
% 0.95/0.99  --sub_typing                            true
% 0.95/0.99  --prep_gs_sim                           true
% 0.95/0.99  --prep_unflatten                        true
% 0.95/0.99  --prep_res_sim                          true
% 0.95/0.99  --prep_upred                            true
% 0.95/0.99  --prep_sem_filter                       exhaustive
% 0.95/0.99  --prep_sem_filter_out                   false
% 0.95/0.99  --pred_elim                             true
% 0.95/0.99  --res_sim_input                         true
% 0.95/0.99  --eq_ax_congr_red                       true
% 0.95/0.99  --pure_diseq_elim                       true
% 0.95/0.99  --brand_transform                       false
% 0.95/0.99  --non_eq_to_eq                          false
% 0.95/0.99  --prep_def_merge                        true
% 0.95/0.99  --prep_def_merge_prop_impl              false
% 0.95/0.99  --prep_def_merge_mbd                    true
% 0.95/0.99  --prep_def_merge_tr_red                 false
% 0.95/0.99  --prep_def_merge_tr_cl                  false
% 0.95/0.99  --smt_preprocessing                     true
% 0.95/0.99  --smt_ac_axioms                         fast
% 0.95/0.99  --preprocessed_out                      false
% 0.95/0.99  --preprocessed_stats                    false
% 0.95/0.99  
% 0.95/0.99  ------ Abstraction refinement Options
% 0.95/0.99  
% 0.95/0.99  --abstr_ref                             []
% 0.95/0.99  --abstr_ref_prep                        false
% 0.95/0.99  --abstr_ref_until_sat                   false
% 0.95/0.99  --abstr_ref_sig_restrict                funpre
% 0.95/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 0.95/0.99  --abstr_ref_under                       []
% 0.95/0.99  
% 0.95/0.99  ------ SAT Options
% 0.95/0.99  
% 0.95/0.99  --sat_mode                              false
% 0.95/0.99  --sat_fm_restart_options                ""
% 0.95/0.99  --sat_gr_def                            false
% 0.95/0.99  --sat_epr_types                         true
% 0.95/0.99  --sat_non_cyclic_types                  false
% 0.95/0.99  --sat_finite_models                     false
% 0.95/0.99  --sat_fm_lemmas                         false
% 0.95/0.99  --sat_fm_prep                           false
% 0.95/0.99  --sat_fm_uc_incr                        true
% 0.95/0.99  --sat_out_model                         small
% 0.95/0.99  --sat_out_clauses                       false
% 0.95/0.99  
% 0.95/0.99  ------ QBF Options
% 0.95/0.99  
% 0.95/0.99  --qbf_mode                              false
% 0.95/0.99  --qbf_elim_univ                         false
% 0.95/0.99  --qbf_dom_inst                          none
% 0.95/0.99  --qbf_dom_pre_inst                      false
% 0.95/0.99  --qbf_sk_in                             false
% 0.95/0.99  --qbf_pred_elim                         true
% 0.95/0.99  --qbf_split                             512
% 0.95/0.99  
% 0.95/0.99  ------ BMC1 Options
% 0.95/0.99  
% 0.95/0.99  --bmc1_incremental                      false
% 0.95/0.99  --bmc1_axioms                           reachable_all
% 0.95/0.99  --bmc1_min_bound                        0
% 0.95/0.99  --bmc1_max_bound                        -1
% 0.95/0.99  --bmc1_max_bound_default                -1
% 0.95/0.99  --bmc1_symbol_reachability              true
% 0.95/0.99  --bmc1_property_lemmas                  false
% 0.95/0.99  --bmc1_k_induction                      false
% 0.95/0.99  --bmc1_non_equiv_states                 false
% 0.95/0.99  --bmc1_deadlock                         false
% 0.95/0.99  --bmc1_ucm                              false
% 0.95/0.99  --bmc1_add_unsat_core                   none
% 0.95/0.99  --bmc1_unsat_core_children              false
% 0.95/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 0.95/0.99  --bmc1_out_stat                         full
% 0.95/0.99  --bmc1_ground_init                      false
% 0.95/0.99  --bmc1_pre_inst_next_state              false
% 0.95/0.99  --bmc1_pre_inst_state                   false
% 0.95/0.99  --bmc1_pre_inst_reach_state             false
% 0.95/0.99  --bmc1_out_unsat_core                   false
% 0.95/0.99  --bmc1_aig_witness_out                  false
% 0.95/0.99  --bmc1_verbose                          false
% 0.95/0.99  --bmc1_dump_clauses_tptp                false
% 0.95/0.99  --bmc1_dump_unsat_core_tptp             false
% 0.95/0.99  --bmc1_dump_file                        -
% 0.95/0.99  --bmc1_ucm_expand_uc_limit              128
% 0.95/0.99  --bmc1_ucm_n_expand_iterations          6
% 0.95/0.99  --bmc1_ucm_extend_mode                  1
% 0.95/0.99  --bmc1_ucm_init_mode                    2
% 0.95/0.99  --bmc1_ucm_cone_mode                    none
% 0.95/0.99  --bmc1_ucm_reduced_relation_type        0
% 0.95/0.99  --bmc1_ucm_relax_model                  4
% 0.95/0.99  --bmc1_ucm_full_tr_after_sat            true
% 0.95/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 0.95/0.99  --bmc1_ucm_layered_model                none
% 0.95/0.99  --bmc1_ucm_max_lemma_size               10
% 0.95/0.99  
% 0.95/0.99  ------ AIG Options
% 0.95/0.99  
% 0.95/0.99  --aig_mode                              false
% 0.95/0.99  
% 0.95/0.99  ------ Instantiation Options
% 0.95/0.99  
% 0.95/0.99  --instantiation_flag                    true
% 0.95/0.99  --inst_sos_flag                         false
% 0.95/0.99  --inst_sos_phase                        true
% 0.95/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.95/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.95/0.99  --inst_lit_sel_side                     none
% 0.95/0.99  --inst_solver_per_active                1400
% 0.95/0.99  --inst_solver_calls_frac                1.
% 0.95/0.99  --inst_passive_queue_type               priority_queues
% 0.95/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.95/0.99  --inst_passive_queues_freq              [25;2]
% 0.95/0.99  --inst_dismatching                      true
% 0.95/0.99  --inst_eager_unprocessed_to_passive     true
% 0.95/0.99  --inst_prop_sim_given                   true
% 0.95/0.99  --inst_prop_sim_new                     false
% 0.95/0.99  --inst_subs_new                         false
% 0.95/0.99  --inst_eq_res_simp                      false
% 0.95/0.99  --inst_subs_given                       false
% 0.95/0.99  --inst_orphan_elimination               true
% 0.95/0.99  --inst_learning_loop_flag               true
% 0.95/0.99  --inst_learning_start                   3000
% 0.95/0.99  --inst_learning_factor                  2
% 0.95/0.99  --inst_start_prop_sim_after_learn       3
% 0.95/0.99  --inst_sel_renew                        solver
% 0.95/0.99  --inst_lit_activity_flag                true
% 0.95/0.99  --inst_restr_to_given                   false
% 0.95/0.99  --inst_activity_threshold               500
% 0.95/0.99  --inst_out_proof                        true
% 0.95/0.99  
% 0.95/0.99  ------ Resolution Options
% 0.95/0.99  
% 0.95/0.99  --resolution_flag                       false
% 0.95/0.99  --res_lit_sel                           adaptive
% 0.95/0.99  --res_lit_sel_side                      none
% 0.95/0.99  --res_ordering                          kbo
% 0.95/0.99  --res_to_prop_solver                    active
% 0.95/0.99  --res_prop_simpl_new                    false
% 0.95/0.99  --res_prop_simpl_given                  true
% 0.95/0.99  --res_passive_queue_type                priority_queues
% 0.95/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.95/0.99  --res_passive_queues_freq               [15;5]
% 0.95/0.99  --res_forward_subs                      full
% 0.95/0.99  --res_backward_subs                     full
% 0.95/0.99  --res_forward_subs_resolution           true
% 0.95/0.99  --res_backward_subs_resolution          true
% 0.95/0.99  --res_orphan_elimination                true
% 0.95/0.99  --res_time_limit                        2.
% 0.95/0.99  --res_out_proof                         true
% 0.95/0.99  
% 0.95/0.99  ------ Superposition Options
% 0.95/0.99  
% 0.95/0.99  --superposition_flag                    true
% 0.95/0.99  --sup_passive_queue_type                priority_queues
% 0.95/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.95/0.99  --sup_passive_queues_freq               [8;1;4]
% 0.95/0.99  --demod_completeness_check              fast
% 0.95/0.99  --demod_use_ground                      true
% 0.95/0.99  --sup_to_prop_solver                    passive
% 0.95/0.99  --sup_prop_simpl_new                    true
% 0.95/0.99  --sup_prop_simpl_given                  true
% 0.95/0.99  --sup_fun_splitting                     false
% 0.95/0.99  --sup_smt_interval                      50000
% 0.95/0.99  
% 0.95/0.99  ------ Superposition Simplification Setup
% 0.95/0.99  
% 0.95/0.99  --sup_indices_passive                   []
% 0.95/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.95/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.95/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.95/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 0.95/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.95/0.99  --sup_full_bw                           [BwDemod]
% 0.95/0.99  --sup_immed_triv                        [TrivRules]
% 0.95/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.95/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.95/0.99  --sup_immed_bw_main                     []
% 0.95/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.95/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 0.95/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.95/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.95/0.99  
% 0.95/0.99  ------ Combination Options
% 0.95/0.99  
% 0.95/0.99  --comb_res_mult                         3
% 0.95/0.99  --comb_sup_mult                         2
% 0.95/0.99  --comb_inst_mult                        10
% 0.95/0.99  
% 0.95/0.99  ------ Debug Options
% 0.95/0.99  
% 0.95/0.99  --dbg_backtrace                         false
% 0.95/0.99  --dbg_dump_prop_clauses                 false
% 0.95/0.99  --dbg_dump_prop_clauses_file            -
% 0.95/0.99  --dbg_out_stat                          false
% 0.95/0.99  
% 0.95/0.99  
% 0.95/0.99  
% 0.95/0.99  
% 0.95/0.99  ------ Proving...
% 0.95/0.99  
% 0.95/0.99  
% 0.95/0.99  % SZS status Theorem for theBenchmark.p
% 0.95/0.99  
% 0.95/0.99   Resolution empty clause
% 0.95/0.99  
% 0.95/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 0.95/0.99  
% 0.95/0.99  fof(f5,axiom,(
% 0.95/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.95/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.95/0.99  
% 0.95/0.99  fof(f19,plain,(
% 0.95/0.99    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.95/0.99    inference(ennf_transformation,[],[f5])).
% 0.95/0.99  
% 0.95/0.99  fof(f32,plain,(
% 0.95/0.99    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.95/0.99    inference(nnf_transformation,[],[f19])).
% 0.95/0.99  
% 0.95/0.99  fof(f50,plain,(
% 0.95/0.99    ( ! [X0,X1] : (v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.95/0.99    inference(cnf_transformation,[],[f32])).
% 0.95/0.99  
% 0.95/0.99  fof(f6,axiom,(
% 0.95/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.95/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.95/0.99  
% 0.95/0.99  fof(f20,plain,(
% 0.95/0.99    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.95/0.99    inference(ennf_transformation,[],[f6])).
% 0.95/0.99  
% 0.95/0.99  fof(f33,plain,(
% 0.95/0.99    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.95/0.99    inference(nnf_transformation,[],[f20])).
% 0.95/0.99  
% 0.95/0.99  fof(f51,plain,(
% 0.95/0.99    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.95/0.99    inference(cnf_transformation,[],[f33])).
% 0.95/0.99  
% 0.95/0.99  fof(f66,plain,(
% 0.95/0.99    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 0.95/0.99    inference(equality_resolution,[],[f51])).
% 0.95/0.99  
% 0.95/0.99  fof(f11,conjecture,(
% 0.95/0.99    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.95/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.95/0.99  
% 0.95/0.99  fof(f12,negated_conjecture,(
% 0.95/0.99    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.95/0.99    inference(negated_conjecture,[],[f11])).
% 0.95/0.99  
% 0.95/0.99  fof(f29,plain,(
% 0.95/0.99    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.95/0.99    inference(ennf_transformation,[],[f12])).
% 0.95/0.99  
% 0.95/0.99  fof(f30,plain,(
% 0.95/0.99    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.95/0.99    inference(flattening,[],[f29])).
% 0.95/0.99  
% 0.95/0.99  fof(f38,plain,(
% 0.95/0.99    ? [X0] : (? [X1] : (((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.95/0.99    inference(nnf_transformation,[],[f30])).
% 0.95/0.99  
% 0.95/0.99  fof(f39,plain,(
% 0.95/0.99    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.95/0.99    inference(flattening,[],[f38])).
% 0.95/0.99  
% 0.95/0.99  fof(f41,plain,(
% 0.95/0.99    ( ! [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_subset_1(sK2,u1_struct_0(X0)) | ~v3_tex_2(sK2,X0)) & (~v1_subset_1(sK2,u1_struct_0(X0)) | v3_tex_2(sK2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 0.95/0.99    introduced(choice_axiom,[])).
% 0.95/0.99  
% 0.95/0.99  fof(f40,plain,(
% 0.95/0.99    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((v1_subset_1(X1,u1_struct_0(sK1)) | ~v3_tex_2(X1,sK1)) & (~v1_subset_1(X1,u1_struct_0(sK1)) | v3_tex_2(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v1_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.95/0.99    introduced(choice_axiom,[])).
% 0.95/0.99  
% 0.95/0.99  fof(f42,plain,(
% 0.95/0.99    ((v1_subset_1(sK2,u1_struct_0(sK1)) | ~v3_tex_2(sK2,sK1)) & (~v1_subset_1(sK2,u1_struct_0(sK1)) | v3_tex_2(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v1_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 0.95/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f39,f41,f40])).
% 0.95/0.99  
% 0.95/0.99  fof(f65,plain,(
% 0.95/0.99    v1_subset_1(sK2,u1_struct_0(sK1)) | ~v3_tex_2(sK2,sK1)),
% 0.95/0.99    inference(cnf_transformation,[],[f42])).
% 0.95/0.99  
% 0.95/0.99  fof(f8,axiom,(
% 0.95/0.99    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.95/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.95/0.99  
% 0.95/0.99  fof(f23,plain,(
% 0.95/0.99    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.95/0.99    inference(ennf_transformation,[],[f8])).
% 0.95/0.99  
% 0.95/0.99  fof(f24,plain,(
% 0.95/0.99    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.95/0.99    inference(flattening,[],[f23])).
% 0.95/0.99  
% 0.95/0.99  fof(f56,plain,(
% 0.95/0.99    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.95/0.99    inference(cnf_transformation,[],[f24])).
% 0.95/0.99  
% 0.95/0.99  fof(f10,axiom,(
% 0.95/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 0.95/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.95/0.99  
% 0.95/0.99  fof(f27,plain,(
% 0.95/0.99    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) | (~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.95/0.99    inference(ennf_transformation,[],[f10])).
% 0.95/0.99  
% 0.95/0.99  fof(f28,plain,(
% 0.95/0.99    ! [X0] : (! [X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.95/0.99    inference(flattening,[],[f27])).
% 0.95/0.99  
% 0.95/0.99  fof(f58,plain,(
% 0.95/0.99    ( ! [X0,X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.95/0.99    inference(cnf_transformation,[],[f28])).
% 0.95/0.99  
% 0.95/0.99  fof(f4,axiom,(
% 0.95/0.99    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 0.95/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.95/0.99  
% 0.95/0.99  fof(f17,plain,(
% 0.95/0.99    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 0.95/0.99    inference(ennf_transformation,[],[f4])).
% 0.95/0.99  
% 0.95/0.99  fof(f18,plain,(
% 0.95/0.99    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 0.95/0.99    inference(flattening,[],[f17])).
% 0.95/0.99  
% 0.95/0.99  fof(f48,plain,(
% 0.95/0.99    ( ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 0.95/0.99    inference(cnf_transformation,[],[f18])).
% 0.95/0.99  
% 0.95/0.99  fof(f59,plain,(
% 0.95/0.99    ~v2_struct_0(sK1)),
% 0.95/0.99    inference(cnf_transformation,[],[f42])).
% 0.95/0.99  
% 0.95/0.99  fof(f61,plain,(
% 0.95/0.99    v1_tdlat_3(sK1)),
% 0.95/0.99    inference(cnf_transformation,[],[f42])).
% 0.95/0.99  
% 0.95/0.99  fof(f62,plain,(
% 0.95/0.99    l1_pre_topc(sK1)),
% 0.95/0.99    inference(cnf_transformation,[],[f42])).
% 0.95/0.99  
% 0.95/0.99  fof(f63,plain,(
% 0.95/0.99    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.95/0.99    inference(cnf_transformation,[],[f42])).
% 0.95/0.99  
% 0.95/0.99  fof(f7,axiom,(
% 0.95/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 0.95/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.95/0.99  
% 0.95/0.99  fof(f21,plain,(
% 0.95/0.99    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.95/0.99    inference(ennf_transformation,[],[f7])).
% 0.95/0.99  
% 0.95/0.99  fof(f22,plain,(
% 0.95/0.99    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.95/0.99    inference(flattening,[],[f21])).
% 0.95/0.99  
% 0.95/0.99  fof(f34,plain,(
% 0.95/0.99    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.95/0.99    inference(nnf_transformation,[],[f22])).
% 0.95/0.99  
% 0.95/0.99  fof(f35,plain,(
% 0.95/0.99    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.95/0.99    inference(rectify,[],[f34])).
% 0.95/0.99  
% 0.95/0.99  fof(f36,plain,(
% 0.95/0.99    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK0(X0),X0) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.95/0.99    introduced(choice_axiom,[])).
% 0.95/0.99  
% 0.95/0.99  fof(f37,plain,(
% 0.95/0.99    ! [X0] : (((v1_tdlat_3(X0) | (~v3_pre_topc(sK0(X0),X0) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.95/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).
% 0.95/0.99  
% 0.95/0.99  fof(f53,plain,(
% 0.95/0.99    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.95/0.99    inference(cnf_transformation,[],[f37])).
% 0.95/0.99  
% 0.95/0.99  fof(f60,plain,(
% 0.95/0.99    v2_pre_topc(sK1)),
% 0.95/0.99    inference(cnf_transformation,[],[f42])).
% 0.95/0.99  
% 0.95/0.99  fof(f3,axiom,(
% 0.95/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.95/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.95/0.99  
% 0.95/0.99  fof(f16,plain,(
% 0.95/0.99    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.95/0.99    inference(ennf_transformation,[],[f3])).
% 0.95/0.99  
% 0.95/0.99  fof(f31,plain,(
% 0.95/0.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.95/0.99    inference(nnf_transformation,[],[f16])).
% 0.95/0.99  
% 0.95/0.99  fof(f47,plain,(
% 0.95/0.99    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.95/0.99    inference(cnf_transformation,[],[f31])).
% 0.95/0.99  
% 0.95/0.99  fof(f1,axiom,(
% 0.95/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.95/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.95/0.99  
% 0.95/0.99  fof(f13,plain,(
% 0.95/0.99    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.95/0.99    inference(ennf_transformation,[],[f1])).
% 0.95/0.99  
% 0.95/0.99  fof(f43,plain,(
% 0.95/0.99    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.95/0.99    inference(cnf_transformation,[],[f13])).
% 0.95/0.99  
% 0.95/0.99  fof(f2,axiom,(
% 0.95/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.95/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.95/0.99  
% 0.95/0.99  fof(f14,plain,(
% 0.95/0.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.95/0.99    inference(ennf_transformation,[],[f2])).
% 0.95/0.99  
% 0.95/0.99  fof(f15,plain,(
% 0.95/0.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.95/0.99    inference(flattening,[],[f14])).
% 0.95/0.99  
% 0.95/0.99  fof(f44,plain,(
% 0.95/0.99    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.95/0.99    inference(cnf_transformation,[],[f15])).
% 0.95/0.99  
% 0.95/0.99  fof(f49,plain,(
% 0.95/0.99    ( ! [X0,X1] : (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.95/0.99    inference(cnf_transformation,[],[f32])).
% 0.95/0.99  
% 0.95/0.99  fof(f52,plain,(
% 0.95/0.99    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.95/0.99    inference(cnf_transformation,[],[f33])).
% 0.95/0.99  
% 0.95/0.99  fof(f64,plain,(
% 0.95/0.99    ~v1_subset_1(sK2,u1_struct_0(sK1)) | v3_tex_2(sK2,sK1)),
% 0.95/0.99    inference(cnf_transformation,[],[f42])).
% 0.95/0.99  
% 0.95/0.99  fof(f9,axiom,(
% 0.95/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 0.95/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.95/0.99  
% 0.95/0.99  fof(f25,plain,(
% 0.95/0.99    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.95/0.99    inference(ennf_transformation,[],[f9])).
% 0.95/0.99  
% 0.95/0.99  fof(f26,plain,(
% 0.95/0.99    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.95/0.99    inference(flattening,[],[f25])).
% 0.95/0.99  
% 0.95/0.99  fof(f57,plain,(
% 0.95/0.99    ( ! [X0,X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.95/0.99    inference(cnf_transformation,[],[f26])).
% 0.95/0.99  
% 0.95/0.99  cnf(c_6,plain,
% 0.95/0.99      ( v1_tops_1(X0,X1)
% 0.95/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.95/0.99      | ~ l1_pre_topc(X1)
% 0.95/0.99      | k2_pre_topc(X1,X0) != u1_struct_0(X1) ),
% 0.95/0.99      inference(cnf_transformation,[],[f50]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_9,plain,
% 0.95/0.99      ( ~ v1_subset_1(X0,X0) | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
% 0.95/0.99      inference(cnf_transformation,[],[f66]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_16,negated_conjecture,
% 0.95/0.99      ( ~ v3_tex_2(sK2,sK1) | v1_subset_1(sK2,u1_struct_0(sK1)) ),
% 0.95/0.99      inference(cnf_transformation,[],[f65]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_170,plain,
% 0.95/0.99      ( ~ v3_tex_2(sK2,sK1) | v1_subset_1(sK2,u1_struct_0(sK1)) ),
% 0.95/0.99      inference(prop_impl,[status(thm)],[c_16]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_320,plain,
% 0.95/0.99      ( ~ v3_tex_2(sK2,sK1)
% 0.95/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X0))
% 0.95/0.99      | u1_struct_0(sK1) != X0
% 0.95/0.99      | sK2 != X0 ),
% 0.95/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_170]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_321,plain,
% 0.95/0.99      ( ~ v3_tex_2(sK2,sK1)
% 0.95/0.99      | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.95/0.99      | sK2 != u1_struct_0(sK1) ),
% 0.95/0.99      inference(unflattening,[status(thm)],[c_320]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_13,plain,
% 0.95/0.99      ( v2_tex_2(X0,X1)
% 0.95/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.95/0.99      | v2_struct_0(X1)
% 0.95/0.99      | ~ v1_tdlat_3(X1)
% 0.95/0.99      | ~ l1_pre_topc(X1)
% 0.95/0.99      | ~ v2_pre_topc(X1) ),
% 0.95/0.99      inference(cnf_transformation,[],[f56]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_15,plain,
% 0.95/0.99      ( v3_tex_2(X0,X1)
% 0.95/0.99      | ~ v2_tex_2(X0,X1)
% 0.95/0.99      | ~ v1_tops_1(X0,X1)
% 0.95/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.95/0.99      | v2_struct_0(X1)
% 0.95/0.99      | ~ l1_pre_topc(X1)
% 0.95/0.99      | ~ v2_pre_topc(X1) ),
% 0.95/0.99      inference(cnf_transformation,[],[f58]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_340,plain,
% 0.95/0.99      ( v3_tex_2(X0,X1)
% 0.95/0.99      | ~ v1_tops_1(X0,X1)
% 0.95/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.95/0.99      | v2_struct_0(X1)
% 0.95/0.99      | ~ v1_tdlat_3(X1)
% 0.95/0.99      | ~ l1_pre_topc(X1)
% 0.95/0.99      | ~ v2_pre_topc(X1) ),
% 0.95/0.99      inference(resolution,[status(thm)],[c_13,c_15]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_5,plain,
% 0.95/0.99      ( ~ v1_tdlat_3(X0) | ~ l1_pre_topc(X0) | v2_pre_topc(X0) ),
% 0.95/0.99      inference(cnf_transformation,[],[f48]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_358,plain,
% 0.95/0.99      ( v3_tex_2(X0,X1)
% 0.95/0.99      | ~ v1_tops_1(X0,X1)
% 0.95/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.95/0.99      | v2_struct_0(X1)
% 0.95/0.99      | ~ v1_tdlat_3(X1)
% 0.95/0.99      | ~ l1_pre_topc(X1) ),
% 0.95/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_340,c_5]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_22,negated_conjecture,
% 0.95/0.99      ( ~ v2_struct_0(sK1) ),
% 0.95/0.99      inference(cnf_transformation,[],[f59]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_375,plain,
% 0.95/0.99      ( v3_tex_2(X0,X1)
% 0.95/0.99      | ~ v1_tops_1(X0,X1)
% 0.95/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.95/0.99      | ~ v1_tdlat_3(X1)
% 0.95/0.99      | ~ l1_pre_topc(X1)
% 0.95/0.99      | sK1 != X1 ),
% 0.95/0.99      inference(resolution_lifted,[status(thm)],[c_358,c_22]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_376,plain,
% 0.95/0.99      ( v3_tex_2(X0,sK1)
% 0.95/0.99      | ~ v1_tops_1(X0,sK1)
% 0.95/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.95/0.99      | ~ v1_tdlat_3(sK1)
% 0.95/0.99      | ~ l1_pre_topc(sK1) ),
% 0.95/0.99      inference(unflattening,[status(thm)],[c_375]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_20,negated_conjecture,
% 0.95/0.99      ( v1_tdlat_3(sK1) ),
% 0.95/0.99      inference(cnf_transformation,[],[f61]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_19,negated_conjecture,
% 0.95/0.99      ( l1_pre_topc(sK1) ),
% 0.95/0.99      inference(cnf_transformation,[],[f62]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_380,plain,
% 0.95/0.99      ( v3_tex_2(X0,sK1)
% 0.95/0.99      | ~ v1_tops_1(X0,sK1)
% 0.95/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 0.95/0.99      inference(global_propositional_subsumption,
% 0.95/0.99                [status(thm)],
% 0.95/0.99                [c_376,c_20,c_19]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_448,plain,
% 0.95/0.99      ( ~ v1_tops_1(X0,sK1)
% 0.95/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.95/0.99      | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.95/0.99      | u1_struct_0(sK1) != sK2
% 0.95/0.99      | sK1 != sK1
% 0.95/0.99      | sK2 != X0 ),
% 0.95/0.99      inference(resolution_lifted,[status(thm)],[c_321,c_380]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_449,plain,
% 0.95/0.99      ( ~ v1_tops_1(sK2,sK1)
% 0.95/0.99      | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.95/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.95/1.00      | u1_struct_0(sK1) != sK2 ),
% 0.95/1.00      inference(unflattening,[status(thm)],[c_448]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_18,negated_conjecture,
% 0.95/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 0.95/1.00      inference(cnf_transformation,[],[f63]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_451,plain,
% 0.95/1.00      ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.95/1.00      | ~ v1_tops_1(sK2,sK1)
% 0.95/1.00      | u1_struct_0(sK1) != sK2 ),
% 0.95/1.00      inference(global_propositional_subsumption,[status(thm)],[c_449,c_18]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_452,plain,
% 0.95/1.00      ( ~ v1_tops_1(sK2,sK1)
% 0.95/1.00      | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.95/1.00      | u1_struct_0(sK1) != sK2 ),
% 0.95/1.00      inference(renaming,[status(thm)],[c_451]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_475,plain,
% 0.95/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.95/1.00      | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.95/1.00      | ~ l1_pre_topc(X1)
% 0.95/1.00      | k2_pre_topc(X1,X0) != u1_struct_0(X1)
% 0.95/1.00      | u1_struct_0(sK1) != sK2
% 0.95/1.00      | sK1 != X1
% 0.95/1.00      | sK2 != X0 ),
% 0.95/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_452]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_476,plain,
% 0.95/1.00      ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.95/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.95/1.00      | ~ l1_pre_topc(sK1)
% 0.95/1.00      | k2_pre_topc(sK1,sK2) != u1_struct_0(sK1)
% 0.95/1.00      | u1_struct_0(sK1) != sK2 ),
% 0.95/1.00      inference(unflattening,[status(thm)],[c_475]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_478,plain,
% 0.95/1.00      ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.95/1.00      | k2_pre_topc(sK1,sK2) != u1_struct_0(sK1)
% 0.95/1.00      | u1_struct_0(sK1) != sK2 ),
% 0.95/1.00      inference(global_propositional_subsumption,
% 0.95/1.00                [status(thm)],
% 0.95/1.00                [c_476,c_19,c_18]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_703,plain,
% 0.95/1.00      ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.95/1.00      | k2_pre_topc(sK1,sK2) != u1_struct_0(sK1)
% 0.95/1.00      | u1_struct_0(sK1) != sK2 ),
% 0.95/1.00      inference(subtyping,[status(esa)],[c_478]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_798,plain,
% 0.95/1.00      ( k2_pre_topc(sK1,sK2) != u1_struct_0(sK1)
% 0.95/1.00      | u1_struct_0(sK1) != sK2
% 0.95/1.00      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 0.95/1.00      inference(predicate_to_equality,[status(thm)],[c_703]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_723,plain,
% 0.95/1.00      ( k2_pre_topc(sK1,sK2) != u1_struct_0(sK1)
% 0.95/1.00      | u1_struct_0(sK1) != sK2
% 0.95/1.00      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 0.95/1.00      inference(predicate_to_equality,[status(thm)],[c_703]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_704,negated_conjecture,
% 0.95/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 0.95/1.00      inference(subtyping,[status(esa)],[c_18]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_797,plain,
% 0.95/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 0.95/1.00      inference(predicate_to_equality,[status(thm)],[c_704]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_12,plain,
% 0.95/1.00      ( v3_pre_topc(X0,X1)
% 0.95/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.95/1.00      | ~ v1_tdlat_3(X1)
% 0.95/1.00      | ~ l1_pre_topc(X1)
% 0.95/1.00      | ~ v2_pre_topc(X1) ),
% 0.95/1.00      inference(cnf_transformation,[],[f53]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_553,plain,
% 0.95/1.00      ( v3_pre_topc(X0,X1)
% 0.95/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.95/1.00      | ~ v1_tdlat_3(X1)
% 0.95/1.00      | ~ v2_pre_topc(X1)
% 0.95/1.00      | sK1 != X1 ),
% 0.95/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_19]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_554,plain,
% 0.95/1.00      ( v3_pre_topc(X0,sK1)
% 0.95/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.95/1.00      | ~ v1_tdlat_3(sK1)
% 0.95/1.00      | ~ v2_pre_topc(sK1) ),
% 0.95/1.00      inference(unflattening,[status(thm)],[c_553]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_21,negated_conjecture,
% 0.95/1.00      ( v2_pre_topc(sK1) ),
% 0.95/1.00      inference(cnf_transformation,[],[f60]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_558,plain,
% 0.95/1.00      ( v3_pre_topc(X0,sK1) | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 0.95/1.00      inference(global_propositional_subsumption,
% 0.95/1.00                [status(thm)],
% 0.95/1.00                [c_554,c_21,c_20]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_3,plain,
% 0.95/1.00      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 0.95/1.00      | v4_pre_topc(X1,X0)
% 0.95/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 0.95/1.00      | ~ l1_pre_topc(X0) ),
% 0.95/1.00      inference(cnf_transformation,[],[f47]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_538,plain,
% 0.95/1.00      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 0.95/1.00      | v4_pre_topc(X1,X0)
% 0.95/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 0.95/1.00      | sK1 != X0 ),
% 0.95/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_19]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_539,plain,
% 0.95/1.00      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),X0),sK1)
% 0.95/1.00      | v4_pre_topc(X0,sK1)
% 0.95/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 0.95/1.00      inference(unflattening,[status(thm)],[c_538]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_638,plain,
% 0.95/1.00      ( v4_pre_topc(X0,sK1)
% 0.95/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.95/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.95/1.00      | k3_subset_1(u1_struct_0(sK1),X0) != X1
% 0.95/1.00      | sK1 != sK1 ),
% 0.95/1.00      inference(resolution_lifted,[status(thm)],[c_558,c_539]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_639,plain,
% 0.95/1.00      ( v4_pre_topc(X0,sK1)
% 0.95/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.95/1.00      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 0.95/1.00      inference(unflattening,[status(thm)],[c_638]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_0,plain,
% 0.95/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.95/1.00      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 0.95/1.00      inference(cnf_transformation,[],[f43]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_649,plain,
% 0.95/1.00      ( v4_pre_topc(X0,sK1) | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 0.95/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_639,c_0]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_2,plain,
% 0.95/1.00      ( ~ v4_pre_topc(X0,X1)
% 0.95/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.95/1.00      | ~ l1_pre_topc(X1)
% 0.95/1.00      | k2_pre_topc(X1,X0) = X0 ),
% 0.95/1.00      inference(cnf_transformation,[],[f44]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_571,plain,
% 0.95/1.00      ( ~ v4_pre_topc(X0,X1)
% 0.95/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.95/1.00      | k2_pre_topc(X1,X0) = X0
% 0.95/1.00      | sK1 != X1 ),
% 0.95/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_19]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_572,plain,
% 0.95/1.00      ( ~ v4_pre_topc(X0,sK1)
% 0.95/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.95/1.00      | k2_pre_topc(sK1,X0) = X0 ),
% 0.95/1.00      inference(unflattening,[status(thm)],[c_571]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_663,plain,
% 0.95/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.95/1.00      | k2_pre_topc(sK1,X0) = X0 ),
% 0.95/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_649,c_572]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_701,plain,
% 0.95/1.00      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.95/1.00      | k2_pre_topc(sK1,X0_46) = X0_46 ),
% 0.95/1.00      inference(subtyping,[status(esa)],[c_663]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_799,plain,
% 0.95/1.00      ( k2_pre_topc(sK1,X0_46) = X0_46
% 0.95/1.00      | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 0.95/1.00      inference(predicate_to_equality,[status(thm)],[c_701]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_892,plain,
% 0.95/1.00      ( k2_pre_topc(sK1,sK2) = sK2 ),
% 0.95/1.00      inference(superposition,[status(thm)],[c_797,c_799]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_7,plain,
% 0.95/1.00      ( ~ v1_tops_1(X0,X1)
% 0.95/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.95/1.00      | ~ l1_pre_topc(X1)
% 0.95/1.00      | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
% 0.95/1.00      inference(cnf_transformation,[],[f49]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_8,plain,
% 0.95/1.00      ( v1_subset_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | X0 = X1 ),
% 0.95/1.00      inference(cnf_transformation,[],[f52]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_17,negated_conjecture,
% 0.95/1.00      ( v3_tex_2(sK2,sK1) | ~ v1_subset_1(sK2,u1_struct_0(sK1)) ),
% 0.95/1.00      inference(cnf_transformation,[],[f64]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_168,plain,
% 0.95/1.00      ( v3_tex_2(sK2,sK1) | ~ v1_subset_1(sK2,u1_struct_0(sK1)) ),
% 0.95/1.00      inference(prop_impl,[status(thm)],[c_17]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_306,plain,
% 0.95/1.00      ( v3_tex_2(sK2,sK1)
% 0.95/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.95/1.00      | X1 = X0
% 0.95/1.00      | u1_struct_0(sK1) != X1
% 0.95/1.00      | sK2 != X0 ),
% 0.95/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_168]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_307,plain,
% 0.95/1.00      ( v3_tex_2(sK2,sK1)
% 0.95/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.95/1.00      | u1_struct_0(sK1) = sK2 ),
% 0.95/1.00      inference(unflattening,[status(thm)],[c_306]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_309,plain,
% 0.95/1.00      ( v3_tex_2(sK2,sK1) | u1_struct_0(sK1) = sK2 ),
% 0.95/1.00      inference(global_propositional_subsumption,[status(thm)],[c_307,c_18]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_14,plain,
% 0.95/1.00      ( ~ v3_tex_2(X0,X1)
% 0.95/1.00      | v1_tops_1(X0,X1)
% 0.95/1.00      | ~ v3_pre_topc(X0,X1)
% 0.95/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.95/1.00      | v2_struct_0(X1)
% 0.95/1.00      | ~ l1_pre_topc(X1)
% 0.95/1.00      | ~ v2_pre_topc(X1) ),
% 0.95/1.00      inference(cnf_transformation,[],[f57]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_396,plain,
% 0.95/1.00      ( ~ v3_tex_2(X0,X1)
% 0.95/1.00      | v1_tops_1(X0,X1)
% 0.95/1.00      | ~ v3_pre_topc(X0,X1)
% 0.95/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.95/1.00      | ~ l1_pre_topc(X1)
% 0.95/1.00      | ~ v2_pre_topc(X1)
% 0.95/1.00      | sK1 != X1 ),
% 0.95/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_397,plain,
% 0.95/1.00      ( ~ v3_tex_2(X0,sK1)
% 0.95/1.00      | v1_tops_1(X0,sK1)
% 0.95/1.00      | ~ v3_pre_topc(X0,sK1)
% 0.95/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.95/1.00      | ~ l1_pre_topc(sK1)
% 0.95/1.00      | ~ v2_pre_topc(sK1) ),
% 0.95/1.00      inference(unflattening,[status(thm)],[c_396]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_401,plain,
% 0.95/1.00      ( ~ v3_tex_2(X0,sK1)
% 0.95/1.00      | v1_tops_1(X0,sK1)
% 0.95/1.00      | ~ v3_pre_topc(X0,sK1)
% 0.95/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 0.95/1.00      inference(global_propositional_subsumption,
% 0.95/1.00                [status(thm)],
% 0.95/1.00                [c_397,c_21,c_19]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_431,plain,
% 0.95/1.00      ( v1_tops_1(X0,sK1)
% 0.95/1.00      | ~ v3_pre_topc(X0,sK1)
% 0.95/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.95/1.00      | u1_struct_0(sK1) = sK2
% 0.95/1.00      | sK1 != sK1
% 0.95/1.00      | sK2 != X0 ),
% 0.95/1.00      inference(resolution_lifted,[status(thm)],[c_309,c_401]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_432,plain,
% 0.95/1.00      ( v1_tops_1(sK2,sK1)
% 0.95/1.00      | ~ v3_pre_topc(sK2,sK1)
% 0.95/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.95/1.00      | u1_struct_0(sK1) = sK2 ),
% 0.95/1.00      inference(unflattening,[status(thm)],[c_431]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_434,plain,
% 0.95/1.00      ( ~ v3_pre_topc(sK2,sK1) | v1_tops_1(sK2,sK1) | u1_struct_0(sK1) = sK2 ),
% 0.95/1.00      inference(global_propositional_subsumption,[status(thm)],[c_432,c_18]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_435,plain,
% 0.95/1.00      ( v1_tops_1(sK2,sK1) | ~ v3_pre_topc(sK2,sK1) | u1_struct_0(sK1) = sK2 ),
% 0.95/1.00      inference(renaming,[status(thm)],[c_434]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_492,plain,
% 0.95/1.00      ( ~ v3_pre_topc(sK2,sK1)
% 0.95/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.95/1.00      | ~ l1_pre_topc(X1)
% 0.95/1.00      | k2_pre_topc(X1,X0) = u1_struct_0(X1)
% 0.95/1.00      | u1_struct_0(sK1) = sK2
% 0.95/1.00      | sK1 != X1
% 0.95/1.00      | sK2 != X0 ),
% 0.95/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_435]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_493,plain,
% 0.95/1.00      ( ~ v3_pre_topc(sK2,sK1)
% 0.95/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.95/1.00      | ~ l1_pre_topc(sK1)
% 0.95/1.00      | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1)
% 0.95/1.00      | u1_struct_0(sK1) = sK2 ),
% 0.95/1.00      inference(unflattening,[status(thm)],[c_492]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_495,plain,
% 0.95/1.00      ( ~ v3_pre_topc(sK2,sK1)
% 0.95/1.00      | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1)
% 0.95/1.00      | u1_struct_0(sK1) = sK2 ),
% 0.95/1.00      inference(global_propositional_subsumption,
% 0.95/1.00                [status(thm)],
% 0.95/1.00                [c_493,c_19,c_18]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_627,plain,
% 0.95/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.95/1.00      | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1)
% 0.95/1.00      | u1_struct_0(sK1) = sK2
% 0.95/1.00      | sK1 != sK1
% 0.95/1.00      | sK2 != X0 ),
% 0.95/1.00      inference(resolution_lifted,[status(thm)],[c_558,c_495]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_628,plain,
% 0.95/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.95/1.00      | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1)
% 0.95/1.00      | u1_struct_0(sK1) = sK2 ),
% 0.95/1.00      inference(unflattening,[status(thm)],[c_627]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_630,plain,
% 0.95/1.00      ( k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) | u1_struct_0(sK1) = sK2 ),
% 0.95/1.00      inference(global_propositional_subsumption,[status(thm)],[c_628,c_18]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_702,plain,
% 0.95/1.00      ( k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) | u1_struct_0(sK1) = sK2 ),
% 0.95/1.00      inference(subtyping,[status(esa)],[c_630]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_894,plain,
% 0.95/1.00      ( u1_struct_0(sK1) = sK2 ),
% 0.95/1.00      inference(demodulation,[status(thm)],[c_892,c_702]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_1015,plain,
% 0.95/1.00      ( k2_pre_topc(sK1,sK2) != u1_struct_0(sK1)
% 0.95/1.00      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 0.95/1.00      inference(global_propositional_subsumption,
% 0.95/1.00                [status(thm)],
% 0.95/1.00                [c_798,c_723,c_894]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_1019,plain,
% 0.95/1.00      ( sK2 != sK2 | m1_subset_1(sK2,k1_zfmisc_1(sK2)) != iProver_top ),
% 0.95/1.00      inference(light_normalisation,[status(thm)],[c_1015,c_892,c_894]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_1020,plain,
% 0.95/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(sK2)) != iProver_top ),
% 0.95/1.00      inference(equality_resolution_simp,[status(thm)],[c_1019]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_926,plain,
% 0.95/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(sK2)) = iProver_top ),
% 0.95/1.00      inference(demodulation,[status(thm)],[c_894,c_797]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_1022,plain,
% 0.95/1.00      ( $false ),
% 0.95/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_1020,c_926]) ).
% 0.95/1.00  
% 0.95/1.00  
% 0.95/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 0.95/1.00  
% 0.95/1.00  ------                               Statistics
% 0.95/1.00  
% 0.95/1.00  ------ General
% 0.95/1.00  
% 0.95/1.00  abstr_ref_over_cycles:                  0
% 0.95/1.00  abstr_ref_under_cycles:                 0
% 0.95/1.00  gc_basic_clause_elim:                   0
% 0.95/1.00  forced_gc_time:                         0
% 0.95/1.00  parsing_time:                           0.029
% 0.95/1.00  unif_index_cands_time:                  0.
% 0.95/1.00  unif_index_add_time:                    0.
% 0.95/1.00  orderings_time:                         0.
% 0.95/1.00  out_proof_time:                         0.011
% 0.95/1.00  total_time:                             0.082
% 0.95/1.00  num_of_symbols:                         52
% 0.95/1.00  num_of_terms:                           681
% 0.95/1.00  
% 0.95/1.00  ------ Preprocessing
% 0.95/1.00  
% 0.95/1.00  num_of_splits:                          0
% 0.95/1.00  num_of_split_atoms:                     0
% 0.95/1.00  num_of_reused_defs:                     0
% 0.95/1.00  num_eq_ax_congr_red:                    17
% 0.95/1.00  num_of_sem_filtered_clauses:            1
% 0.95/1.00  num_of_subtypes:                        3
% 0.95/1.00  monotx_restored_types:                  0
% 0.95/1.00  sat_num_of_epr_types:                   0
% 0.95/1.00  sat_num_of_non_cyclic_types:            0
% 0.95/1.00  sat_guarded_non_collapsed_types:        1
% 0.95/1.00  num_pure_diseq_elim:                    0
% 0.95/1.00  simp_replaced_by:                       0
% 0.95/1.00  res_preprocessed:                       51
% 0.95/1.00  prep_upred:                             0
% 0.95/1.00  prep_unflattend:                        23
% 0.95/1.00  smt_new_axioms:                         0
% 0.95/1.00  pred_elim_cands:                        1
% 0.95/1.00  pred_elim:                              10
% 0.95/1.00  pred_elim_cl:                           18
% 0.95/1.00  pred_elim_cycles:                       12
% 0.95/1.00  merged_defs:                            2
% 0.95/1.00  merged_defs_ncl:                        0
% 0.95/1.00  bin_hyper_res:                          2
% 0.95/1.00  prep_cycles:                            4
% 0.95/1.00  pred_elim_time:                         0.006
% 0.95/1.00  splitting_time:                         0.
% 0.95/1.00  sem_filter_time:                        0.
% 0.95/1.00  monotx_time:                            0.
% 0.95/1.00  subtype_inf_time:                       0.
% 0.95/1.00  
% 0.95/1.00  ------ Problem properties
% 0.95/1.00  
% 0.95/1.00  clauses:                                5
% 0.95/1.00  conjectures:                            1
% 0.95/1.00  epr:                                    0
% 0.95/1.00  horn:                                   4
% 0.95/1.00  ground:                                 3
% 0.95/1.00  unary:                                  1
% 0.95/1.00  binary:                                 3
% 0.95/1.00  lits:                                   10
% 0.95/1.00  lits_eq:                                5
% 0.95/1.00  fd_pure:                                0
% 0.95/1.00  fd_pseudo:                              0
% 0.95/1.00  fd_cond:                                0
% 0.95/1.00  fd_pseudo_cond:                         0
% 0.95/1.00  ac_symbols:                             0
% 0.95/1.00  
% 0.95/1.00  ------ Propositional Solver
% 0.95/1.00  
% 0.95/1.00  prop_solver_calls:                      24
% 0.95/1.00  prop_fast_solver_calls:                 384
% 0.95/1.00  smt_solver_calls:                       0
% 0.95/1.00  smt_fast_solver_calls:                  0
% 0.95/1.00  prop_num_of_clauses:                    283
% 0.95/1.00  prop_preprocess_simplified:             1363
% 0.95/1.00  prop_fo_subsumed:                       20
% 0.95/1.00  prop_solver_time:                       0.
% 0.95/1.00  smt_solver_time:                        0.
% 0.95/1.00  smt_fast_solver_time:                   0.
% 0.95/1.00  prop_fast_solver_time:                  0.
% 0.95/1.00  prop_unsat_core_time:                   0.
% 0.95/1.00  
% 0.95/1.00  ------ QBF
% 0.95/1.00  
% 0.95/1.00  qbf_q_res:                              0
% 0.95/1.00  qbf_num_tautologies:                    0
% 0.95/1.00  qbf_prep_cycles:                        0
% 0.95/1.00  
% 0.95/1.00  ------ BMC1
% 0.95/1.00  
% 0.95/1.00  bmc1_current_bound:                     -1
% 0.95/1.00  bmc1_last_solved_bound:                 -1
% 0.95/1.00  bmc1_unsat_core_size:                   -1
% 0.95/1.00  bmc1_unsat_core_parents_size:           -1
% 0.95/1.00  bmc1_merge_next_fun:                    0
% 0.95/1.00  bmc1_unsat_core_clauses_time:           0.
% 0.95/1.00  
% 0.95/1.00  ------ Instantiation
% 0.95/1.00  
% 0.95/1.00  inst_num_of_clauses:                    50
% 0.95/1.00  inst_num_in_passive:                    9
% 0.95/1.00  inst_num_in_active:                     36
% 0.95/1.00  inst_num_in_unprocessed:                5
% 0.95/1.00  inst_num_of_loops:                      40
% 0.95/1.00  inst_num_of_learning_restarts:          0
% 0.95/1.00  inst_num_moves_active_passive:          0
% 0.95/1.00  inst_lit_activity:                      0
% 0.95/1.00  inst_lit_activity_moves:                0
% 0.95/1.00  inst_num_tautologies:                   0
% 0.95/1.00  inst_num_prop_implied:                  0
% 0.95/1.00  inst_num_existing_simplified:           0
% 0.95/1.00  inst_num_eq_res_simplified:             0
% 0.95/1.00  inst_num_child_elim:                    0
% 0.95/1.00  inst_num_of_dismatching_blockings:      7
% 0.95/1.00  inst_num_of_non_proper_insts:           45
% 0.95/1.00  inst_num_of_duplicates:                 0
% 0.95/1.00  inst_inst_num_from_inst_to_res:         0
% 0.95/1.00  inst_dismatching_checking_time:         0.
% 0.95/1.00  
% 0.95/1.00  ------ Resolution
% 0.95/1.00  
% 0.95/1.00  res_num_of_clauses:                     0
% 0.95/1.00  res_num_in_passive:                     0
% 0.95/1.00  res_num_in_active:                      0
% 0.95/1.00  res_num_of_loops:                       55
% 0.95/1.00  res_forward_subset_subsumed:            7
% 0.95/1.00  res_backward_subset_subsumed:           1
% 0.95/1.00  res_forward_subsumed:                   1
% 0.95/1.00  res_backward_subsumed:                  0
% 0.95/1.00  res_forward_subsumption_resolution:     2
% 0.95/1.00  res_backward_subsumption_resolution:    1
% 0.95/1.00  res_clause_to_clause_subsumption:       18
% 0.95/1.00  res_orphan_elimination:                 0
% 0.95/1.00  res_tautology_del:                      13
% 0.95/1.00  res_num_eq_res_simplified:              0
% 0.95/1.00  res_num_sel_changes:                    0
% 0.95/1.00  res_moves_from_active_to_pass:          0
% 0.95/1.00  
% 0.95/1.00  ------ Superposition
% 0.95/1.00  
% 0.95/1.00  sup_time_total:                         0.
% 0.95/1.00  sup_time_generating:                    0.
% 0.95/1.00  sup_time_sim_full:                      0.
% 0.95/1.00  sup_time_sim_immed:                     0.
% 0.95/1.00  
% 0.95/1.00  sup_num_of_clauses:                     5
% 0.95/1.00  sup_num_in_active:                      4
% 0.95/1.00  sup_num_in_passive:                     1
% 0.95/1.00  sup_num_of_loops:                       7
% 0.95/1.00  sup_fw_superposition:                   2
% 0.95/1.00  sup_bw_superposition:                   0
% 0.95/1.00  sup_immediate_simplified:               0
% 0.95/1.00  sup_given_eliminated:                   0
% 0.95/1.00  comparisons_done:                       0
% 0.95/1.00  comparisons_avoided:                    0
% 0.95/1.00  
% 0.95/1.00  ------ Simplifications
% 0.95/1.00  
% 0.95/1.00  
% 0.95/1.00  sim_fw_subset_subsumed:                 0
% 0.95/1.00  sim_bw_subset_subsumed:                 0
% 0.95/1.00  sim_fw_subsumed:                        0
% 0.95/1.00  sim_bw_subsumed:                        0
% 0.95/1.00  sim_fw_subsumption_res:                 1
% 0.95/1.00  sim_bw_subsumption_res:                 0
% 0.95/1.00  sim_tautology_del:                      0
% 0.95/1.00  sim_eq_tautology_del:                   0
% 0.95/1.00  sim_eq_res_simp:                        1
% 0.95/1.00  sim_fw_demodulated:                     0
% 0.95/1.00  sim_bw_demodulated:                     3
% 0.95/1.00  sim_light_normalised:                   1
% 0.95/1.00  sim_joinable_taut:                      0
% 0.95/1.00  sim_joinable_simp:                      0
% 0.95/1.00  sim_ac_normalised:                      0
% 0.95/1.00  sim_smt_subsumption:                    0
% 0.95/1.00  
%------------------------------------------------------------------------------
