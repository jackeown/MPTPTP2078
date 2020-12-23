%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:41 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 444 expanded)
%              Number of clauses        :   66 ( 110 expanded)
%              Number of leaves         :   14 ( 118 expanded)
%              Depth                    :   17
%              Number of atoms          :  463 (3110 expanded)
%              Number of equality atoms :   81 ( 113 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f34,plain,(
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

fof(f33,plain,
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

fof(f35,plain,
    ( v1_subset_1(sK2,u1_struct_0(sK1))
    & v3_tex_2(sK2,sK1)
    & ( v4_pre_topc(sK2,sK1)
      | v3_pre_topc(sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v3_tdlat_3(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f25,f34,f33])).

fof(f58,plain,
    ( v4_pre_topc(sK2,sK1)
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f56,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f57,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f35])).

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
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
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

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f59,plain,(
    v3_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK0(X0),X0)
        & v4_pre_topc(sK0(X0),X0)
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f48,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f60,plain,(
    v1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

cnf(c_19,negated_conjecture,
    ( v3_pre_topc(sK2,sK1)
    | v4_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_6,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_384,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_21])).

cnf(c_385,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),X0),sK1)
    | v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_384])).

cnf(c_444,plain,
    ( v4_pre_topc(X0,sK1)
    | v4_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_subset_1(u1_struct_0(sK1),X0) != sK2
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_385])).

cnf(c_506,plain,
    ( v4_pre_topc(X0,sK1)
    | v4_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_subset_1(u1_struct_0(sK1),X0) != sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_444])).

cnf(c_1049,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    | v4_pre_topc(sK2,sK1)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_506])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_898,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | k3_subset_1(X0,k3_subset_1(X0,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1017,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_898])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_838,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k3_subset_1(u1_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_975,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_838])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_745,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_399,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_21])).

cnf(c_400,plain,
    ( ~ v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_399])).

cnf(c_742,plain,
    ( k2_pre_topc(sK1,X0) = X0
    | v4_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_400])).

cnf(c_879,plain,
    ( k2_pre_topc(sK1,sK2) = sK2
    | v4_pre_topc(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_745,c_742])).

cnf(c_9,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_16,plain,
    ( ~ v3_tex_2(X0,X1)
    | v1_tops_1(X0,X1)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_18,negated_conjecture,
    ( v3_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_278,plain,
    ( v1_tops_1(X0,X1)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_18])).

cnf(c_279,plain,
    ( v1_tops_1(sK2,sK1)
    | ~ v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_278])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_281,plain,
    ( v1_tops_1(sK2,sK1)
    | ~ v3_pre_topc(sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_279,c_24,c_23,c_21,c_20])).

cnf(c_296,plain,
    ( ~ v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1)
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_281])).

cnf(c_297,plain,
    ( ~ v3_pre_topc(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_296])).

cnf(c_299,plain,
    ( ~ v3_pre_topc(sK2,sK1)
    | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_297,c_21,c_20])).

cnf(c_15,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_319,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_23])).

cnf(c_320,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_319])).

cnf(c_22,negated_conjecture,
    ( v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_324,plain,
    ( v3_pre_topc(X0,sK1)
    | ~ v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_320,c_22,c_21])).

cnf(c_436,plain,
    ( ~ v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1)
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_299,c_324])).

cnf(c_437,plain,
    ( ~ v4_pre_topc(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_436])).

cnf(c_426,plain,
    ( v4_pre_topc(sK2,sK1)
    | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_19,c_299])).

cnf(c_439,plain,
    ( k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_437,c_20,c_426])).

cnf(c_880,plain,
    ( u1_struct_0(sK1) = sK2
    | v4_pre_topc(sK2,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_879,c_439])).

cnf(c_465,plain,
    ( ~ v4_pre_topc(X0,sK1)
    | v4_pre_topc(X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_subset_1(u1_struct_0(sK1),X1) != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_324,c_385])).

cnf(c_466,plain,
    ( v4_pre_topc(X0,sK1)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK1),X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_465])).

cnf(c_478,plain,
    ( v4_pre_topc(X0,sK1)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK1),X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_466,c_2])).

cnf(c_823,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    | v4_pre_topc(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_478])).

cnf(c_820,plain,
    ( ~ v4_pre_topc(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,sK2) = sK2 ),
    inference(instantiation,[status(thm)],[c_400])).

cnf(c_4,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_340,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_23])).

cnf(c_341,plain,
    ( v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k2_pre_topc(sK1,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_340])).

cnf(c_345,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_pre_topc(X0,sK1)
    | k2_pre_topc(sK1,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_341,c_21])).

cnf(c_346,plain,
    ( v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,X0) != X0 ),
    inference(renaming,[status(thm)],[c_345])).

cnf(c_817,plain,
    ( v4_pre_topc(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,sK2) != sK2 ),
    inference(instantiation,[status(thm)],[c_346])).

cnf(c_818,plain,
    ( k2_pre_topc(sK1,sK2) != sK2
    | v4_pre_topc(sK2,sK1) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_817])).

cnf(c_11,plain,
    ( ~ v1_subset_1(X0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_17,negated_conjecture,
    ( v1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_265,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
    | u1_struct_0(sK1) != X0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_17])).

cnf(c_266,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK2 != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_265])).

cnf(c_744,plain,
    ( sK2 != u1_struct_0(sK1)
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_266])).

cnf(c_1,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_748,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_755,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_748,c_0])).

cnf(c_760,plain,
    ( u1_struct_0(sK1) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_744,c_755])).

cnf(c_29,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1049,c_1017,c_975,c_880,c_823,c_820,c_818,c_760,c_29,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:28:27 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.09/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/0.98  
% 2.09/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.09/0.98  
% 2.09/0.98  ------  iProver source info
% 2.09/0.98  
% 2.09/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.09/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.09/0.98  git: non_committed_changes: false
% 2.09/0.98  git: last_make_outside_of_git: false
% 2.09/0.98  
% 2.09/0.98  ------ 
% 2.09/0.98  
% 2.09/0.98  ------ Input Options
% 2.09/0.98  
% 2.09/0.98  --out_options                           all
% 2.09/0.98  --tptp_safe_out                         true
% 2.09/0.98  --problem_path                          ""
% 2.09/0.98  --include_path                          ""
% 2.09/0.98  --clausifier                            res/vclausify_rel
% 2.09/0.98  --clausifier_options                    --mode clausify
% 2.09/0.98  --stdin                                 false
% 2.09/0.98  --stats_out                             all
% 2.09/0.98  
% 2.09/0.98  ------ General Options
% 2.09/0.98  
% 2.09/0.98  --fof                                   false
% 2.09/0.98  --time_out_real                         305.
% 2.09/0.98  --time_out_virtual                      -1.
% 2.09/0.98  --symbol_type_check                     false
% 2.09/0.98  --clausify_out                          false
% 2.09/0.98  --sig_cnt_out                           false
% 2.09/0.98  --trig_cnt_out                          false
% 2.09/0.98  --trig_cnt_out_tolerance                1.
% 2.09/0.98  --trig_cnt_out_sk_spl                   false
% 2.09/0.98  --abstr_cl_out                          false
% 2.09/0.98  
% 2.09/0.98  ------ Global Options
% 2.09/0.98  
% 2.09/0.98  --schedule                              default
% 2.09/0.98  --add_important_lit                     false
% 2.09/0.98  --prop_solver_per_cl                    1000
% 2.09/0.98  --min_unsat_core                        false
% 2.09/0.98  --soft_assumptions                      false
% 2.09/0.98  --soft_lemma_size                       3
% 2.09/0.98  --prop_impl_unit_size                   0
% 2.09/0.98  --prop_impl_unit                        []
% 2.09/0.98  --share_sel_clauses                     true
% 2.09/0.98  --reset_solvers                         false
% 2.09/0.98  --bc_imp_inh                            [conj_cone]
% 2.09/0.98  --conj_cone_tolerance                   3.
% 2.09/0.98  --extra_neg_conj                        none
% 2.09/0.98  --large_theory_mode                     true
% 2.09/0.98  --prolific_symb_bound                   200
% 2.09/0.98  --lt_threshold                          2000
% 2.09/0.98  --clause_weak_htbl                      true
% 2.09/0.98  --gc_record_bc_elim                     false
% 2.09/0.98  
% 2.09/0.98  ------ Preprocessing Options
% 2.09/0.98  
% 2.09/0.98  --preprocessing_flag                    true
% 2.09/0.98  --time_out_prep_mult                    0.1
% 2.09/0.98  --splitting_mode                        input
% 2.09/0.98  --splitting_grd                         true
% 2.09/0.98  --splitting_cvd                         false
% 2.09/0.98  --splitting_cvd_svl                     false
% 2.09/0.98  --splitting_nvd                         32
% 2.09/0.98  --sub_typing                            true
% 2.09/0.98  --prep_gs_sim                           true
% 2.09/0.98  --prep_unflatten                        true
% 2.09/0.98  --prep_res_sim                          true
% 2.09/0.98  --prep_upred                            true
% 2.09/0.98  --prep_sem_filter                       exhaustive
% 2.09/0.98  --prep_sem_filter_out                   false
% 2.09/0.98  --pred_elim                             true
% 2.09/0.98  --res_sim_input                         true
% 2.09/0.98  --eq_ax_congr_red                       true
% 2.09/0.98  --pure_diseq_elim                       true
% 2.09/0.98  --brand_transform                       false
% 2.09/0.98  --non_eq_to_eq                          false
% 2.09/0.98  --prep_def_merge                        true
% 2.09/0.98  --prep_def_merge_prop_impl              false
% 2.09/0.98  --prep_def_merge_mbd                    true
% 2.09/0.98  --prep_def_merge_tr_red                 false
% 2.09/0.98  --prep_def_merge_tr_cl                  false
% 2.09/0.98  --smt_preprocessing                     true
% 2.09/0.98  --smt_ac_axioms                         fast
% 2.09/0.98  --preprocessed_out                      false
% 2.09/0.98  --preprocessed_stats                    false
% 2.09/0.98  
% 2.09/0.98  ------ Abstraction refinement Options
% 2.09/0.98  
% 2.09/0.98  --abstr_ref                             []
% 2.09/0.98  --abstr_ref_prep                        false
% 2.09/0.98  --abstr_ref_until_sat                   false
% 2.09/0.98  --abstr_ref_sig_restrict                funpre
% 2.09/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.09/0.98  --abstr_ref_under                       []
% 2.09/0.98  
% 2.09/0.98  ------ SAT Options
% 2.09/0.98  
% 2.09/0.98  --sat_mode                              false
% 2.09/0.98  --sat_fm_restart_options                ""
% 2.09/0.98  --sat_gr_def                            false
% 2.09/0.98  --sat_epr_types                         true
% 2.09/0.98  --sat_non_cyclic_types                  false
% 2.09/0.98  --sat_finite_models                     false
% 2.09/0.98  --sat_fm_lemmas                         false
% 2.09/0.98  --sat_fm_prep                           false
% 2.09/0.98  --sat_fm_uc_incr                        true
% 2.09/0.98  --sat_out_model                         small
% 2.09/0.98  --sat_out_clauses                       false
% 2.09/0.98  
% 2.09/0.98  ------ QBF Options
% 2.09/0.98  
% 2.09/0.98  --qbf_mode                              false
% 2.09/0.98  --qbf_elim_univ                         false
% 2.09/0.98  --qbf_dom_inst                          none
% 2.09/0.98  --qbf_dom_pre_inst                      false
% 2.09/0.98  --qbf_sk_in                             false
% 2.09/0.98  --qbf_pred_elim                         true
% 2.09/0.98  --qbf_split                             512
% 2.09/0.98  
% 2.09/0.98  ------ BMC1 Options
% 2.09/0.98  
% 2.09/0.98  --bmc1_incremental                      false
% 2.09/0.98  --bmc1_axioms                           reachable_all
% 2.09/0.98  --bmc1_min_bound                        0
% 2.09/0.98  --bmc1_max_bound                        -1
% 2.09/0.98  --bmc1_max_bound_default                -1
% 2.09/0.98  --bmc1_symbol_reachability              true
% 2.09/0.98  --bmc1_property_lemmas                  false
% 2.09/0.98  --bmc1_k_induction                      false
% 2.09/0.98  --bmc1_non_equiv_states                 false
% 2.09/0.98  --bmc1_deadlock                         false
% 2.09/0.98  --bmc1_ucm                              false
% 2.09/0.98  --bmc1_add_unsat_core                   none
% 2.09/0.98  --bmc1_unsat_core_children              false
% 2.09/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.09/0.98  --bmc1_out_stat                         full
% 2.09/0.98  --bmc1_ground_init                      false
% 2.09/0.98  --bmc1_pre_inst_next_state              false
% 2.09/0.98  --bmc1_pre_inst_state                   false
% 2.09/0.98  --bmc1_pre_inst_reach_state             false
% 2.09/0.98  --bmc1_out_unsat_core                   false
% 2.09/0.98  --bmc1_aig_witness_out                  false
% 2.09/0.98  --bmc1_verbose                          false
% 2.09/0.98  --bmc1_dump_clauses_tptp                false
% 2.09/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.09/0.98  --bmc1_dump_file                        -
% 2.09/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.09/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.09/0.98  --bmc1_ucm_extend_mode                  1
% 2.09/0.98  --bmc1_ucm_init_mode                    2
% 2.09/0.98  --bmc1_ucm_cone_mode                    none
% 2.09/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.09/0.98  --bmc1_ucm_relax_model                  4
% 2.09/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.09/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.09/0.98  --bmc1_ucm_layered_model                none
% 2.09/0.98  --bmc1_ucm_max_lemma_size               10
% 2.09/0.98  
% 2.09/0.98  ------ AIG Options
% 2.09/0.98  
% 2.09/0.98  --aig_mode                              false
% 2.09/0.98  
% 2.09/0.98  ------ Instantiation Options
% 2.09/0.98  
% 2.09/0.98  --instantiation_flag                    true
% 2.09/0.98  --inst_sos_flag                         false
% 2.09/0.98  --inst_sos_phase                        true
% 2.09/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.09/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.09/0.98  --inst_lit_sel_side                     num_symb
% 2.09/0.98  --inst_solver_per_active                1400
% 2.09/0.98  --inst_solver_calls_frac                1.
% 2.09/0.98  --inst_passive_queue_type               priority_queues
% 2.09/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.09/0.98  --inst_passive_queues_freq              [25;2]
% 2.09/0.98  --inst_dismatching                      true
% 2.09/0.98  --inst_eager_unprocessed_to_passive     true
% 2.09/0.98  --inst_prop_sim_given                   true
% 2.09/0.98  --inst_prop_sim_new                     false
% 2.09/0.98  --inst_subs_new                         false
% 2.09/0.98  --inst_eq_res_simp                      false
% 2.09/0.98  --inst_subs_given                       false
% 2.09/0.98  --inst_orphan_elimination               true
% 2.09/0.98  --inst_learning_loop_flag               true
% 2.09/0.98  --inst_learning_start                   3000
% 2.09/0.98  --inst_learning_factor                  2
% 2.09/0.98  --inst_start_prop_sim_after_learn       3
% 2.09/0.98  --inst_sel_renew                        solver
% 2.09/0.98  --inst_lit_activity_flag                true
% 2.09/0.98  --inst_restr_to_given                   false
% 2.09/0.98  --inst_activity_threshold               500
% 2.09/0.98  --inst_out_proof                        true
% 2.09/0.98  
% 2.09/0.98  ------ Resolution Options
% 2.09/0.98  
% 2.09/0.98  --resolution_flag                       true
% 2.09/0.98  --res_lit_sel                           adaptive
% 2.09/0.98  --res_lit_sel_side                      none
% 2.09/0.98  --res_ordering                          kbo
% 2.09/0.98  --res_to_prop_solver                    active
% 2.09/0.98  --res_prop_simpl_new                    false
% 2.09/0.98  --res_prop_simpl_given                  true
% 2.09/0.98  --res_passive_queue_type                priority_queues
% 2.09/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.09/0.98  --res_passive_queues_freq               [15;5]
% 2.09/0.98  --res_forward_subs                      full
% 2.09/0.98  --res_backward_subs                     full
% 2.09/0.98  --res_forward_subs_resolution           true
% 2.09/0.98  --res_backward_subs_resolution          true
% 2.09/0.98  --res_orphan_elimination                true
% 2.09/0.98  --res_time_limit                        2.
% 2.09/0.98  --res_out_proof                         true
% 2.09/0.98  
% 2.09/0.98  ------ Superposition Options
% 2.09/0.98  
% 2.09/0.98  --superposition_flag                    true
% 2.09/0.98  --sup_passive_queue_type                priority_queues
% 2.09/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.09/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.09/0.98  --demod_completeness_check              fast
% 2.09/0.98  --demod_use_ground                      true
% 2.09/0.98  --sup_to_prop_solver                    passive
% 2.09/0.98  --sup_prop_simpl_new                    true
% 2.09/0.98  --sup_prop_simpl_given                  true
% 2.09/0.98  --sup_fun_splitting                     false
% 2.09/0.98  --sup_smt_interval                      50000
% 2.09/0.98  
% 2.09/0.98  ------ Superposition Simplification Setup
% 2.09/0.98  
% 2.09/0.98  --sup_indices_passive                   []
% 2.09/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.09/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.98  --sup_full_bw                           [BwDemod]
% 2.09/0.98  --sup_immed_triv                        [TrivRules]
% 2.09/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.09/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.98  --sup_immed_bw_main                     []
% 2.09/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.09/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/0.98  
% 2.09/0.98  ------ Combination Options
% 2.09/0.98  
% 2.09/0.98  --comb_res_mult                         3
% 2.09/0.98  --comb_sup_mult                         2
% 2.09/0.98  --comb_inst_mult                        10
% 2.09/0.98  
% 2.09/0.98  ------ Debug Options
% 2.09/0.98  
% 2.09/0.98  --dbg_backtrace                         false
% 2.09/0.98  --dbg_dump_prop_clauses                 false
% 2.09/0.98  --dbg_dump_prop_clauses_file            -
% 2.09/0.98  --dbg_out_stat                          false
% 2.09/0.98  ------ Parsing...
% 2.09/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.09/0.98  
% 2.09/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 2.09/0.98  
% 2.09/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.09/0.98  
% 2.09/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.09/0.98  ------ Proving...
% 2.09/0.98  ------ Problem Properties 
% 2.09/0.98  
% 2.09/0.98  
% 2.09/0.98  clauses                                 11
% 2.09/0.98  conjectures                             1
% 2.09/0.98  EPR                                     0
% 2.09/0.98  Horn                                    10
% 2.09/0.98  unary                                   4
% 2.09/0.98  binary                                  3
% 2.09/0.98  lits                                    23
% 2.09/0.98  lits eq                                 7
% 2.09/0.98  fd_pure                                 0
% 2.09/0.98  fd_pseudo                               0
% 2.09/0.98  fd_cond                                 0
% 2.09/0.98  fd_pseudo_cond                          0
% 2.09/0.98  AC symbols                              0
% 2.09/0.98  
% 2.09/0.98  ------ Schedule dynamic 5 is on 
% 2.09/0.98  
% 2.09/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.09/0.98  
% 2.09/0.98  
% 2.09/0.98  ------ 
% 2.09/0.98  Current options:
% 2.09/0.98  ------ 
% 2.09/0.98  
% 2.09/0.98  ------ Input Options
% 2.09/0.98  
% 2.09/0.98  --out_options                           all
% 2.09/0.98  --tptp_safe_out                         true
% 2.09/0.98  --problem_path                          ""
% 2.09/0.98  --include_path                          ""
% 2.09/0.98  --clausifier                            res/vclausify_rel
% 2.09/0.98  --clausifier_options                    --mode clausify
% 2.09/0.98  --stdin                                 false
% 2.09/0.98  --stats_out                             all
% 2.09/0.98  
% 2.09/0.98  ------ General Options
% 2.09/0.98  
% 2.09/0.98  --fof                                   false
% 2.09/0.98  --time_out_real                         305.
% 2.09/0.98  --time_out_virtual                      -1.
% 2.09/0.98  --symbol_type_check                     false
% 2.09/0.98  --clausify_out                          false
% 2.09/0.98  --sig_cnt_out                           false
% 2.09/0.98  --trig_cnt_out                          false
% 2.09/0.98  --trig_cnt_out_tolerance                1.
% 2.09/0.98  --trig_cnt_out_sk_spl                   false
% 2.09/0.98  --abstr_cl_out                          false
% 2.09/0.98  
% 2.09/0.98  ------ Global Options
% 2.09/0.98  
% 2.09/0.98  --schedule                              default
% 2.09/0.98  --add_important_lit                     false
% 2.09/0.98  --prop_solver_per_cl                    1000
% 2.09/0.98  --min_unsat_core                        false
% 2.09/0.98  --soft_assumptions                      false
% 2.09/0.98  --soft_lemma_size                       3
% 2.09/0.98  --prop_impl_unit_size                   0
% 2.09/0.98  --prop_impl_unit                        []
% 2.09/0.98  --share_sel_clauses                     true
% 2.09/0.98  --reset_solvers                         false
% 2.09/0.98  --bc_imp_inh                            [conj_cone]
% 2.09/0.98  --conj_cone_tolerance                   3.
% 2.09/0.98  --extra_neg_conj                        none
% 2.09/0.98  --large_theory_mode                     true
% 2.09/0.98  --prolific_symb_bound                   200
% 2.09/0.98  --lt_threshold                          2000
% 2.09/0.98  --clause_weak_htbl                      true
% 2.09/0.98  --gc_record_bc_elim                     false
% 2.09/0.98  
% 2.09/0.98  ------ Preprocessing Options
% 2.09/0.98  
% 2.09/0.98  --preprocessing_flag                    true
% 2.09/0.98  --time_out_prep_mult                    0.1
% 2.09/0.98  --splitting_mode                        input
% 2.09/0.98  --splitting_grd                         true
% 2.09/0.98  --splitting_cvd                         false
% 2.09/0.98  --splitting_cvd_svl                     false
% 2.09/0.98  --splitting_nvd                         32
% 2.09/0.98  --sub_typing                            true
% 2.09/0.98  --prep_gs_sim                           true
% 2.09/0.98  --prep_unflatten                        true
% 2.09/0.98  --prep_res_sim                          true
% 2.09/0.98  --prep_upred                            true
% 2.09/0.98  --prep_sem_filter                       exhaustive
% 2.09/0.98  --prep_sem_filter_out                   false
% 2.09/0.98  --pred_elim                             true
% 2.09/0.98  --res_sim_input                         true
% 2.09/0.98  --eq_ax_congr_red                       true
% 2.09/0.98  --pure_diseq_elim                       true
% 2.09/0.98  --brand_transform                       false
% 2.09/0.98  --non_eq_to_eq                          false
% 2.09/0.98  --prep_def_merge                        true
% 2.09/0.98  --prep_def_merge_prop_impl              false
% 2.09/0.98  --prep_def_merge_mbd                    true
% 2.09/0.98  --prep_def_merge_tr_red                 false
% 2.09/0.98  --prep_def_merge_tr_cl                  false
% 2.09/0.98  --smt_preprocessing                     true
% 2.09/0.98  --smt_ac_axioms                         fast
% 2.09/0.98  --preprocessed_out                      false
% 2.09/0.98  --preprocessed_stats                    false
% 2.09/0.98  
% 2.09/0.98  ------ Abstraction refinement Options
% 2.09/0.98  
% 2.09/0.98  --abstr_ref                             []
% 2.09/0.98  --abstr_ref_prep                        false
% 2.09/0.98  --abstr_ref_until_sat                   false
% 2.09/0.98  --abstr_ref_sig_restrict                funpre
% 2.09/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.09/0.98  --abstr_ref_under                       []
% 2.09/0.98  
% 2.09/0.98  ------ SAT Options
% 2.09/0.98  
% 2.09/0.98  --sat_mode                              false
% 2.09/0.98  --sat_fm_restart_options                ""
% 2.09/0.98  --sat_gr_def                            false
% 2.09/0.98  --sat_epr_types                         true
% 2.09/0.98  --sat_non_cyclic_types                  false
% 2.09/0.98  --sat_finite_models                     false
% 2.09/0.98  --sat_fm_lemmas                         false
% 2.09/0.98  --sat_fm_prep                           false
% 2.09/0.98  --sat_fm_uc_incr                        true
% 2.09/0.98  --sat_out_model                         small
% 2.09/0.98  --sat_out_clauses                       false
% 2.09/0.98  
% 2.09/0.98  ------ QBF Options
% 2.09/0.98  
% 2.09/0.98  --qbf_mode                              false
% 2.09/0.98  --qbf_elim_univ                         false
% 2.09/0.98  --qbf_dom_inst                          none
% 2.09/0.98  --qbf_dom_pre_inst                      false
% 2.09/0.98  --qbf_sk_in                             false
% 2.09/0.98  --qbf_pred_elim                         true
% 2.09/0.98  --qbf_split                             512
% 2.09/0.98  
% 2.09/0.98  ------ BMC1 Options
% 2.09/0.98  
% 2.09/0.98  --bmc1_incremental                      false
% 2.09/0.98  --bmc1_axioms                           reachable_all
% 2.09/0.98  --bmc1_min_bound                        0
% 2.09/0.98  --bmc1_max_bound                        -1
% 2.09/0.98  --bmc1_max_bound_default                -1
% 2.09/0.98  --bmc1_symbol_reachability              true
% 2.09/0.98  --bmc1_property_lemmas                  false
% 2.09/0.98  --bmc1_k_induction                      false
% 2.09/0.98  --bmc1_non_equiv_states                 false
% 2.09/0.98  --bmc1_deadlock                         false
% 2.09/0.98  --bmc1_ucm                              false
% 2.09/0.98  --bmc1_add_unsat_core                   none
% 2.09/0.98  --bmc1_unsat_core_children              false
% 2.09/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.09/0.98  --bmc1_out_stat                         full
% 2.09/0.98  --bmc1_ground_init                      false
% 2.09/0.98  --bmc1_pre_inst_next_state              false
% 2.09/0.98  --bmc1_pre_inst_state                   false
% 2.09/0.98  --bmc1_pre_inst_reach_state             false
% 2.09/0.98  --bmc1_out_unsat_core                   false
% 2.09/0.98  --bmc1_aig_witness_out                  false
% 2.09/0.98  --bmc1_verbose                          false
% 2.09/0.98  --bmc1_dump_clauses_tptp                false
% 2.09/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.09/0.98  --bmc1_dump_file                        -
% 2.09/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.09/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.09/0.98  --bmc1_ucm_extend_mode                  1
% 2.09/0.98  --bmc1_ucm_init_mode                    2
% 2.09/0.98  --bmc1_ucm_cone_mode                    none
% 2.09/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.09/0.98  --bmc1_ucm_relax_model                  4
% 2.09/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.09/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.09/0.98  --bmc1_ucm_layered_model                none
% 2.09/0.98  --bmc1_ucm_max_lemma_size               10
% 2.09/0.98  
% 2.09/0.98  ------ AIG Options
% 2.09/0.98  
% 2.09/0.98  --aig_mode                              false
% 2.09/0.98  
% 2.09/0.98  ------ Instantiation Options
% 2.09/0.98  
% 2.09/0.98  --instantiation_flag                    true
% 2.09/0.98  --inst_sos_flag                         false
% 2.09/0.98  --inst_sos_phase                        true
% 2.09/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.09/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.09/0.98  --inst_lit_sel_side                     none
% 2.09/0.98  --inst_solver_per_active                1400
% 2.09/0.98  --inst_solver_calls_frac                1.
% 2.09/0.98  --inst_passive_queue_type               priority_queues
% 2.09/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.09/0.98  --inst_passive_queues_freq              [25;2]
% 2.09/0.98  --inst_dismatching                      true
% 2.09/0.98  --inst_eager_unprocessed_to_passive     true
% 2.09/0.98  --inst_prop_sim_given                   true
% 2.09/0.98  --inst_prop_sim_new                     false
% 2.09/0.98  --inst_subs_new                         false
% 2.09/0.98  --inst_eq_res_simp                      false
% 2.09/0.98  --inst_subs_given                       false
% 2.09/0.98  --inst_orphan_elimination               true
% 2.09/0.98  --inst_learning_loop_flag               true
% 2.09/0.98  --inst_learning_start                   3000
% 2.09/0.98  --inst_learning_factor                  2
% 2.09/0.98  --inst_start_prop_sim_after_learn       3
% 2.09/0.98  --inst_sel_renew                        solver
% 2.09/0.98  --inst_lit_activity_flag                true
% 2.09/0.98  --inst_restr_to_given                   false
% 2.09/0.98  --inst_activity_threshold               500
% 2.09/0.98  --inst_out_proof                        true
% 2.09/0.98  
% 2.09/0.98  ------ Resolution Options
% 2.09/0.98  
% 2.09/0.98  --resolution_flag                       false
% 2.09/0.98  --res_lit_sel                           adaptive
% 2.09/0.98  --res_lit_sel_side                      none
% 2.09/0.98  --res_ordering                          kbo
% 2.09/0.98  --res_to_prop_solver                    active
% 2.09/0.98  --res_prop_simpl_new                    false
% 2.09/0.98  --res_prop_simpl_given                  true
% 2.09/0.98  --res_passive_queue_type                priority_queues
% 2.09/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.09/0.98  --res_passive_queues_freq               [15;5]
% 2.09/0.98  --res_forward_subs                      full
% 2.09/0.98  --res_backward_subs                     full
% 2.09/0.98  --res_forward_subs_resolution           true
% 2.09/0.98  --res_backward_subs_resolution          true
% 2.09/0.98  --res_orphan_elimination                true
% 2.09/0.98  --res_time_limit                        2.
% 2.09/0.98  --res_out_proof                         true
% 2.09/0.98  
% 2.09/0.98  ------ Superposition Options
% 2.09/0.98  
% 2.09/0.98  --superposition_flag                    true
% 2.09/0.98  --sup_passive_queue_type                priority_queues
% 2.09/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.09/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.09/0.98  --demod_completeness_check              fast
% 2.09/0.98  --demod_use_ground                      true
% 2.09/0.98  --sup_to_prop_solver                    passive
% 2.09/0.98  --sup_prop_simpl_new                    true
% 2.09/0.98  --sup_prop_simpl_given                  true
% 2.09/0.98  --sup_fun_splitting                     false
% 2.09/0.98  --sup_smt_interval                      50000
% 2.09/0.98  
% 2.09/0.98  ------ Superposition Simplification Setup
% 2.09/0.98  
% 2.09/0.98  --sup_indices_passive                   []
% 2.09/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.09/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.98  --sup_full_bw                           [BwDemod]
% 2.09/0.98  --sup_immed_triv                        [TrivRules]
% 2.09/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.09/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.98  --sup_immed_bw_main                     []
% 2.09/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.09/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/0.98  
% 2.09/0.98  ------ Combination Options
% 2.09/0.98  
% 2.09/0.98  --comb_res_mult                         3
% 2.09/0.98  --comb_sup_mult                         2
% 2.09/0.98  --comb_inst_mult                        10
% 2.09/0.98  
% 2.09/0.98  ------ Debug Options
% 2.09/0.98  
% 2.09/0.98  --dbg_backtrace                         false
% 2.09/0.98  --dbg_dump_prop_clauses                 false
% 2.09/0.98  --dbg_dump_prop_clauses_file            -
% 2.09/0.98  --dbg_out_stat                          false
% 2.09/0.98  
% 2.09/0.98  
% 2.09/0.98  
% 2.09/0.98  
% 2.09/0.98  ------ Proving...
% 2.09/0.98  
% 2.09/0.98  
% 2.09/0.98  % SZS status Theorem for theBenchmark.p
% 2.09/0.98  
% 2.09/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.09/0.98  
% 2.09/0.98  fof(f11,conjecture,(
% 2.09/0.98    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)))))),
% 2.09/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.98  
% 2.09/0.98  fof(f12,negated_conjecture,(
% 2.09/0.98    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)))))),
% 2.09/0.98    inference(negated_conjecture,[],[f11])).
% 2.09/0.98  
% 2.09/0.98  fof(f24,plain,(
% 2.09/0.98    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.09/0.98    inference(ennf_transformation,[],[f12])).
% 2.09/0.98  
% 2.09/0.98  fof(f25,plain,(
% 2.09/0.98    ? [X0] : (? [X1] : (v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.09/0.98    inference(flattening,[],[f24])).
% 2.09/0.98  
% 2.09/0.98  fof(f34,plain,(
% 2.09/0.98    ( ! [X0] : (? [X1] : (v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v1_subset_1(sK2,u1_struct_0(X0)) & v3_tex_2(sK2,X0) & (v4_pre_topc(sK2,X0) | v3_pre_topc(sK2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.09/0.98    introduced(choice_axiom,[])).
% 2.09/0.98  
% 2.09/0.98  fof(f33,plain,(
% 2.09/0.98    ? [X0] : (? [X1] : (v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (v1_subset_1(X1,u1_struct_0(sK1)) & v3_tex_2(X1,sK1) & (v4_pre_topc(X1,sK1) | v3_pre_topc(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v3_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.09/0.98    introduced(choice_axiom,[])).
% 2.09/0.98  
% 2.09/0.98  fof(f35,plain,(
% 2.09/0.98    (v1_subset_1(sK2,u1_struct_0(sK1)) & v3_tex_2(sK2,sK1) & (v4_pre_topc(sK2,sK1) | v3_pre_topc(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v3_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.09/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f25,f34,f33])).
% 2.09/0.98  
% 2.09/0.98  fof(f58,plain,(
% 2.09/0.98    v4_pre_topc(sK2,sK1) | v3_pre_topc(sK2,sK1)),
% 2.09/0.98    inference(cnf_transformation,[],[f35])).
% 2.09/0.98  
% 2.09/0.98  fof(f6,axiom,(
% 2.09/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 2.09/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.98  
% 2.09/0.98  fof(f17,plain,(
% 2.09/0.98    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.09/0.98    inference(ennf_transformation,[],[f6])).
% 2.09/0.98  
% 2.09/0.98  fof(f26,plain,(
% 2.09/0.98    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.09/0.98    inference(nnf_transformation,[],[f17])).
% 2.09/0.98  
% 2.09/0.98  fof(f43,plain,(
% 2.09/0.98    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.09/0.98    inference(cnf_transformation,[],[f26])).
% 2.09/0.98  
% 2.09/0.98  fof(f56,plain,(
% 2.09/0.98    l1_pre_topc(sK1)),
% 2.09/0.98    inference(cnf_transformation,[],[f35])).
% 2.09/0.98  
% 2.09/0.98  fof(f4,axiom,(
% 2.09/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.09/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.98  
% 2.09/0.98  fof(f14,plain,(
% 2.09/0.98    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.09/0.98    inference(ennf_transformation,[],[f4])).
% 2.09/0.98  
% 2.09/0.98  fof(f39,plain,(
% 2.09/0.98    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.09/0.98    inference(cnf_transformation,[],[f14])).
% 2.09/0.98  
% 2.09/0.98  fof(f3,axiom,(
% 2.09/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.09/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.98  
% 2.09/0.98  fof(f13,plain,(
% 2.09/0.98    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.09/0.98    inference(ennf_transformation,[],[f3])).
% 2.09/0.98  
% 2.09/0.98  fof(f38,plain,(
% 2.09/0.98    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.09/0.98    inference(cnf_transformation,[],[f13])).
% 2.09/0.98  
% 2.09/0.98  fof(f57,plain,(
% 2.09/0.98    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.09/0.98    inference(cnf_transformation,[],[f35])).
% 2.09/0.98  
% 2.09/0.98  fof(f5,axiom,(
% 2.09/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.09/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.98  
% 2.09/0.98  fof(f15,plain,(
% 2.09/0.98    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.09/0.98    inference(ennf_transformation,[],[f5])).
% 2.09/0.98  
% 2.09/0.98  fof(f16,plain,(
% 2.09/0.98    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.09/0.98    inference(flattening,[],[f15])).
% 2.09/0.98  
% 2.09/0.98  fof(f40,plain,(
% 2.09/0.98    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.09/0.98    inference(cnf_transformation,[],[f16])).
% 2.09/0.98  
% 2.09/0.98  fof(f7,axiom,(
% 2.09/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 2.09/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.98  
% 2.09/0.98  fof(f18,plain,(
% 2.09/0.98    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.09/0.98    inference(ennf_transformation,[],[f7])).
% 2.09/0.98  
% 2.09/0.98  fof(f27,plain,(
% 2.09/0.98    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.09/0.98    inference(nnf_transformation,[],[f18])).
% 2.09/0.98  
% 2.09/0.98  fof(f44,plain,(
% 2.09/0.98    ( ! [X0,X1] : (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.09/0.98    inference(cnf_transformation,[],[f27])).
% 2.09/0.98  
% 2.09/0.98  fof(f10,axiom,(
% 2.09/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 2.09/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.98  
% 2.09/0.98  fof(f22,plain,(
% 2.09/0.98    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.09/0.98    inference(ennf_transformation,[],[f10])).
% 2.09/0.98  
% 2.09/0.98  fof(f23,plain,(
% 2.09/0.98    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.09/0.98    inference(flattening,[],[f22])).
% 2.09/0.98  
% 2.09/0.98  fof(f52,plain,(
% 2.09/0.98    ( ! [X0,X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.98    inference(cnf_transformation,[],[f23])).
% 2.09/0.98  
% 2.09/0.98  fof(f59,plain,(
% 2.09/0.98    v3_tex_2(sK2,sK1)),
% 2.09/0.98    inference(cnf_transformation,[],[f35])).
% 2.09/0.98  
% 2.09/0.98  fof(f53,plain,(
% 2.09/0.98    ~v2_struct_0(sK1)),
% 2.09/0.98    inference(cnf_transformation,[],[f35])).
% 2.09/0.98  
% 2.09/0.98  fof(f54,plain,(
% 2.09/0.98    v2_pre_topc(sK1)),
% 2.09/0.98    inference(cnf_transformation,[],[f35])).
% 2.09/0.98  
% 2.09/0.98  fof(f9,axiom,(
% 2.09/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 2.09/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.98  
% 2.09/0.98  fof(f20,plain,(
% 2.09/0.98    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.09/0.98    inference(ennf_transformation,[],[f9])).
% 2.09/0.98  
% 2.09/0.98  fof(f21,plain,(
% 2.09/0.98    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.09/0.98    inference(flattening,[],[f20])).
% 2.09/0.98  
% 2.09/0.98  fof(f29,plain,(
% 2.09/0.98    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.09/0.98    inference(nnf_transformation,[],[f21])).
% 2.09/0.98  
% 2.09/0.98  fof(f30,plain,(
% 2.09/0.98    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.09/0.98    inference(rectify,[],[f29])).
% 2.09/0.98  
% 2.09/0.98  fof(f31,plain,(
% 2.09/0.98    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK0(X0),X0) & v4_pre_topc(sK0(X0),X0) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.09/0.98    introduced(choice_axiom,[])).
% 2.09/0.98  
% 2.09/0.98  fof(f32,plain,(
% 2.09/0.98    ! [X0] : (((v3_tdlat_3(X0) | (~v3_pre_topc(sK0(X0),X0) & v4_pre_topc(sK0(X0),X0) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.09/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 2.09/0.98  
% 2.09/0.98  fof(f48,plain,(
% 2.09/0.98    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.09/0.98    inference(cnf_transformation,[],[f32])).
% 2.09/0.98  
% 2.09/0.98  fof(f55,plain,(
% 2.09/0.98    v3_tdlat_3(sK1)),
% 2.09/0.98    inference(cnf_transformation,[],[f35])).
% 2.09/0.98  
% 2.09/0.98  fof(f41,plain,(
% 2.09/0.98    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.09/0.98    inference(cnf_transformation,[],[f16])).
% 2.09/0.98  
% 2.09/0.98  fof(f8,axiom,(
% 2.09/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 2.09/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.98  
% 2.09/0.98  fof(f19,plain,(
% 2.09/0.98    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.09/0.98    inference(ennf_transformation,[],[f8])).
% 2.09/0.98  
% 2.09/0.98  fof(f28,plain,(
% 2.09/0.98    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.09/0.98    inference(nnf_transformation,[],[f19])).
% 2.09/0.98  
% 2.09/0.98  fof(f46,plain,(
% 2.09/0.98    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.09/0.98    inference(cnf_transformation,[],[f28])).
% 2.09/0.98  
% 2.09/0.98  fof(f61,plain,(
% 2.09/0.98    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 2.09/0.98    inference(equality_resolution,[],[f46])).
% 2.09/0.98  
% 2.09/0.98  fof(f60,plain,(
% 2.09/0.98    v1_subset_1(sK2,u1_struct_0(sK1))),
% 2.09/0.98    inference(cnf_transformation,[],[f35])).
% 2.09/0.98  
% 2.09/0.98  fof(f2,axiom,(
% 2.09/0.98    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.09/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.98  
% 2.09/0.98  fof(f37,plain,(
% 2.09/0.98    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.09/0.98    inference(cnf_transformation,[],[f2])).
% 2.09/0.98  
% 2.09/0.98  fof(f1,axiom,(
% 2.09/0.98    ! [X0] : k2_subset_1(X0) = X0),
% 2.09/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.98  
% 2.09/0.98  fof(f36,plain,(
% 2.09/0.98    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.09/0.98    inference(cnf_transformation,[],[f1])).
% 2.09/0.98  
% 2.09/0.98  cnf(c_19,negated_conjecture,
% 2.09/0.98      ( v3_pre_topc(sK2,sK1) | v4_pre_topc(sK2,sK1) ),
% 2.09/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_6,plain,
% 2.09/0.98      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 2.09/0.98      | v4_pre_topc(X1,X0)
% 2.09/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.09/0.98      | ~ l1_pre_topc(X0) ),
% 2.09/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_21,negated_conjecture,
% 2.09/0.98      ( l1_pre_topc(sK1) ),
% 2.09/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_384,plain,
% 2.09/0.98      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 2.09/0.98      | v4_pre_topc(X1,X0)
% 2.09/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.09/0.98      | sK1 != X0 ),
% 2.09/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_21]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_385,plain,
% 2.09/0.98      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),X0),sK1)
% 2.09/0.98      | v4_pre_topc(X0,sK1)
% 2.09/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.09/0.98      inference(unflattening,[status(thm)],[c_384]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_444,plain,
% 2.09/0.98      ( v4_pre_topc(X0,sK1)
% 2.09/0.98      | v4_pre_topc(sK2,sK1)
% 2.09/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.09/0.98      | k3_subset_1(u1_struct_0(sK1),X0) != sK2
% 2.09/0.98      | sK1 != sK1 ),
% 2.09/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_385]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_506,plain,
% 2.09/0.98      ( v4_pre_topc(X0,sK1)
% 2.09/0.98      | v4_pre_topc(sK2,sK1)
% 2.09/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.09/0.98      | k3_subset_1(u1_struct_0(sK1),X0) != sK2 ),
% 2.09/0.98      inference(equality_resolution_simp,[status(thm)],[c_444]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_1049,plain,
% 2.09/0.98      ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
% 2.09/0.98      | v4_pre_topc(sK2,sK1)
% 2.09/0.98      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.09/0.98      | k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK2)) != sK2 ),
% 2.09/0.98      inference(instantiation,[status(thm)],[c_506]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_3,plain,
% 2.09/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.09/0.98      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 2.09/0.98      inference(cnf_transformation,[],[f39]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_898,plain,
% 2.09/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
% 2.09/0.98      | k3_subset_1(X0,k3_subset_1(X0,sK2)) = sK2 ),
% 2.09/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_1017,plain,
% 2.09/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.09/0.98      | k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK2)) = sK2 ),
% 2.09/0.98      inference(instantiation,[status(thm)],[c_898]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_2,plain,
% 2.09/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.09/0.98      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 2.09/0.98      inference(cnf_transformation,[],[f38]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_838,plain,
% 2.09/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.09/0.98      | m1_subset_1(k3_subset_1(u1_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.09/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_975,plain,
% 2.09/0.98      ( m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.09/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.09/0.98      inference(instantiation,[status(thm)],[c_838]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_20,negated_conjecture,
% 2.09/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.09/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_745,plain,
% 2.09/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.09/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_5,plain,
% 2.09/0.98      ( ~ v4_pre_topc(X0,X1)
% 2.09/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.09/0.98      | ~ l1_pre_topc(X1)
% 2.09/0.98      | k2_pre_topc(X1,X0) = X0 ),
% 2.09/0.98      inference(cnf_transformation,[],[f40]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_399,plain,
% 2.09/0.98      ( ~ v4_pre_topc(X0,X1)
% 2.09/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.09/0.98      | k2_pre_topc(X1,X0) = X0
% 2.09/0.98      | sK1 != X1 ),
% 2.09/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_21]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_400,plain,
% 2.09/0.98      ( ~ v4_pre_topc(X0,sK1)
% 2.09/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.09/0.98      | k2_pre_topc(sK1,X0) = X0 ),
% 2.09/0.98      inference(unflattening,[status(thm)],[c_399]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_742,plain,
% 2.09/0.98      ( k2_pre_topc(sK1,X0) = X0
% 2.09/0.98      | v4_pre_topc(X0,sK1) != iProver_top
% 2.09/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.09/0.98      inference(predicate_to_equality,[status(thm)],[c_400]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_879,plain,
% 2.09/0.98      ( k2_pre_topc(sK1,sK2) = sK2
% 2.09/0.98      | v4_pre_topc(sK2,sK1) != iProver_top ),
% 2.09/0.98      inference(superposition,[status(thm)],[c_745,c_742]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_9,plain,
% 2.09/0.98      ( ~ v1_tops_1(X0,X1)
% 2.09/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.09/0.98      | ~ l1_pre_topc(X1)
% 2.09/0.98      | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
% 2.09/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_16,plain,
% 2.09/0.98      ( ~ v3_tex_2(X0,X1)
% 2.09/0.98      | v1_tops_1(X0,X1)
% 2.09/0.98      | ~ v3_pre_topc(X0,X1)
% 2.09/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.09/0.98      | v2_struct_0(X1)
% 2.09/0.98      | ~ l1_pre_topc(X1)
% 2.09/0.98      | ~ v2_pre_topc(X1) ),
% 2.09/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_18,negated_conjecture,
% 2.09/0.98      ( v3_tex_2(sK2,sK1) ),
% 2.09/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_278,plain,
% 2.09/0.98      ( v1_tops_1(X0,X1)
% 2.09/0.98      | ~ v3_pre_topc(X0,X1)
% 2.09/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.09/0.98      | v2_struct_0(X1)
% 2.09/0.98      | ~ l1_pre_topc(X1)
% 2.09/0.98      | ~ v2_pre_topc(X1)
% 2.09/0.98      | sK1 != X1
% 2.09/0.98      | sK2 != X0 ),
% 2.09/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_18]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_279,plain,
% 2.09/0.98      ( v1_tops_1(sK2,sK1)
% 2.09/0.98      | ~ v3_pre_topc(sK2,sK1)
% 2.09/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.09/0.98      | v2_struct_0(sK1)
% 2.09/0.98      | ~ l1_pre_topc(sK1)
% 2.09/0.98      | ~ v2_pre_topc(sK1) ),
% 2.09/0.98      inference(unflattening,[status(thm)],[c_278]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_24,negated_conjecture,
% 2.09/0.98      ( ~ v2_struct_0(sK1) ),
% 2.09/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_23,negated_conjecture,
% 2.09/0.98      ( v2_pre_topc(sK1) ),
% 2.09/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_281,plain,
% 2.09/0.98      ( v1_tops_1(sK2,sK1) | ~ v3_pre_topc(sK2,sK1) ),
% 2.09/0.98      inference(global_propositional_subsumption,
% 2.09/0.98                [status(thm)],
% 2.09/0.98                [c_279,c_24,c_23,c_21,c_20]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_296,plain,
% 2.09/0.98      ( ~ v3_pre_topc(sK2,sK1)
% 2.09/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.09/0.98      | ~ l1_pre_topc(X1)
% 2.09/0.98      | k2_pre_topc(X1,X0) = u1_struct_0(X1)
% 2.09/0.98      | sK1 != X1
% 2.09/0.98      | sK2 != X0 ),
% 2.09/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_281]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_297,plain,
% 2.09/0.98      ( ~ v3_pre_topc(sK2,sK1)
% 2.09/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.09/0.98      | ~ l1_pre_topc(sK1)
% 2.09/0.98      | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
% 2.09/0.98      inference(unflattening,[status(thm)],[c_296]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_299,plain,
% 2.09/0.98      ( ~ v3_pre_topc(sK2,sK1)
% 2.09/0.98      | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
% 2.09/0.98      inference(global_propositional_subsumption,
% 2.09/0.98                [status(thm)],
% 2.09/0.98                [c_297,c_21,c_20]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_15,plain,
% 2.09/0.98      ( v3_pre_topc(X0,X1)
% 2.09/0.98      | ~ v4_pre_topc(X0,X1)
% 2.09/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.09/0.98      | ~ v3_tdlat_3(X1)
% 2.09/0.98      | ~ l1_pre_topc(X1)
% 2.09/0.98      | ~ v2_pre_topc(X1) ),
% 2.09/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_319,plain,
% 2.09/0.98      ( v3_pre_topc(X0,X1)
% 2.09/0.98      | ~ v4_pre_topc(X0,X1)
% 2.09/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.09/0.98      | ~ v3_tdlat_3(X1)
% 2.09/0.98      | ~ l1_pre_topc(X1)
% 2.09/0.98      | sK1 != X1 ),
% 2.09/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_23]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_320,plain,
% 2.09/0.98      ( v3_pre_topc(X0,sK1)
% 2.09/0.98      | ~ v4_pre_topc(X0,sK1)
% 2.09/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.09/0.98      | ~ v3_tdlat_3(sK1)
% 2.09/0.98      | ~ l1_pre_topc(sK1) ),
% 2.09/0.98      inference(unflattening,[status(thm)],[c_319]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_22,negated_conjecture,
% 2.09/0.98      ( v3_tdlat_3(sK1) ),
% 2.09/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_324,plain,
% 2.09/0.98      ( v3_pre_topc(X0,sK1)
% 2.09/0.98      | ~ v4_pre_topc(X0,sK1)
% 2.09/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.09/0.98      inference(global_propositional_subsumption,
% 2.09/0.98                [status(thm)],
% 2.09/0.98                [c_320,c_22,c_21]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_436,plain,
% 2.09/0.98      ( ~ v4_pre_topc(X0,sK1)
% 2.09/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.09/0.98      | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1)
% 2.09/0.98      | sK1 != sK1
% 2.09/0.98      | sK2 != X0 ),
% 2.09/0.98      inference(resolution_lifted,[status(thm)],[c_299,c_324]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_437,plain,
% 2.09/0.98      ( ~ v4_pre_topc(sK2,sK1)
% 2.09/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.09/0.98      | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
% 2.09/0.98      inference(unflattening,[status(thm)],[c_436]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_426,plain,
% 2.09/0.98      ( v4_pre_topc(sK2,sK1) | k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
% 2.09/0.98      inference(resolution,[status(thm)],[c_19,c_299]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_439,plain,
% 2.09/0.98      ( k2_pre_topc(sK1,sK2) = u1_struct_0(sK1) ),
% 2.09/0.98      inference(global_propositional_subsumption,
% 2.09/0.98                [status(thm)],
% 2.09/0.98                [c_437,c_20,c_426]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_880,plain,
% 2.09/0.98      ( u1_struct_0(sK1) = sK2 | v4_pre_topc(sK2,sK1) != iProver_top ),
% 2.09/0.98      inference(demodulation,[status(thm)],[c_879,c_439]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_465,plain,
% 2.09/0.98      ( ~ v4_pre_topc(X0,sK1)
% 2.09/0.98      | v4_pre_topc(X1,sK1)
% 2.09/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.09/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.09/0.98      | k3_subset_1(u1_struct_0(sK1),X1) != X0
% 2.09/0.98      | sK1 != sK1 ),
% 2.09/0.98      inference(resolution_lifted,[status(thm)],[c_324,c_385]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_466,plain,
% 2.09/0.98      ( v4_pre_topc(X0,sK1)
% 2.09/0.98      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK1),X0),sK1)
% 2.09/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.09/0.98      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.09/0.98      inference(unflattening,[status(thm)],[c_465]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_478,plain,
% 2.09/0.98      ( v4_pre_topc(X0,sK1)
% 2.09/0.98      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK1),X0),sK1)
% 2.09/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.09/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_466,c_2]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_823,plain,
% 2.09/0.98      ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
% 2.09/0.98      | v4_pre_topc(sK2,sK1)
% 2.09/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.09/0.98      inference(instantiation,[status(thm)],[c_478]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_820,plain,
% 2.09/0.98      ( ~ v4_pre_topc(sK2,sK1)
% 2.09/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.09/0.98      | k2_pre_topc(sK1,sK2) = sK2 ),
% 2.09/0.98      inference(instantiation,[status(thm)],[c_400]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_4,plain,
% 2.09/0.98      ( v4_pre_topc(X0,X1)
% 2.09/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.09/0.98      | ~ l1_pre_topc(X1)
% 2.09/0.98      | ~ v2_pre_topc(X1)
% 2.09/0.98      | k2_pre_topc(X1,X0) != X0 ),
% 2.09/0.98      inference(cnf_transformation,[],[f41]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_340,plain,
% 2.09/0.98      ( v4_pre_topc(X0,X1)
% 2.09/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.09/0.98      | ~ l1_pre_topc(X1)
% 2.09/0.98      | k2_pre_topc(X1,X0) != X0
% 2.09/0.98      | sK1 != X1 ),
% 2.09/0.98      inference(resolution_lifted,[status(thm)],[c_4,c_23]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_341,plain,
% 2.09/0.98      ( v4_pre_topc(X0,sK1)
% 2.09/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.09/0.98      | ~ l1_pre_topc(sK1)
% 2.09/0.98      | k2_pre_topc(sK1,X0) != X0 ),
% 2.09/0.98      inference(unflattening,[status(thm)],[c_340]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_345,plain,
% 2.09/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.09/0.98      | v4_pre_topc(X0,sK1)
% 2.09/0.98      | k2_pre_topc(sK1,X0) != X0 ),
% 2.09/0.98      inference(global_propositional_subsumption,
% 2.09/0.98                [status(thm)],
% 2.09/0.98                [c_341,c_21]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_346,plain,
% 2.09/0.98      ( v4_pre_topc(X0,sK1)
% 2.09/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.09/0.98      | k2_pre_topc(sK1,X0) != X0 ),
% 2.09/0.98      inference(renaming,[status(thm)],[c_345]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_817,plain,
% 2.09/0.98      ( v4_pre_topc(sK2,sK1)
% 2.09/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.09/0.98      | k2_pre_topc(sK1,sK2) != sK2 ),
% 2.09/0.98      inference(instantiation,[status(thm)],[c_346]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_818,plain,
% 2.09/0.98      ( k2_pre_topc(sK1,sK2) != sK2
% 2.09/0.98      | v4_pre_topc(sK2,sK1) = iProver_top
% 2.09/0.98      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.09/0.98      inference(predicate_to_equality,[status(thm)],[c_817]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_11,plain,
% 2.09/0.98      ( ~ v1_subset_1(X0,X0) | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
% 2.09/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_17,negated_conjecture,
% 2.09/0.98      ( v1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.09/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_265,plain,
% 2.09/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
% 2.09/0.98      | u1_struct_0(sK1) != X0
% 2.09/0.98      | sK2 != X0 ),
% 2.09/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_17]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_266,plain,
% 2.09/0.98      ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.09/0.98      | sK2 != u1_struct_0(sK1) ),
% 2.09/0.98      inference(unflattening,[status(thm)],[c_265]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_744,plain,
% 2.09/0.98      ( sK2 != u1_struct_0(sK1)
% 2.09/0.98      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.09/0.98      inference(predicate_to_equality,[status(thm)],[c_266]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_1,plain,
% 2.09/0.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.09/0.98      inference(cnf_transformation,[],[f37]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_748,plain,
% 2.09/0.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.09/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_0,plain,
% 2.09/0.98      ( k2_subset_1(X0) = X0 ),
% 2.09/0.98      inference(cnf_transformation,[],[f36]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_755,plain,
% 2.09/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.09/0.98      inference(light_normalisation,[status(thm)],[c_748,c_0]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_760,plain,
% 2.09/0.98      ( u1_struct_0(sK1) != sK2 ),
% 2.09/0.98      inference(forward_subsumption_resolution,
% 2.09/0.98                [status(thm)],
% 2.09/0.98                [c_744,c_755]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(c_29,plain,
% 2.09/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.09/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.09/0.98  
% 2.09/0.98  cnf(contradiction,plain,
% 2.09/0.98      ( $false ),
% 2.09/0.98      inference(minisat,
% 2.09/0.98                [status(thm)],
% 2.09/0.98                [c_1049,c_1017,c_975,c_880,c_823,c_820,c_818,c_760,c_29,
% 2.09/0.98                 c_20]) ).
% 2.09/0.98  
% 2.09/0.98  
% 2.09/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.09/0.98  
% 2.09/0.98  ------                               Statistics
% 2.09/0.98  
% 2.09/0.98  ------ General
% 2.09/0.98  
% 2.09/0.98  abstr_ref_over_cycles:                  0
% 2.09/0.98  abstr_ref_under_cycles:                 0
% 2.09/0.98  gc_basic_clause_elim:                   0
% 2.09/0.98  forced_gc_time:                         0
% 2.09/0.98  parsing_time:                           0.008
% 2.09/0.98  unif_index_cands_time:                  0.
% 2.09/0.98  unif_index_add_time:                    0.
% 2.09/0.98  orderings_time:                         0.
% 2.09/0.98  out_proof_time:                         0.009
% 2.09/0.98  total_time:                             0.067
% 2.09/0.98  num_of_symbols:                         49
% 2.09/0.98  num_of_terms:                           817
% 2.09/0.98  
% 2.09/0.98  ------ Preprocessing
% 2.09/0.98  
% 2.09/0.98  num_of_splits:                          0
% 2.09/0.98  num_of_split_atoms:                     0
% 2.09/0.98  num_of_reused_defs:                     0
% 2.09/0.98  num_eq_ax_congr_red:                    8
% 2.09/0.98  num_of_sem_filtered_clauses:            1
% 2.09/0.98  num_of_subtypes:                        0
% 2.09/0.98  monotx_restored_types:                  0
% 2.09/0.98  sat_num_of_epr_types:                   0
% 2.09/0.98  sat_num_of_non_cyclic_types:            0
% 2.09/0.98  sat_guarded_non_collapsed_types:        0
% 2.09/0.98  num_pure_diseq_elim:                    0
% 2.09/0.98  simp_replaced_by:                       0
% 2.09/0.98  res_preprocessed:                       75
% 2.09/0.98  prep_upred:                             0
% 2.09/0.98  prep_unflattend:                        17
% 2.09/0.98  smt_new_axioms:                         0
% 2.09/0.98  pred_elim_cands:                        2
% 2.09/0.98  pred_elim:                              8
% 2.09/0.98  pred_elim_cl:                           14
% 2.09/0.98  pred_elim_cycles:                       10
% 2.09/0.98  merged_defs:                            0
% 2.09/0.98  merged_defs_ncl:                        0
% 2.09/0.98  bin_hyper_res:                          0
% 2.09/0.98  prep_cycles:                            4
% 2.09/0.98  pred_elim_time:                         0.005
% 2.09/0.98  splitting_time:                         0.
% 2.09/0.98  sem_filter_time:                        0.
% 2.09/0.98  monotx_time:                            0.001
% 2.09/0.98  subtype_inf_time:                       0.
% 2.09/0.98  
% 2.09/0.98  ------ Problem properties
% 2.09/0.98  
% 2.09/0.98  clauses:                                11
% 2.09/0.98  conjectures:                            1
% 2.09/0.98  epr:                                    0
% 2.09/0.98  horn:                                   10
% 2.09/0.98  ground:                                 3
% 2.09/0.98  unary:                                  4
% 2.09/0.98  binary:                                 3
% 2.09/0.98  lits:                                   23
% 2.09/0.98  lits_eq:                                7
% 2.09/0.98  fd_pure:                                0
% 2.09/0.98  fd_pseudo:                              0
% 2.09/0.98  fd_cond:                                0
% 2.09/0.98  fd_pseudo_cond:                         0
% 2.09/0.98  ac_symbols:                             0
% 2.09/0.98  
% 2.09/0.98  ------ Propositional Solver
% 2.09/0.98  
% 2.09/0.98  prop_solver_calls:                      24
% 2.09/0.98  prop_fast_solver_calls:                 445
% 2.09/0.98  smt_solver_calls:                       0
% 2.09/0.98  smt_fast_solver_calls:                  0
% 2.09/0.98  prop_num_of_clauses:                    272
% 2.09/0.98  prop_preprocess_simplified:             1939
% 2.09/0.98  prop_fo_subsumed:                       13
% 2.09/0.98  prop_solver_time:                       0.
% 2.09/0.98  smt_solver_time:                        0.
% 2.09/0.98  smt_fast_solver_time:                   0.
% 2.09/0.98  prop_fast_solver_time:                  0.
% 2.09/0.98  prop_unsat_core_time:                   0.
% 2.09/0.98  
% 2.09/0.98  ------ QBF
% 2.09/0.98  
% 2.09/0.98  qbf_q_res:                              0
% 2.09/0.98  qbf_num_tautologies:                    0
% 2.09/0.98  qbf_prep_cycles:                        0
% 2.09/0.98  
% 2.09/0.98  ------ BMC1
% 2.09/0.98  
% 2.09/0.98  bmc1_current_bound:                     -1
% 2.09/0.98  bmc1_last_solved_bound:                 -1
% 2.09/0.98  bmc1_unsat_core_size:                   -1
% 2.09/0.98  bmc1_unsat_core_parents_size:           -1
% 2.09/0.98  bmc1_merge_next_fun:                    0
% 2.09/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.09/0.98  
% 2.09/0.98  ------ Instantiation
% 2.09/0.98  
% 2.09/0.98  inst_num_of_clauses:                    60
% 2.09/0.98  inst_num_in_passive:                    18
% 2.09/0.98  inst_num_in_active:                     40
% 2.09/0.98  inst_num_in_unprocessed:                1
% 2.09/0.98  inst_num_of_loops:                      46
% 2.09/0.98  inst_num_of_learning_restarts:          0
% 2.09/0.98  inst_num_moves_active_passive:          3
% 2.09/0.98  inst_lit_activity:                      0
% 2.09/0.98  inst_lit_activity_moves:                0
% 2.09/0.98  inst_num_tautologies:                   0
% 2.09/0.98  inst_num_prop_implied:                  0
% 2.09/0.98  inst_num_existing_simplified:           0
% 2.09/0.98  inst_num_eq_res_simplified:             0
% 2.09/0.98  inst_num_child_elim:                    0
% 2.09/0.98  inst_num_of_dismatching_blockings:      16
% 2.09/0.98  inst_num_of_non_proper_insts:           38
% 2.09/0.98  inst_num_of_duplicates:                 0
% 2.09/0.98  inst_inst_num_from_inst_to_res:         0
% 2.09/0.98  inst_dismatching_checking_time:         0.
% 2.09/0.98  
% 2.09/0.98  ------ Resolution
% 2.09/0.98  
% 2.09/0.98  res_num_of_clauses:                     0
% 2.09/0.98  res_num_in_passive:                     0
% 2.09/0.98  res_num_in_active:                      0
% 2.09/0.98  res_num_of_loops:                       79
% 2.09/0.98  res_forward_subset_subsumed:            5
% 2.09/0.98  res_backward_subset_subsumed:           0
% 2.09/0.98  res_forward_subsumed:                   0
% 2.09/0.98  res_backward_subsumed:                  1
% 2.09/0.98  res_forward_subsumption_resolution:     1
% 2.09/0.98  res_backward_subsumption_resolution:    0
% 2.09/0.98  res_clause_to_clause_subsumption:       25
% 2.09/0.98  res_orphan_elimination:                 0
% 2.09/0.98  res_tautology_del:                      5
% 2.09/0.98  res_num_eq_res_simplified:              1
% 2.09/0.98  res_num_sel_changes:                    0
% 2.09/0.98  res_moves_from_active_to_pass:          0
% 2.09/0.98  
% 2.09/0.98  ------ Superposition
% 2.09/0.98  
% 2.09/0.98  sup_time_total:                         0.
% 2.09/0.98  sup_time_generating:                    0.
% 2.09/0.98  sup_time_sim_full:                      0.
% 2.09/0.98  sup_time_sim_immed:                     0.
% 2.09/0.98  
% 2.09/0.98  sup_num_of_clauses:                     12
% 2.09/0.98  sup_num_in_active:                      8
% 2.09/0.98  sup_num_in_passive:                     4
% 2.09/0.98  sup_num_of_loops:                       8
% 2.09/0.98  sup_fw_superposition:                   2
% 2.09/0.98  sup_bw_superposition:                   0
% 2.09/0.98  sup_immediate_simplified:               2
% 2.09/0.98  sup_given_eliminated:                   0
% 2.09/0.98  comparisons_done:                       0
% 2.09/0.98  comparisons_avoided:                    0
% 2.09/0.98  
% 2.09/0.98  ------ Simplifications
% 2.09/0.98  
% 2.09/0.98  
% 2.09/0.98  sim_fw_subset_subsumed:                 1
% 2.09/0.98  sim_bw_subset_subsumed:                 0
% 2.09/0.98  sim_fw_subsumed:                        0
% 2.09/0.98  sim_bw_subsumed:                        0
% 2.09/0.98  sim_fw_subsumption_res:                 1
% 2.09/0.98  sim_bw_subsumption_res:                 0
% 2.09/0.98  sim_tautology_del:                      0
% 2.09/0.98  sim_eq_tautology_del:                   0
% 2.09/0.98  sim_eq_res_simp:                        0
% 2.09/0.98  sim_fw_demodulated:                     1
% 2.09/0.98  sim_bw_demodulated:                     0
% 2.09/0.98  sim_light_normalised:                   1
% 2.09/0.98  sim_joinable_taut:                      0
% 2.09/0.98  sim_joinable_simp:                      0
% 2.09/0.98  sim_ac_normalised:                      0
% 2.09/0.98  sim_smt_subsumption:                    0
% 2.09/0.98  
%------------------------------------------------------------------------------
