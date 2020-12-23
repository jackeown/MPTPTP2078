%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1893+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:49 EST 2020

% Result     : Theorem 0.79s
% Output     : CNFRefutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 313 expanded)
%              Number of clauses        :   49 (  72 expanded)
%              Number of leaves         :   11 (  85 expanded)
%              Depth                    :   18
%              Number of atoms          :  428 (2302 expanded)
%              Number of equality atoms :   52 (  55 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
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

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v3_tex_2(X1,X0)
          & ( v4_pre_topc(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v1_subset_1(sK3,u1_struct_0(X0))
        & v3_tex_2(sK3,X0)
        & ( v4_pre_topc(sK3,X0)
          | v3_pre_topc(sK3,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
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
          ( v1_subset_1(X1,u1_struct_0(sK2))
          & v3_tex_2(X1,sK2)
          & ( v4_pre_topc(X1,sK2)
            | v3_pre_topc(X1,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v3_tdlat_3(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( v1_subset_1(sK3,u1_struct_0(sK2))
    & v3_tex_2(sK3,sK2)
    & ( v4_pre_topc(sK3,sK2)
      | v3_pre_topc(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v3_tdlat_3(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f32,f31])).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK1(X0),X0)
        & v4_pre_topc(sK1(X0),X0)
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK1(X0),X0)
            & v4_pre_topc(sK1(X0),X0)
            & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).

fof(f42,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f50,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
             => v4_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f23,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v4_pre_topc(X1,X0)
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v4_pre_topc(X1,X0)
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v4_pre_topc(X2,X0)
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK0(X0),X0)
        & v3_pre_topc(sK0(X0),X0)
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ( ~ v4_pre_topc(sK0(X0),X0)
            & v3_pre_topc(sK0(X0),X0)
            & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v4_pre_topc(X2,X0)
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f38,plain,(
    ! [X2,X0] :
      ( v4_pre_topc(X2,X0)
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f54,plain,
    ( v4_pre_topc(sK3,sK2)
    | v3_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
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

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f55,plain,(
    v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
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

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f57,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f56,plain,(
    v1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_11,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_312,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_313,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ v4_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_tdlat_3(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_312])).

cnf(c_20,negated_conjecture,
    ( v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_317,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ v4_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_313,c_20,c_19])).

cnf(c_426,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ v4_pre_topc(X0,sK2)
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_317])).

cnf(c_427,plain,
    ( v3_pre_topc(sK3,sK2)
    | ~ v4_pre_topc(sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_426])).

cnf(c_7,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_333,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_21])).

cnf(c_334,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | v4_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_tdlat_3(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_333])).

cnf(c_338,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | v4_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_334,c_20,c_19])).

cnf(c_414,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | v4_pre_topc(X0,sK2)
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_338])).

cnf(c_415,plain,
    ( ~ v3_pre_topc(sK3,sK2)
    | v4_pre_topc(sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_17,negated_conjecture,
    ( v3_pre_topc(sK3,sK2)
    | v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_417,plain,
    ( v4_pre_topc(sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_415,c_17])).

cnf(c_429,plain,
    ( v3_pre_topc(sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_427,c_17,c_415])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tops_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_12,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tops_1(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_16,negated_conjecture,
    ( v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_256,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tops_1(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_16])).

cnf(c_257,plain,
    ( ~ v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_tops_1(sK3,sK2)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_256])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_259,plain,
    ( v1_tops_1(sK3,sK2)
    | ~ v3_pre_topc(sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_257,c_22,c_21,c_19,c_18])).

cnf(c_260,plain,
    ( ~ v3_pre_topc(sK3,sK2)
    | v1_tops_1(sK3,sK2) ),
    inference(renaming,[status(thm)],[c_259])).

cnf(c_274,plain,
    ( ~ v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1)
    | sK2 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_260])).

cnf(c_275,plain,
    ( ~ v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | k2_pre_topc(sK2,sK3) = u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_274])).

cnf(c_277,plain,
    ( ~ v3_pre_topc(sK3,sK2)
    | k2_pre_topc(sK2,sK3) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_275,c_19,c_18])).

cnf(c_445,plain,
    ( k2_pre_topc(sK2,sK3) = u1_struct_0(sK2) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_429,c_277])).

cnf(c_453,plain,
    ( k2_pre_topc(sK2,sK3) = u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_445])).

cnf(c_14,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_378,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_19])).

cnf(c_379,plain,
    ( ~ v4_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_pre_topc(sK2,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_378])).

cnf(c_404,plain,
    ( ~ v4_pre_topc(X0,sK2)
    | k2_pre_topc(sK2,X0) = X0
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_379])).

cnf(c_405,plain,
    ( ~ v4_pre_topc(sK3,sK2)
    | k2_pre_topc(sK2,sK3) = sK3 ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_424,plain,
    ( k2_pre_topc(sK2,sK3) = sK3 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_417,c_405])).

cnf(c_454,plain,
    ( k2_pre_topc(sK2,sK3) = sK3 ),
    inference(subtyping,[status(esa)],[c_424])).

cnf(c_460,plain,
    ( u1_struct_0(sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_453,c_454])).

cnf(c_3,plain,
    ( ~ v1_subset_1(X0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_15,negated_conjecture,
    ( v1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_243,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
    | u1_struct_0(sK2) != X0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_15])).

cnf(c_244,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | sK3 != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_243])).

cnf(c_397,plain,
    ( k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
    | u1_struct_0(sK2) != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_244])).

cnf(c_447,plain,
    ( u1_struct_0(sK2) != sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_397])).

cnf(c_452,plain,
    ( u1_struct_0(sK2) != sK3 ),
    inference(subtyping,[status(esa)],[c_447])).

cnf(c_461,plain,
    ( sK3 != sK3 ),
    inference(demodulation,[status(thm)],[c_460,c_452])).

cnf(c_462,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_461])).


%------------------------------------------------------------------------------
