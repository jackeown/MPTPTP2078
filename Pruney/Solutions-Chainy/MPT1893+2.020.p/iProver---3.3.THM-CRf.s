%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:41 EST 2020

% Result     : Theorem 3.91s
% Output     : CNFRefutation 3.91s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_4059)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f66,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v3_tex_2(X1,X0)
          & ( v4_pre_topc(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v1_subset_1(sK9,u1_struct_0(X0))
        & v3_tex_2(sK9,X0)
        & ( v4_pre_topc(sK9,X0)
          | v3_pre_topc(sK9,X0) )
        & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,
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
          ( v1_subset_1(X1,u1_struct_0(sK8))
          & v3_tex_2(X1,sK8)
          & ( v4_pre_topc(X1,sK8)
            | v3_pre_topc(X1,sK8) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) )
      & l1_pre_topc(sK8)
      & v3_tdlat_3(sK8)
      & v2_pre_topc(sK8)
      & ~ v2_struct_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,
    ( v1_subset_1(sK9,u1_struct_0(sK8))
    & v3_tex_2(sK9,sK8)
    & ( v4_pre_topc(sK9,sK8)
      | v3_pre_topc(sK9,sK8) )
    & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    & l1_pre_topc(sK8)
    & v3_tdlat_3(sK8)
    & v2_pre_topc(sK8)
    & ~ v2_struct_0(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f36,f66,f65])).

fof(f111,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(cnf_transformation,[],[f67])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

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
    inference(flattening,[],[f16])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
             => v4_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f53,plain,(
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
    inference(rectify,[],[f52])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK5(X0),X0)
        & v3_pre_topc(sK5(X0),X0)
        & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ( ~ v4_pre_topc(sK5(X0),X0)
            & v3_pre_topc(sK5(X0),X0)
            & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v4_pre_topc(X2,X0)
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f53,f54])).

fof(f92,plain,(
    ! [X2,X0] :
      ( v4_pre_topc(X2,X0)
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f108,plain,(
    v2_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f67])).

fof(f109,plain,(
    v3_tdlat_3(sK8) ),
    inference(cnf_transformation,[],[f67])).

fof(f110,plain,(
    l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f67])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

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

fof(f104,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f74,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f107,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f67])).

fof(f113,plain,(
    v3_tex_2(sK9,sK8) ),
    inference(cnf_transformation,[],[f67])).

fof(f112,plain,
    ( v4_pre_topc(sK9,sK8)
    | v3_pre_topc(sK9,sK8) ),
    inference(cnf_transformation,[],[f67])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f57,plain,(
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
    inference(rectify,[],[f56])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK6(X0),X0)
        & v4_pre_topc(sK6(X0),X0)
        & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK6(X0),X0)
            & v4_pre_topc(sK6(X0),X0)
            & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f57,f58])).

fof(f96,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k1_tarski(X2) = X1
                 => v3_pre_topc(X1,X0) ) ) )
       => v1_tdlat_3(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(X1,X0)
              & k1_tarski(X2) = X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(X1,X0)
              & k1_tarski(X2) = X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X1,X0)
          & k1_tarski(X2) = X1
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ v3_pre_topc(X1,X0)
        & k1_tarski(sK4(X0)) = X1
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(X1,X0)
              & k1_tarski(X2) = X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ v3_pre_topc(sK3(X0),X0)
            & k1_tarski(X2) = sK3(X0)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | ( ~ v3_pre_topc(sK3(X0),X0)
        & k1_tarski(sK4(X0)) = sK3(X0)
        & m1_subset_1(sK4(X0),u1_struct_0(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f24,f50,f49])).

fof(f88,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f13,axiom,(
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

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | v1_subset_1(X1,u1_struct_0(X0)) )
            & ( ~ v1_subset_1(X1,u1_struct_0(X0))
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,u1_struct_0(X0))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f114,plain,(
    v1_subset_1(sK9,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f67])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v3_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
                      & v3_pre_topc(X5,X0)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f39])).

fof(f42,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v3_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4
        & v3_pre_topc(sK1(X0,X1,X4),X0)
        & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1)
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK0(X0,X1),X1)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4
                    & v3_pre_topc(sK1(X0,X1,X4),X0)
                    & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).

fof(f76,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f77,plain,(
    ! [X4,X0,X1] :
      ( v3_pre_topc(sK1(X0,X1,X4),X0)
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK2(X0,X1) != X1
        & r1_tarski(X1,sK2(X0,X1))
        & v2_tex_2(sK2(X0,X1),X0)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK2(X0,X1) != X1
                & r1_tarski(X1,sK2(X0,X1))
                & v2_tex_2(sK2(X0,X1),X0)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f46,f47])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
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

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f60,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f61,plain,(
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
    inference(rectify,[],[f60])).

fof(f62,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK7(X0,X1))) != sK7(X0,X1)
        & r1_tarski(sK7(X0,X1),X1)
        & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK7(X0,X1))) != sK7(X0,X1)
                & r1_tarski(sK7(X0,X1),X1)
                & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f61,f62])).

fof(f100,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
      | ~ r1_tarski(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f78,plain,(
    ! [X4,X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f91,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | ~ v3_pre_topc(sK3(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_3836,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_5,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_27,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_45,negated_conjecture,
    ( v2_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_889,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_45])).

cnf(c_890,plain,
    ( ~ v3_pre_topc(X0,sK8)
    | v4_pre_topc(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ v3_tdlat_3(sK8)
    | ~ l1_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_889])).

cnf(c_44,negated_conjecture,
    ( v3_tdlat_3(sK8) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_43,negated_conjecture,
    ( l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_894,plain,
    ( ~ v3_pre_topc(X0,sK8)
    | v4_pre_topc(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_890,c_44,c_43])).

cnf(c_974,plain,
    ( ~ v3_pre_topc(X0,sK8)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ l1_pre_topc(X2)
    | X0 != X1
    | k2_pre_topc(X2,X1) = X1
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_894])).

cnf(c_975,plain,
    ( ~ v3_pre_topc(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ l1_pre_topc(sK8)
    | k2_pre_topc(sK8,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_974])).

cnf(c_979,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ v3_pre_topc(X0,sK8)
    | k2_pre_topc(sK8,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_975,c_43])).

cnf(c_980,plain,
    ( ~ v3_pre_topc(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | k2_pre_topc(sK8,X0) = X0 ),
    inference(renaming,[status(thm)],[c_979])).

cnf(c_3826,plain,
    ( k2_pre_topc(sK8,X0) = X0
    | v3_pre_topc(X0,sK8) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_980])).

cnf(c_5923,plain,
    ( k2_pre_topc(sK8,sK9) = sK9
    | v3_pre_topc(sK9,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_3836,c_3826])).

cnf(c_36,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ v3_pre_topc(X0,X1)
    | v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_7,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_583,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
    inference(resolution,[status(thm)],[c_36,c_7])).

cnf(c_46,negated_conjecture,
    ( ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_668,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_583,c_46])).

cnf(c_669,plain,
    ( ~ v3_tex_2(X0,sK8)
    | ~ v3_pre_topc(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ l1_pre_topc(sK8)
    | ~ v2_pre_topc(sK8)
    | k2_pre_topc(sK8,X0) = u1_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_668])).

cnf(c_673,plain,
    ( ~ v3_tex_2(X0,sK8)
    | ~ v3_pre_topc(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | k2_pre_topc(sK8,X0) = u1_struct_0(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_669,c_45,c_43])).

cnf(c_3835,plain,
    ( k2_pre_topc(sK8,X0) = u1_struct_0(sK8)
    | v3_tex_2(X0,sK8) != iProver_top
    | v3_pre_topc(X0,sK8) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_673])).

cnf(c_4390,plain,
    ( k2_pre_topc(sK8,sK9) = u1_struct_0(sK8)
    | v3_tex_2(sK9,sK8) != iProver_top
    | v3_pre_topc(sK9,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_3836,c_3835])).

cnf(c_40,negated_conjecture,
    ( v3_tex_2(sK9,sK8) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_41,negated_conjecture,
    ( v3_pre_topc(sK9,sK8)
    | v4_pre_topc(sK9,sK8) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_31,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_868,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_45])).

cnf(c_869,plain,
    ( v3_pre_topc(X0,sK8)
    | ~ v4_pre_topc(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ v3_tdlat_3(sK8)
    | ~ l1_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_868])).

cnf(c_873,plain,
    ( v3_pre_topc(X0,sK8)
    | ~ v4_pre_topc(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_869,c_44,c_43])).

cnf(c_995,plain,
    ( v3_pre_topc(X0,sK8)
    | v3_pre_topc(sK9,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | sK8 != sK8
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_41,c_873])).

cnf(c_996,plain,
    ( v3_pre_topc(sK9,sK8)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(unflattening,[status(thm)],[c_995])).

cnf(c_998,plain,
    ( v3_pre_topc(sK9,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_996,c_42])).

cnf(c_1378,plain,
    ( ~ v3_tex_2(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | k2_pre_topc(sK8,X0) = u1_struct_0(sK8)
    | sK8 != sK8
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_998,c_673])).

cnf(c_1379,plain,
    ( ~ v3_tex_2(sK9,sK8)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | k2_pre_topc(sK8,sK9) = u1_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_1378])).

cnf(c_4398,plain,
    ( k2_pre_topc(sK8,sK9) = u1_struct_0(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4390,c_42,c_40,c_1379])).

cnf(c_5930,plain,
    ( u1_struct_0(sK8) = sK9
    | v3_pre_topc(sK9,sK8) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5923,c_4398])).

cnf(c_51,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_997,plain,
    ( v3_pre_topc(sK9,sK8) = iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_996])).

cnf(c_6075,plain,
    ( u1_struct_0(sK8) = sK9 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5930,c_51,c_997])).

cnf(c_23,plain,
    ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v1_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_38,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(X1))
    | ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_39,negated_conjecture,
    ( v1_subset_1(sK9,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_619,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK8)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_39])).

cnf(c_620,plain,
    ( ~ v3_tex_2(sK9,X0)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v1_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_619])).

cnf(c_654,plain,
    ( ~ v3_tex_2(sK9,X0)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK8)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_620,c_46])).

cnf(c_655,plain,
    ( ~ v3_tex_2(sK9,sK8)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ v1_tdlat_3(sK8)
    | ~ l1_pre_topc(sK8)
    | ~ v2_pre_topc(sK8)
    | u1_struct_0(sK8) != u1_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_654])).

cnf(c_622,plain,
    ( ~ v3_tex_2(sK9,sK8)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | v2_struct_0(sK8)
    | ~ v1_tdlat_3(sK8)
    | ~ l1_pre_topc(sK8)
    | ~ v2_pre_topc(sK8)
    | u1_struct_0(sK8) != u1_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_620])).

cnf(c_657,plain,
    ( ~ v1_tdlat_3(sK8)
    | u1_struct_0(sK8) != u1_struct_0(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_655,c_46,c_45,c_43,c_42,c_40,c_622])).

cnf(c_808,plain,
    ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(sK8) != u1_struct_0(sK8)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_657])).

cnf(c_809,plain,
    ( m1_subset_1(sK3(sK8),k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ l1_pre_topc(sK8)
    | ~ v2_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_808])).

cnf(c_811,plain,
    ( m1_subset_1(sK3(sK8),k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_809,c_45,c_43])).

cnf(c_3830,plain,
    ( m1_subset_1(sK3(sK8),k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_811])).

cnf(c_6084,plain,
    ( m1_subset_1(sK3(sK8),k1_zfmisc_1(sK9)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6075,c_3830])).

cnf(c_1,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3840,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3841,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3840,c_0])).

cnf(c_13,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1148,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_43])).

cnf(c_1149,plain,
    ( ~ v2_tex_2(X0,sK8)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
    | m1_subset_1(sK1(sK8,X0,X1),k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(unflattening,[status(thm)],[c_1148])).

cnf(c_3817,plain,
    ( v2_tex_2(X0,sK8) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_subset_1(sK1(sK8,X0,X1),k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1149])).

cnf(c_6098,plain,
    ( v2_tex_2(X0,sK8) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK9)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(sK9)) != iProver_top
    | m1_subset_1(sK1(sK8,X0,X1),k1_zfmisc_1(sK9)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6075,c_3817])).

cnf(c_5927,plain,
    ( k2_pre_topc(sK8,sK1(sK8,X0,X1)) = sK1(sK8,X0,X1)
    | v3_pre_topc(sK1(sK8,X0,X1),sK8) != iProver_top
    | v2_tex_2(X0,sK8) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3817,c_3826])).

cnf(c_12,plain,
    ( v3_pre_topc(sK1(X0,X1,X2),X0)
    | ~ v2_tex_2(X1,X0)
    | ~ r1_tarski(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1016,plain,
    ( v3_pre_topc(sK1(X0,X1,X2),X0)
    | ~ v2_tex_2(X1,X0)
    | ~ r1_tarski(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_43])).

cnf(c_1017,plain,
    ( v3_pre_topc(sK1(sK8,X0,X1),sK8)
    | ~ v2_tex_2(X0,sK8)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(unflattening,[status(thm)],[c_1016])).

cnf(c_1445,plain,
    ( ~ v2_tex_2(X0,sK8)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | sK1(sK8,X0,X1) != X2
    | k2_pre_topc(sK8,X2) = X2
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_980,c_1017])).

cnf(c_1446,plain,
    ( ~ v2_tex_2(X0,sK8)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(sK1(sK8,X0,X1),k1_zfmisc_1(u1_struct_0(sK8)))
    | k2_pre_topc(sK8,sK1(sK8,X0,X1)) = sK1(sK8,X0,X1) ),
    inference(unflattening,[status(thm)],[c_1445])).

cnf(c_1450,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ r1_tarski(X1,X0)
    | ~ v2_tex_2(X0,sK8)
    | k2_pre_topc(sK8,sK1(sK8,X0,X1)) = sK1(sK8,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1446,c_1149])).

cnf(c_1451,plain,
    ( ~ v2_tex_2(X0,sK8)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
    | k2_pre_topc(sK8,sK1(sK8,X0,X1)) = sK1(sK8,X0,X1) ),
    inference(renaming,[status(thm)],[c_1450])).

cnf(c_1452,plain,
    ( k2_pre_topc(sK8,sK1(sK8,X0,X1)) = sK1(sK8,X0,X1)
    | v2_tex_2(X0,sK8) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1451])).

cnf(c_8270,plain,
    ( k2_pre_topc(sK8,sK1(sK8,X0,X1)) = sK1(sK8,X0,X1)
    | v2_tex_2(X0,sK8) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5927,c_1452])).

cnf(c_8274,plain,
    ( k2_pre_topc(sK8,sK1(sK8,X0,X1)) = sK1(sK8,X0,X1)
    | v2_tex_2(X0,sK8) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK9)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(sK9)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8270,c_6075])).

cnf(c_8279,plain,
    ( k2_pre_topc(sK8,sK1(sK8,sK9,X0)) = sK1(sK8,sK9,X0)
    | v2_tex_2(sK9,sK8) != iProver_top
    | r1_tarski(X0,sK9) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3841,c_8274])).

cnf(c_19,plain,
    ( ~ v3_tex_2(X0,X1)
    | v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1037,plain,
    ( ~ v3_tex_2(X0,X1)
    | v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_43])).

cnf(c_1038,plain,
    ( ~ v3_tex_2(X0,sK8)
    | v2_tex_2(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(unflattening,[status(thm)],[c_1037])).

cnf(c_1755,plain,
    ( v2_tex_2(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | sK8 != sK8
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_40,c_1038])).

cnf(c_1756,plain,
    ( v2_tex_2(sK9,sK8)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(unflattening,[status(thm)],[c_1755])).

cnf(c_1757,plain,
    ( v2_tex_2(sK9,sK8) = iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1756])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_4415,plain,
    ( r1_tarski(X0,sK9)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK9)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4416,plain,
    ( r1_tarski(X0,sK9) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4415])).

cnf(c_8422,plain,
    ( k2_pre_topc(sK8,sK1(sK8,sK9,X0)) = sK1(sK8,sK9,X0)
    | m1_subset_1(X0,k1_zfmisc_1(sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8279,c_51,c_1757,c_4416])).

cnf(c_8430,plain,
    ( k2_pre_topc(sK8,sK1(sK8,sK9,sK1(sK8,X0,X1))) = sK1(sK8,sK9,sK1(sK8,X0,X1))
    | v2_tex_2(X0,sK8) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK9)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6098,c_8422])).

cnf(c_13191,plain,
    ( k2_pre_topc(sK8,sK1(sK8,sK9,sK1(sK8,sK9,X0))) = sK1(sK8,sK9,sK1(sK8,sK9,X0))
    | v2_tex_2(sK9,sK8) != iProver_top
    | r1_tarski(X0,sK9) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3841,c_8430])).

cnf(c_14096,plain,
    ( k2_pre_topc(sK8,sK1(sK8,sK9,sK1(sK8,sK9,X0))) = sK1(sK8,sK9,sK1(sK8,sK9,X0))
    | m1_subset_1(X0,k1_zfmisc_1(sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13191,c_51,c_1757,c_4416])).

cnf(c_14104,plain,
    ( k2_pre_topc(sK8,sK1(sK8,sK9,sK1(sK8,sK9,sK3(sK8)))) = sK1(sK8,sK9,sK1(sK8,sK9,sK3(sK8))) ),
    inference(superposition,[status(thm)],[c_6084,c_14096])).

cnf(c_35,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_692,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_46])).

cnf(c_693,plain,
    ( ~ v2_tex_2(X0,sK8)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ l1_pre_topc(sK8)
    | ~ v2_pre_topc(sK8)
    | k9_subset_1(u1_struct_0(sK8),X0,k2_pre_topc(sK8,X1)) = X1 ),
    inference(unflattening,[status(thm)],[c_692])).

cnf(c_697,plain,
    ( ~ v2_tex_2(X0,sK8)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
    | k9_subset_1(u1_struct_0(sK8),X0,k2_pre_topc(sK8,X1)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_693,c_45,c_43])).

cnf(c_3834,plain,
    ( k9_subset_1(u1_struct_0(sK8),X0,k2_pre_topc(sK8,X1)) = X1
    | v2_tex_2(X0,sK8) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_697])).

cnf(c_4434,plain,
    ( k9_subset_1(u1_struct_0(sK8),sK9,k2_pre_topc(sK8,X0)) = X0
    | v2_tex_2(sK9,sK8) != iProver_top
    | r1_tarski(X0,sK9) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3836,c_3834])).

cnf(c_4567,plain,
    ( k9_subset_1(u1_struct_0(sK8),sK9,k2_pre_topc(sK8,X0)) = X0
    | r1_tarski(X0,sK9) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4434,c_51,c_1757,c_4059])).

cnf(c_6104,plain,
    ( k9_subset_1(sK9,sK9,k2_pre_topc(sK8,X0)) = X0
    | r1_tarski(X0,sK9) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK9)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6075,c_4567])).

cnf(c_6484,plain,
    ( k9_subset_1(sK9,sK9,k2_pre_topc(sK8,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6104,c_4416])).

cnf(c_7790,plain,
    ( k9_subset_1(sK9,sK9,k2_pre_topc(sK8,sK1(sK8,X0,X1))) = sK1(sK8,X0,X1)
    | v2_tex_2(X0,sK8) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK9)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6098,c_6484])).

cnf(c_13014,plain,
    ( k9_subset_1(sK9,sK9,k2_pre_topc(sK8,sK1(sK8,sK9,X0))) = sK1(sK8,sK9,X0)
    | v2_tex_2(sK9,sK8) != iProver_top
    | r1_tarski(X0,sK9) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3841,c_7790])).

cnf(c_13358,plain,
    ( k9_subset_1(sK9,sK9,k2_pre_topc(sK8,sK1(sK8,sK9,X0))) = sK1(sK8,sK9,X0)
    | m1_subset_1(X0,k1_zfmisc_1(sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13014,c_51,c_1757,c_4416])).

cnf(c_13366,plain,
    ( k9_subset_1(sK9,sK9,k2_pre_topc(sK8,sK1(sK8,sK9,sK3(sK8)))) = sK1(sK8,sK9,sK3(sK8)) ),
    inference(superposition,[status(thm)],[c_6084,c_13358])).

cnf(c_11,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,sK1(X1,X0,X2)) = X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1169,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | k9_subset_1(u1_struct_0(X1),X0,sK1(X1,X0,X2)) = X2
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_43])).

cnf(c_1170,plain,
    ( ~ v2_tex_2(X0,sK8)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
    | k9_subset_1(u1_struct_0(sK8),X0,sK1(sK8,X0,X1)) = X1 ),
    inference(unflattening,[status(thm)],[c_1169])).

cnf(c_3816,plain,
    ( k9_subset_1(u1_struct_0(sK8),X0,sK1(sK8,X0,X1)) = X1
    | v2_tex_2(X0,sK8) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1170])).

cnf(c_4584,plain,
    ( k9_subset_1(u1_struct_0(sK8),sK9,sK1(sK8,sK9,X0)) = X0
    | v2_tex_2(sK9,sK8) != iProver_top
    | r1_tarski(X0,sK9) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3836,c_3816])).

cnf(c_4650,plain,
    ( k9_subset_1(u1_struct_0(sK8),sK9,sK1(sK8,sK9,X0)) = X0
    | r1_tarski(X0,sK9) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4584,c_51,c_1757,c_4063])).

cnf(c_5606,plain,
    ( k9_subset_1(u1_struct_0(sK8),sK9,sK1(sK8,sK9,sK3(sK8))) = sK3(sK8)
    | r1_tarski(sK3(sK8),sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_3830,c_4650])).

cnf(c_3838,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5599,plain,
    ( r1_tarski(sK3(sK8),u1_struct_0(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3830,c_3838])).

cnf(c_6080,plain,
    ( r1_tarski(sK3(sK8),sK9) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6075,c_5599])).

cnf(c_6265,plain,
    ( k9_subset_1(u1_struct_0(sK8),sK9,sK1(sK8,sK9,sK3(sK8))) = sK3(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5606,c_6080])).

cnf(c_6267,plain,
    ( k9_subset_1(sK9,sK9,sK1(sK8,sK9,sK3(sK8))) = sK3(sK8) ),
    inference(light_normalisation,[status(thm)],[c_6265,c_6075])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3839,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_8428,plain,
    ( k2_pre_topc(sK8,sK1(sK8,sK9,X0)) = sK1(sK8,sK9,X0)
    | r1_tarski(X0,sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_3839,c_8422])).

cnf(c_9623,plain,
    ( k2_pre_topc(sK8,sK1(sK8,sK9,sK3(sK8))) = sK1(sK8,sK9,sK3(sK8)) ),
    inference(superposition,[status(thm)],[c_6080,c_8428])).

cnf(c_13371,plain,
    ( sK1(sK8,sK9,sK3(sK8)) = sK3(sK8) ),
    inference(light_normalisation,[status(thm)],[c_13366,c_6267,c_9623])).

cnf(c_14109,plain,
    ( k2_pre_topc(sK8,sK3(sK8)) = sK3(sK8) ),
    inference(light_normalisation,[status(thm)],[c_14104,c_13371])).

cnf(c_20,plain,
    ( ~ v3_pre_topc(sK3(X0),X0)
    | v1_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_838,plain,
    ( ~ v3_pre_topc(sK3(X0),X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(sK8) != u1_struct_0(sK8)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_657])).

cnf(c_839,plain,
    ( ~ v3_pre_topc(sK3(sK8),sK8)
    | ~ l1_pre_topc(sK8)
    | ~ v2_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_838])).

cnf(c_841,plain,
    ( ~ v3_pre_topc(sK3(sK8),sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_839,c_45,c_43])).

cnf(c_4,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_910,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_45])).

cnf(c_911,plain,
    ( v4_pre_topc(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ l1_pre_topc(sK8)
    | k2_pre_topc(sK8,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_910])).

cnf(c_915,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | v4_pre_topc(X0,sK8)
    | k2_pre_topc(sK8,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_911,c_43])).

cnf(c_916,plain,
    ( v4_pre_topc(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | k2_pre_topc(sK8,X0) != X0 ),
    inference(renaming,[status(thm)],[c_915])).

cnf(c_943,plain,
    ( v3_pre_topc(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | k2_pre_topc(sK8,X0) != X0 ),
    inference(resolution,[status(thm)],[c_916,c_873])).

cnf(c_1386,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | k2_pre_topc(sK8,X0) != X0
    | sK3(sK8) != X0
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_841,c_943])).

cnf(c_1387,plain,
    ( ~ m1_subset_1(sK3(sK8),k1_zfmisc_1(u1_struct_0(sK8)))
    | k2_pre_topc(sK8,sK3(sK8)) != sK3(sK8) ),
    inference(unflattening,[status(thm)],[c_1386])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14109,c_1387,c_809,c_43,c_45])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:56:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.91/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.00  
% 3.91/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.91/1.00  
% 3.91/1.00  ------  iProver source info
% 3.91/1.00  
% 3.91/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.91/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.91/1.00  git: non_committed_changes: false
% 3.91/1.00  git: last_make_outside_of_git: false
% 3.91/1.00  
% 3.91/1.00  ------ 
% 3.91/1.00  
% 3.91/1.00  ------ Input Options
% 3.91/1.00  
% 3.91/1.00  --out_options                           all
% 3.91/1.00  --tptp_safe_out                         true
% 3.91/1.00  --problem_path                          ""
% 3.91/1.00  --include_path                          ""
% 3.91/1.00  --clausifier                            res/vclausify_rel
% 3.91/1.00  --clausifier_options                    ""
% 3.91/1.00  --stdin                                 false
% 3.91/1.00  --stats_out                             all
% 3.91/1.00  
% 3.91/1.00  ------ General Options
% 3.91/1.00  
% 3.91/1.00  --fof                                   false
% 3.91/1.00  --time_out_real                         305.
% 3.91/1.00  --time_out_virtual                      -1.
% 3.91/1.00  --symbol_type_check                     false
% 3.91/1.00  --clausify_out                          false
% 3.91/1.00  --sig_cnt_out                           false
% 3.91/1.00  --trig_cnt_out                          false
% 3.91/1.00  --trig_cnt_out_tolerance                1.
% 3.91/1.00  --trig_cnt_out_sk_spl                   false
% 3.91/1.00  --abstr_cl_out                          false
% 3.91/1.00  
% 3.91/1.00  ------ Global Options
% 3.91/1.00  
% 3.91/1.00  --schedule                              default
% 3.91/1.00  --add_important_lit                     false
% 3.91/1.00  --prop_solver_per_cl                    1000
% 3.91/1.00  --min_unsat_core                        false
% 3.91/1.00  --soft_assumptions                      false
% 3.91/1.00  --soft_lemma_size                       3
% 3.91/1.00  --prop_impl_unit_size                   0
% 3.91/1.00  --prop_impl_unit                        []
% 3.91/1.00  --share_sel_clauses                     true
% 3.91/1.00  --reset_solvers                         false
% 3.91/1.00  --bc_imp_inh                            [conj_cone]
% 3.91/1.00  --conj_cone_tolerance                   3.
% 3.91/1.00  --extra_neg_conj                        none
% 3.91/1.00  --large_theory_mode                     true
% 3.91/1.00  --prolific_symb_bound                   200
% 3.91/1.00  --lt_threshold                          2000
% 3.91/1.00  --clause_weak_htbl                      true
% 3.91/1.00  --gc_record_bc_elim                     false
% 3.91/1.00  
% 3.91/1.00  ------ Preprocessing Options
% 3.91/1.00  
% 3.91/1.00  --preprocessing_flag                    true
% 3.91/1.00  --time_out_prep_mult                    0.1
% 3.91/1.00  --splitting_mode                        input
% 3.91/1.00  --splitting_grd                         true
% 3.91/1.00  --splitting_cvd                         false
% 3.91/1.00  --splitting_cvd_svl                     false
% 3.91/1.00  --splitting_nvd                         32
% 3.91/1.00  --sub_typing                            true
% 3.91/1.00  --prep_gs_sim                           true
% 3.91/1.00  --prep_unflatten                        true
% 3.91/1.00  --prep_res_sim                          true
% 3.91/1.00  --prep_upred                            true
% 3.91/1.00  --prep_sem_filter                       exhaustive
% 3.91/1.00  --prep_sem_filter_out                   false
% 3.91/1.00  --pred_elim                             true
% 3.91/1.00  --res_sim_input                         true
% 3.91/1.00  --eq_ax_congr_red                       true
% 3.91/1.00  --pure_diseq_elim                       true
% 3.91/1.00  --brand_transform                       false
% 3.91/1.00  --non_eq_to_eq                          false
% 3.91/1.00  --prep_def_merge                        true
% 3.91/1.00  --prep_def_merge_prop_impl              false
% 3.91/1.00  --prep_def_merge_mbd                    true
% 3.91/1.00  --prep_def_merge_tr_red                 false
% 3.91/1.00  --prep_def_merge_tr_cl                  false
% 3.91/1.00  --smt_preprocessing                     true
% 3.91/1.00  --smt_ac_axioms                         fast
% 3.91/1.00  --preprocessed_out                      false
% 3.91/1.00  --preprocessed_stats                    false
% 3.91/1.00  
% 3.91/1.00  ------ Abstraction refinement Options
% 3.91/1.00  
% 3.91/1.00  --abstr_ref                             []
% 3.91/1.00  --abstr_ref_prep                        false
% 3.91/1.00  --abstr_ref_until_sat                   false
% 3.91/1.00  --abstr_ref_sig_restrict                funpre
% 3.91/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.91/1.00  --abstr_ref_under                       []
% 3.91/1.00  
% 3.91/1.00  ------ SAT Options
% 3.91/1.00  
% 3.91/1.00  --sat_mode                              false
% 3.91/1.00  --sat_fm_restart_options                ""
% 3.91/1.00  --sat_gr_def                            false
% 3.91/1.00  --sat_epr_types                         true
% 3.91/1.00  --sat_non_cyclic_types                  false
% 3.91/1.00  --sat_finite_models                     false
% 3.91/1.00  --sat_fm_lemmas                         false
% 3.91/1.00  --sat_fm_prep                           false
% 3.91/1.00  --sat_fm_uc_incr                        true
% 3.91/1.00  --sat_out_model                         small
% 3.91/1.00  --sat_out_clauses                       false
% 3.91/1.00  
% 3.91/1.00  ------ QBF Options
% 3.91/1.00  
% 3.91/1.00  --qbf_mode                              false
% 3.91/1.00  --qbf_elim_univ                         false
% 3.91/1.00  --qbf_dom_inst                          none
% 3.91/1.00  --qbf_dom_pre_inst                      false
% 3.91/1.00  --qbf_sk_in                             false
% 3.91/1.00  --qbf_pred_elim                         true
% 3.91/1.00  --qbf_split                             512
% 3.91/1.00  
% 3.91/1.00  ------ BMC1 Options
% 3.91/1.00  
% 3.91/1.00  --bmc1_incremental                      false
% 3.91/1.00  --bmc1_axioms                           reachable_all
% 3.91/1.00  --bmc1_min_bound                        0
% 3.91/1.00  --bmc1_max_bound                        -1
% 3.91/1.00  --bmc1_max_bound_default                -1
% 3.91/1.00  --bmc1_symbol_reachability              true
% 3.91/1.00  --bmc1_property_lemmas                  false
% 3.91/1.00  --bmc1_k_induction                      false
% 3.91/1.00  --bmc1_non_equiv_states                 false
% 3.91/1.00  --bmc1_deadlock                         false
% 3.91/1.00  --bmc1_ucm                              false
% 3.91/1.00  --bmc1_add_unsat_core                   none
% 3.91/1.00  --bmc1_unsat_core_children              false
% 3.91/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.91/1.00  --bmc1_out_stat                         full
% 3.91/1.00  --bmc1_ground_init                      false
% 3.91/1.00  --bmc1_pre_inst_next_state              false
% 3.91/1.00  --bmc1_pre_inst_state                   false
% 3.91/1.00  --bmc1_pre_inst_reach_state             false
% 3.91/1.00  --bmc1_out_unsat_core                   false
% 3.91/1.00  --bmc1_aig_witness_out                  false
% 3.91/1.00  --bmc1_verbose                          false
% 3.91/1.00  --bmc1_dump_clauses_tptp                false
% 3.91/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.91/1.00  --bmc1_dump_file                        -
% 3.91/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.91/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.91/1.00  --bmc1_ucm_extend_mode                  1
% 3.91/1.00  --bmc1_ucm_init_mode                    2
% 3.91/1.00  --bmc1_ucm_cone_mode                    none
% 3.91/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.91/1.00  --bmc1_ucm_relax_model                  4
% 3.91/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.91/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.91/1.00  --bmc1_ucm_layered_model                none
% 3.91/1.00  --bmc1_ucm_max_lemma_size               10
% 3.91/1.00  
% 3.91/1.00  ------ AIG Options
% 3.91/1.00  
% 3.91/1.00  --aig_mode                              false
% 3.91/1.00  
% 3.91/1.00  ------ Instantiation Options
% 3.91/1.00  
% 3.91/1.00  --instantiation_flag                    true
% 3.91/1.00  --inst_sos_flag                         true
% 3.91/1.00  --inst_sos_phase                        true
% 3.91/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.91/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.91/1.00  --inst_lit_sel_side                     num_symb
% 3.91/1.00  --inst_solver_per_active                1400
% 3.91/1.00  --inst_solver_calls_frac                1.
% 3.91/1.00  --inst_passive_queue_type               priority_queues
% 3.91/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.91/1.00  --inst_passive_queues_freq              [25;2]
% 3.91/1.00  --inst_dismatching                      true
% 3.91/1.00  --inst_eager_unprocessed_to_passive     true
% 3.91/1.00  --inst_prop_sim_given                   true
% 3.91/1.00  --inst_prop_sim_new                     false
% 3.91/1.00  --inst_subs_new                         false
% 3.91/1.00  --inst_eq_res_simp                      false
% 3.91/1.00  --inst_subs_given                       false
% 3.91/1.00  --inst_orphan_elimination               true
% 3.91/1.00  --inst_learning_loop_flag               true
% 3.91/1.00  --inst_learning_start                   3000
% 3.91/1.00  --inst_learning_factor                  2
% 3.91/1.00  --inst_start_prop_sim_after_learn       3
% 3.91/1.00  --inst_sel_renew                        solver
% 3.91/1.00  --inst_lit_activity_flag                true
% 3.91/1.00  --inst_restr_to_given                   false
% 3.91/1.00  --inst_activity_threshold               500
% 3.91/1.00  --inst_out_proof                        true
% 3.91/1.00  
% 3.91/1.00  ------ Resolution Options
% 3.91/1.00  
% 3.91/1.00  --resolution_flag                       true
% 3.91/1.00  --res_lit_sel                           adaptive
% 3.91/1.00  --res_lit_sel_side                      none
% 3.91/1.00  --res_ordering                          kbo
% 3.91/1.00  --res_to_prop_solver                    active
% 3.91/1.00  --res_prop_simpl_new                    false
% 3.91/1.00  --res_prop_simpl_given                  true
% 3.91/1.00  --res_passive_queue_type                priority_queues
% 3.91/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.91/1.00  --res_passive_queues_freq               [15;5]
% 3.91/1.00  --res_forward_subs                      full
% 3.91/1.00  --res_backward_subs                     full
% 3.91/1.00  --res_forward_subs_resolution           true
% 3.91/1.00  --res_backward_subs_resolution          true
% 3.91/1.00  --res_orphan_elimination                true
% 3.91/1.00  --res_time_limit                        2.
% 3.91/1.00  --res_out_proof                         true
% 3.91/1.00  
% 3.91/1.00  ------ Superposition Options
% 3.91/1.00  
% 3.91/1.00  --superposition_flag                    true
% 3.91/1.00  --sup_passive_queue_type                priority_queues
% 3.91/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.91/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.91/1.00  --demod_completeness_check              fast
% 3.91/1.00  --demod_use_ground                      true
% 3.91/1.00  --sup_to_prop_solver                    passive
% 3.91/1.00  --sup_prop_simpl_new                    true
% 3.91/1.00  --sup_prop_simpl_given                  true
% 3.91/1.00  --sup_fun_splitting                     true
% 3.91/1.00  --sup_smt_interval                      50000
% 3.91/1.00  
% 3.91/1.00  ------ Superposition Simplification Setup
% 3.91/1.00  
% 3.91/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.91/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.91/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.91/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.91/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.91/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.91/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.91/1.00  --sup_immed_triv                        [TrivRules]
% 3.91/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.91/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.91/1.00  --sup_immed_bw_main                     []
% 3.91/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.91/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.91/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.91/1.00  --sup_input_bw                          []
% 3.91/1.00  
% 3.91/1.00  ------ Combination Options
% 3.91/1.00  
% 3.91/1.00  --comb_res_mult                         3
% 3.91/1.00  --comb_sup_mult                         2
% 3.91/1.00  --comb_inst_mult                        10
% 3.91/1.00  
% 3.91/1.00  ------ Debug Options
% 3.91/1.00  
% 3.91/1.00  --dbg_backtrace                         false
% 3.91/1.00  --dbg_dump_prop_clauses                 false
% 3.91/1.00  --dbg_dump_prop_clauses_file            -
% 3.91/1.00  --dbg_out_stat                          false
% 3.91/1.00  ------ Parsing...
% 3.91/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.91/1.00  
% 3.91/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 3.91/1.00  
% 3.91/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.91/1.00  
% 3.91/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.91/1.00  ------ Proving...
% 3.91/1.00  ------ Problem Properties 
% 3.91/1.00  
% 3.91/1.00  
% 3.91/1.00  clauses                                 30
% 3.91/1.00  conjectures                             2
% 3.91/1.00  EPR                                     2
% 3.91/1.00  Horn                                    23
% 3.91/1.00  unary                                   9
% 3.91/1.00  binary                                  2
% 3.91/1.00  lits                                    88
% 3.91/1.00  lits eq                                 11
% 3.91/1.00  fd_pure                                 0
% 3.91/1.00  fd_pseudo                               0
% 3.91/1.00  fd_cond                                 0
% 3.91/1.00  fd_pseudo_cond                          1
% 3.91/1.00  AC symbols                              0
% 3.91/1.00  
% 3.91/1.00  ------ Schedule dynamic 5 is on 
% 3.91/1.00  
% 3.91/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.91/1.00  
% 3.91/1.00  
% 3.91/1.00  ------ 
% 3.91/1.00  Current options:
% 3.91/1.00  ------ 
% 3.91/1.00  
% 3.91/1.00  ------ Input Options
% 3.91/1.00  
% 3.91/1.00  --out_options                           all
% 3.91/1.00  --tptp_safe_out                         true
% 3.91/1.00  --problem_path                          ""
% 3.91/1.00  --include_path                          ""
% 3.91/1.00  --clausifier                            res/vclausify_rel
% 3.91/1.00  --clausifier_options                    ""
% 3.91/1.00  --stdin                                 false
% 3.91/1.00  --stats_out                             all
% 3.91/1.00  
% 3.91/1.00  ------ General Options
% 3.91/1.00  
% 3.91/1.00  --fof                                   false
% 3.91/1.00  --time_out_real                         305.
% 3.91/1.00  --time_out_virtual                      -1.
% 3.91/1.00  --symbol_type_check                     false
% 3.91/1.00  --clausify_out                          false
% 3.91/1.00  --sig_cnt_out                           false
% 3.91/1.00  --trig_cnt_out                          false
% 3.91/1.00  --trig_cnt_out_tolerance                1.
% 3.91/1.00  --trig_cnt_out_sk_spl                   false
% 3.91/1.00  --abstr_cl_out                          false
% 3.91/1.00  
% 3.91/1.00  ------ Global Options
% 3.91/1.00  
% 3.91/1.00  --schedule                              default
% 3.91/1.00  --add_important_lit                     false
% 3.91/1.00  --prop_solver_per_cl                    1000
% 3.91/1.00  --min_unsat_core                        false
% 3.91/1.00  --soft_assumptions                      false
% 3.91/1.00  --soft_lemma_size                       3
% 3.91/1.00  --prop_impl_unit_size                   0
% 3.91/1.00  --prop_impl_unit                        []
% 3.91/1.00  --share_sel_clauses                     true
% 3.91/1.00  --reset_solvers                         false
% 3.91/1.00  --bc_imp_inh                            [conj_cone]
% 3.91/1.00  --conj_cone_tolerance                   3.
% 3.91/1.00  --extra_neg_conj                        none
% 3.91/1.00  --large_theory_mode                     true
% 3.91/1.00  --prolific_symb_bound                   200
% 3.91/1.00  --lt_threshold                          2000
% 3.91/1.00  --clause_weak_htbl                      true
% 3.91/1.00  --gc_record_bc_elim                     false
% 3.91/1.00  
% 3.91/1.00  ------ Preprocessing Options
% 3.91/1.00  
% 3.91/1.00  --preprocessing_flag                    true
% 3.91/1.00  --time_out_prep_mult                    0.1
% 3.91/1.00  --splitting_mode                        input
% 3.91/1.00  --splitting_grd                         true
% 3.91/1.00  --splitting_cvd                         false
% 3.91/1.00  --splitting_cvd_svl                     false
% 3.91/1.00  --splitting_nvd                         32
% 3.91/1.00  --sub_typing                            true
% 3.91/1.00  --prep_gs_sim                           true
% 3.91/1.00  --prep_unflatten                        true
% 3.91/1.00  --prep_res_sim                          true
% 3.91/1.00  --prep_upred                            true
% 3.91/1.00  --prep_sem_filter                       exhaustive
% 3.91/1.00  --prep_sem_filter_out                   false
% 3.91/1.00  --pred_elim                             true
% 3.91/1.00  --res_sim_input                         true
% 3.91/1.00  --eq_ax_congr_red                       true
% 3.91/1.00  --pure_diseq_elim                       true
% 3.91/1.00  --brand_transform                       false
% 3.91/1.00  --non_eq_to_eq                          false
% 3.91/1.00  --prep_def_merge                        true
% 3.91/1.00  --prep_def_merge_prop_impl              false
% 3.91/1.00  --prep_def_merge_mbd                    true
% 3.91/1.00  --prep_def_merge_tr_red                 false
% 3.91/1.00  --prep_def_merge_tr_cl                  false
% 3.91/1.00  --smt_preprocessing                     true
% 3.91/1.00  --smt_ac_axioms                         fast
% 3.91/1.00  --preprocessed_out                      false
% 3.91/1.00  --preprocessed_stats                    false
% 3.91/1.00  
% 3.91/1.00  ------ Abstraction refinement Options
% 3.91/1.00  
% 3.91/1.00  --abstr_ref                             []
% 3.91/1.00  --abstr_ref_prep                        false
% 3.91/1.00  --abstr_ref_until_sat                   false
% 3.91/1.00  --abstr_ref_sig_restrict                funpre
% 3.91/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.91/1.00  --abstr_ref_under                       []
% 3.91/1.00  
% 3.91/1.00  ------ SAT Options
% 3.91/1.00  
% 3.91/1.00  --sat_mode                              false
% 3.91/1.00  --sat_fm_restart_options                ""
% 3.91/1.00  --sat_gr_def                            false
% 3.91/1.00  --sat_epr_types                         true
% 3.91/1.00  --sat_non_cyclic_types                  false
% 3.91/1.00  --sat_finite_models                     false
% 3.91/1.00  --sat_fm_lemmas                         false
% 3.91/1.00  --sat_fm_prep                           false
% 3.91/1.00  --sat_fm_uc_incr                        true
% 3.91/1.00  --sat_out_model                         small
% 3.91/1.00  --sat_out_clauses                       false
% 3.91/1.00  
% 3.91/1.00  ------ QBF Options
% 3.91/1.00  
% 3.91/1.00  --qbf_mode                              false
% 3.91/1.00  --qbf_elim_univ                         false
% 3.91/1.00  --qbf_dom_inst                          none
% 3.91/1.00  --qbf_dom_pre_inst                      false
% 3.91/1.00  --qbf_sk_in                             false
% 3.91/1.00  --qbf_pred_elim                         true
% 3.91/1.00  --qbf_split                             512
% 3.91/1.00  
% 3.91/1.00  ------ BMC1 Options
% 3.91/1.00  
% 3.91/1.00  --bmc1_incremental                      false
% 3.91/1.00  --bmc1_axioms                           reachable_all
% 3.91/1.00  --bmc1_min_bound                        0
% 3.91/1.00  --bmc1_max_bound                        -1
% 3.91/1.00  --bmc1_max_bound_default                -1
% 3.91/1.00  --bmc1_symbol_reachability              true
% 3.91/1.00  --bmc1_property_lemmas                  false
% 3.91/1.00  --bmc1_k_induction                      false
% 3.91/1.00  --bmc1_non_equiv_states                 false
% 3.91/1.00  --bmc1_deadlock                         false
% 3.91/1.00  --bmc1_ucm                              false
% 3.91/1.00  --bmc1_add_unsat_core                   none
% 3.91/1.00  --bmc1_unsat_core_children              false
% 3.91/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.91/1.00  --bmc1_out_stat                         full
% 3.91/1.00  --bmc1_ground_init                      false
% 3.91/1.00  --bmc1_pre_inst_next_state              false
% 3.91/1.00  --bmc1_pre_inst_state                   false
% 3.91/1.00  --bmc1_pre_inst_reach_state             false
% 3.91/1.00  --bmc1_out_unsat_core                   false
% 3.91/1.00  --bmc1_aig_witness_out                  false
% 3.91/1.00  --bmc1_verbose                          false
% 3.91/1.00  --bmc1_dump_clauses_tptp                false
% 3.91/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.91/1.00  --bmc1_dump_file                        -
% 3.91/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.91/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.91/1.00  --bmc1_ucm_extend_mode                  1
% 3.91/1.00  --bmc1_ucm_init_mode                    2
% 3.91/1.00  --bmc1_ucm_cone_mode                    none
% 3.91/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.91/1.00  --bmc1_ucm_relax_model                  4
% 3.91/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.91/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.91/1.00  --bmc1_ucm_layered_model                none
% 3.91/1.00  --bmc1_ucm_max_lemma_size               10
% 3.91/1.00  
% 3.91/1.00  ------ AIG Options
% 3.91/1.00  
% 3.91/1.00  --aig_mode                              false
% 3.91/1.00  
% 3.91/1.00  ------ Instantiation Options
% 3.91/1.00  
% 3.91/1.00  --instantiation_flag                    true
% 3.91/1.00  --inst_sos_flag                         true
% 3.91/1.00  --inst_sos_phase                        true
% 3.91/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.91/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.91/1.00  --inst_lit_sel_side                     none
% 3.91/1.00  --inst_solver_per_active                1400
% 3.91/1.00  --inst_solver_calls_frac                1.
% 3.91/1.00  --inst_passive_queue_type               priority_queues
% 3.91/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.91/1.00  --inst_passive_queues_freq              [25;2]
% 3.91/1.00  --inst_dismatching                      true
% 3.91/1.00  --inst_eager_unprocessed_to_passive     true
% 3.91/1.00  --inst_prop_sim_given                   true
% 3.91/1.00  --inst_prop_sim_new                     false
% 3.91/1.00  --inst_subs_new                         false
% 3.91/1.00  --inst_eq_res_simp                      false
% 3.91/1.00  --inst_subs_given                       false
% 3.91/1.00  --inst_orphan_elimination               true
% 3.91/1.00  --inst_learning_loop_flag               true
% 3.91/1.00  --inst_learning_start                   3000
% 3.91/1.00  --inst_learning_factor                  2
% 3.91/1.00  --inst_start_prop_sim_after_learn       3
% 3.91/1.00  --inst_sel_renew                        solver
% 3.91/1.00  --inst_lit_activity_flag                true
% 3.91/1.00  --inst_restr_to_given                   false
% 3.91/1.00  --inst_activity_threshold               500
% 3.91/1.00  --inst_out_proof                        true
% 3.91/1.00  
% 3.91/1.00  ------ Resolution Options
% 3.91/1.00  
% 3.91/1.00  --resolution_flag                       false
% 3.91/1.00  --res_lit_sel                           adaptive
% 3.91/1.00  --res_lit_sel_side                      none
% 3.91/1.00  --res_ordering                          kbo
% 3.91/1.00  --res_to_prop_solver                    active
% 3.91/1.00  --res_prop_simpl_new                    false
% 3.91/1.00  --res_prop_simpl_given                  true
% 3.91/1.00  --res_passive_queue_type                priority_queues
% 3.91/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.91/1.00  --res_passive_queues_freq               [15;5]
% 3.91/1.00  --res_forward_subs                      full
% 3.91/1.00  --res_backward_subs                     full
% 3.91/1.00  --res_forward_subs_resolution           true
% 3.91/1.00  --res_backward_subs_resolution          true
% 3.91/1.00  --res_orphan_elimination                true
% 3.91/1.00  --res_time_limit                        2.
% 3.91/1.00  --res_out_proof                         true
% 3.91/1.00  
% 3.91/1.00  ------ Superposition Options
% 3.91/1.00  
% 3.91/1.00  --superposition_flag                    true
% 3.91/1.00  --sup_passive_queue_type                priority_queues
% 3.91/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.91/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.91/1.00  --demod_completeness_check              fast
% 3.91/1.00  --demod_use_ground                      true
% 3.91/1.00  --sup_to_prop_solver                    passive
% 3.91/1.00  --sup_prop_simpl_new                    true
% 3.91/1.00  --sup_prop_simpl_given                  true
% 3.91/1.00  --sup_fun_splitting                     true
% 3.91/1.00  --sup_smt_interval                      50000
% 3.91/1.00  
% 3.91/1.00  ------ Superposition Simplification Setup
% 3.91/1.00  
% 3.91/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.91/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.91/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.91/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.91/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.91/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.91/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.91/1.00  --sup_immed_triv                        [TrivRules]
% 3.91/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.91/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.91/1.00  --sup_immed_bw_main                     []
% 3.91/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.91/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.91/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.91/1.00  --sup_input_bw                          []
% 3.91/1.00  
% 3.91/1.00  ------ Combination Options
% 3.91/1.00  
% 3.91/1.00  --comb_res_mult                         3
% 3.91/1.00  --comb_sup_mult                         2
% 3.91/1.00  --comb_inst_mult                        10
% 3.91/1.00  
% 3.91/1.00  ------ Debug Options
% 3.91/1.00  
% 3.91/1.00  --dbg_backtrace                         false
% 3.91/1.00  --dbg_dump_prop_clauses                 false
% 3.91/1.00  --dbg_dump_prop_clauses_file            -
% 3.91/1.00  --dbg_out_stat                          false
% 3.91/1.00  
% 3.91/1.00  
% 3.91/1.00  
% 3.91/1.00  
% 3.91/1.00  ------ Proving...
% 3.91/1.00  
% 3.91/1.00  
% 3.91/1.00  % SZS status Theorem for theBenchmark.p
% 3.91/1.00  
% 3.91/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.91/1.00  
% 3.91/1.00  fof(f14,conjecture,(
% 3.91/1.00    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)))))),
% 3.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/1.00  
% 3.91/1.00  fof(f15,negated_conjecture,(
% 3.91/1.00    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)))))),
% 3.91/1.00    inference(negated_conjecture,[],[f14])).
% 3.91/1.00  
% 3.91/1.00  fof(f35,plain,(
% 3.91/1.00    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.91/1.00    inference(ennf_transformation,[],[f15])).
% 3.91/1.00  
% 3.91/1.00  fof(f36,plain,(
% 3.91/1.00    ? [X0] : (? [X1] : (v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.91/1.00    inference(flattening,[],[f35])).
% 3.91/1.00  
% 3.91/1.00  fof(f66,plain,(
% 3.91/1.00    ( ! [X0] : (? [X1] : (v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v1_subset_1(sK9,u1_struct_0(X0)) & v3_tex_2(sK9,X0) & (v4_pre_topc(sK9,X0) | v3_pre_topc(sK9,X0)) & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.91/1.00    introduced(choice_axiom,[])).
% 3.91/1.00  
% 3.91/1.00  fof(f65,plain,(
% 3.91/1.00    ? [X0] : (? [X1] : (v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (v1_subset_1(X1,u1_struct_0(sK8)) & v3_tex_2(X1,sK8) & (v4_pre_topc(X1,sK8) | v3_pre_topc(X1,sK8)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))) & l1_pre_topc(sK8) & v3_tdlat_3(sK8) & v2_pre_topc(sK8) & ~v2_struct_0(sK8))),
% 3.91/1.00    introduced(choice_axiom,[])).
% 3.91/1.00  
% 3.91/1.00  fof(f67,plain,(
% 3.91/1.00    (v1_subset_1(sK9,u1_struct_0(sK8)) & v3_tex_2(sK9,sK8) & (v4_pre_topc(sK9,sK8) | v3_pre_topc(sK9,sK8)) & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))) & l1_pre_topc(sK8) & v3_tdlat_3(sK8) & v2_pre_topc(sK8) & ~v2_struct_0(sK8)),
% 3.91/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f36,f66,f65])).
% 3.91/1.00  
% 3.91/1.00  fof(f111,plain,(
% 3.91/1.00    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))),
% 3.91/1.00    inference(cnf_transformation,[],[f67])).
% 3.91/1.00  
% 3.91/1.00  fof(f4,axiom,(
% 3.91/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/1.00  
% 3.91/1.00  fof(f16,plain,(
% 3.91/1.00    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.91/1.00    inference(ennf_transformation,[],[f4])).
% 3.91/1.00  
% 3.91/1.00  fof(f17,plain,(
% 3.91/1.00    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.91/1.00    inference(flattening,[],[f16])).
% 3.91/1.00  
% 3.91/1.00  fof(f72,plain,(
% 3.91/1.00    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.91/1.00    inference(cnf_transformation,[],[f17])).
% 3.91/1.00  
% 3.91/1.00  fof(f9,axiom,(
% 3.91/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => v4_pre_topc(X1,X0)))))),
% 3.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/1.00  
% 3.91/1.00  fof(f25,plain,(
% 3.91/1.00    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v4_pre_topc(X1,X0) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.91/1.00    inference(ennf_transformation,[],[f9])).
% 3.91/1.00  
% 3.91/1.00  fof(f26,plain,(
% 3.91/1.00    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.91/1.00    inference(flattening,[],[f25])).
% 3.91/1.00  
% 3.91/1.00  fof(f52,plain,(
% 3.91/1.00    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.91/1.00    inference(nnf_transformation,[],[f26])).
% 3.91/1.00  
% 3.91/1.00  fof(f53,plain,(
% 3.91/1.00    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.91/1.00    inference(rectify,[],[f52])).
% 3.91/1.00  
% 3.91/1.00  fof(f54,plain,(
% 3.91/1.00    ! [X0] : (? [X1] : (~v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v4_pre_topc(sK5(X0),X0) & v3_pre_topc(sK5(X0),X0) & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.91/1.00    introduced(choice_axiom,[])).
% 3.91/1.00  
% 3.91/1.00  fof(f55,plain,(
% 3.91/1.00    ! [X0] : (((v3_tdlat_3(X0) | (~v4_pre_topc(sK5(X0),X0) & v3_pre_topc(sK5(X0),X0) & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.91/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f53,f54])).
% 3.91/1.00  
% 3.91/1.00  fof(f92,plain,(
% 3.91/1.00    ( ! [X2,X0] : (v4_pre_topc(X2,X0) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.91/1.00    inference(cnf_transformation,[],[f55])).
% 3.91/1.00  
% 3.91/1.00  fof(f108,plain,(
% 3.91/1.00    v2_pre_topc(sK8)),
% 3.91/1.00    inference(cnf_transformation,[],[f67])).
% 3.91/1.00  
% 3.91/1.00  fof(f109,plain,(
% 3.91/1.00    v3_tdlat_3(sK8)),
% 3.91/1.00    inference(cnf_transformation,[],[f67])).
% 3.91/1.00  
% 3.91/1.00  fof(f110,plain,(
% 3.91/1.00    l1_pre_topc(sK8)),
% 3.91/1.00    inference(cnf_transformation,[],[f67])).
% 3.91/1.00  
% 3.91/1.00  fof(f12,axiom,(
% 3.91/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 3.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/1.00  
% 3.91/1.00  fof(f31,plain,(
% 3.91/1.00    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.91/1.00    inference(ennf_transformation,[],[f12])).
% 3.91/1.00  
% 3.91/1.00  fof(f32,plain,(
% 3.91/1.00    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.91/1.00    inference(flattening,[],[f31])).
% 3.91/1.00  
% 3.91/1.00  fof(f104,plain,(
% 3.91/1.00    ( ! [X0,X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.91/1.00    inference(cnf_transformation,[],[f32])).
% 3.91/1.00  
% 3.91/1.00  fof(f5,axiom,(
% 3.91/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 3.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/1.00  
% 3.91/1.00  fof(f18,plain,(
% 3.91/1.00    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.91/1.00    inference(ennf_transformation,[],[f5])).
% 3.91/1.00  
% 3.91/1.00  fof(f38,plain,(
% 3.91/1.00    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.91/1.00    inference(nnf_transformation,[],[f18])).
% 3.91/1.00  
% 3.91/1.00  fof(f74,plain,(
% 3.91/1.00    ( ! [X0,X1] : (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.91/1.00    inference(cnf_transformation,[],[f38])).
% 3.91/1.00  
% 3.91/1.00  fof(f107,plain,(
% 3.91/1.00    ~v2_struct_0(sK8)),
% 3.91/1.00    inference(cnf_transformation,[],[f67])).
% 3.91/1.00  
% 3.91/1.00  fof(f113,plain,(
% 3.91/1.00    v3_tex_2(sK9,sK8)),
% 3.91/1.00    inference(cnf_transformation,[],[f67])).
% 3.91/1.00  
% 3.91/1.00  fof(f112,plain,(
% 3.91/1.00    v4_pre_topc(sK9,sK8) | v3_pre_topc(sK9,sK8)),
% 3.91/1.00    inference(cnf_transformation,[],[f67])).
% 3.91/1.00  
% 3.91/1.00  fof(f10,axiom,(
% 3.91/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 3.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/1.00  
% 3.91/1.00  fof(f27,plain,(
% 3.91/1.00    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.91/1.00    inference(ennf_transformation,[],[f10])).
% 3.91/1.00  
% 3.91/1.00  fof(f28,plain,(
% 3.91/1.00    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.91/1.00    inference(flattening,[],[f27])).
% 3.91/1.00  
% 3.91/1.00  fof(f56,plain,(
% 3.91/1.00    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.91/1.00    inference(nnf_transformation,[],[f28])).
% 3.91/1.00  
% 3.91/1.00  fof(f57,plain,(
% 3.91/1.00    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.91/1.00    inference(rectify,[],[f56])).
% 3.91/1.00  
% 3.91/1.00  fof(f58,plain,(
% 3.91/1.00    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK6(X0),X0) & v4_pre_topc(sK6(X0),X0) & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.91/1.00    introduced(choice_axiom,[])).
% 3.91/1.00  
% 3.91/1.00  fof(f59,plain,(
% 3.91/1.00    ! [X0] : (((v3_tdlat_3(X0) | (~v3_pre_topc(sK6(X0),X0) & v4_pre_topc(sK6(X0),X0) & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.91/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f57,f58])).
% 3.91/1.00  
% 3.91/1.00  fof(f96,plain,(
% 3.91/1.00    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.91/1.00    inference(cnf_transformation,[],[f59])).
% 3.91/1.00  
% 3.91/1.00  fof(f8,axiom,(
% 3.91/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k1_tarski(X2) = X1 => v3_pre_topc(X1,X0)))) => v1_tdlat_3(X0)))),
% 3.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/1.00  
% 3.91/1.00  fof(f23,plain,(
% 3.91/1.00    ! [X0] : ((v1_tdlat_3(X0) | ? [X1] : (? [X2] : ((~v3_pre_topc(X1,X0) & k1_tarski(X2) = X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.91/1.00    inference(ennf_transformation,[],[f8])).
% 3.91/1.00  
% 3.91/1.00  fof(f24,plain,(
% 3.91/1.00    ! [X0] : (v1_tdlat_3(X0) | ? [X1] : (? [X2] : (~v3_pre_topc(X1,X0) & k1_tarski(X2) = X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.91/1.00    inference(flattening,[],[f23])).
% 3.91/1.00  
% 3.91/1.00  fof(f50,plain,(
% 3.91/1.00    ( ! [X1] : (! [X0] : (? [X2] : (~v3_pre_topc(X1,X0) & k1_tarski(X2) = X1 & m1_subset_1(X2,u1_struct_0(X0))) => (~v3_pre_topc(X1,X0) & k1_tarski(sK4(X0)) = X1 & m1_subset_1(sK4(X0),u1_struct_0(X0))))) )),
% 3.91/1.00    introduced(choice_axiom,[])).
% 3.91/1.00  
% 3.91/1.00  fof(f49,plain,(
% 3.91/1.00    ! [X0] : (? [X1] : (? [X2] : (~v3_pre_topc(X1,X0) & k1_tarski(X2) = X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~v3_pre_topc(sK3(X0),X0) & k1_tarski(X2) = sK3(X0) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.91/1.00    introduced(choice_axiom,[])).
% 3.91/1.00  
% 3.91/1.00  fof(f51,plain,(
% 3.91/1.00    ! [X0] : (v1_tdlat_3(X0) | ((~v3_pre_topc(sK3(X0),X0) & k1_tarski(sK4(X0)) = sK3(X0) & m1_subset_1(sK4(X0),u1_struct_0(X0))) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.91/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f24,f50,f49])).
% 3.91/1.00  
% 3.91/1.00  fof(f88,plain,(
% 3.91/1.00    ( ! [X0] : (v1_tdlat_3(X0) | m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.91/1.00    inference(cnf_transformation,[],[f51])).
% 3.91/1.00  
% 3.91/1.00  fof(f13,axiom,(
% 3.91/1.00    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 3.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/1.00  
% 3.91/1.00  fof(f33,plain,(
% 3.91/1.00    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.91/1.00    inference(ennf_transformation,[],[f13])).
% 3.91/1.00  
% 3.91/1.00  fof(f34,plain,(
% 3.91/1.00    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.91/1.00    inference(flattening,[],[f33])).
% 3.91/1.00  
% 3.91/1.00  fof(f64,plain,(
% 3.91/1.00    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | v1_subset_1(X1,u1_struct_0(X0))) & (~v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.91/1.00    inference(nnf_transformation,[],[f34])).
% 3.91/1.00  
% 3.91/1.00  fof(f105,plain,(
% 3.91/1.00    ( ! [X0,X1] : (~v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.91/1.00    inference(cnf_transformation,[],[f64])).
% 3.91/1.00  
% 3.91/1.00  fof(f114,plain,(
% 3.91/1.00    v1_subset_1(sK9,u1_struct_0(sK8))),
% 3.91/1.00    inference(cnf_transformation,[],[f67])).
% 3.91/1.00  
% 3.91/1.00  fof(f2,axiom,(
% 3.91/1.00    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/1.00  
% 3.91/1.00  fof(f69,plain,(
% 3.91/1.00    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.91/1.00    inference(cnf_transformation,[],[f2])).
% 3.91/1.00  
% 3.91/1.00  fof(f1,axiom,(
% 3.91/1.00    ! [X0] : k2_subset_1(X0) = X0),
% 3.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/1.00  
% 3.91/1.00  fof(f68,plain,(
% 3.91/1.00    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.91/1.00    inference(cnf_transformation,[],[f1])).
% 3.91/1.00  
% 3.91/1.00  fof(f6,axiom,(
% 3.91/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 3.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/1.00  
% 3.91/1.00  fof(f19,plain,(
% 3.91/1.00    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.91/1.00    inference(ennf_transformation,[],[f6])).
% 3.91/1.00  
% 3.91/1.00  fof(f20,plain,(
% 3.91/1.00    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.91/1.00    inference(flattening,[],[f19])).
% 3.91/1.00  
% 3.91/1.00  fof(f39,plain,(
% 3.91/1.00    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.91/1.00    inference(nnf_transformation,[],[f20])).
% 3.91/1.00  
% 3.91/1.00  fof(f40,plain,(
% 3.91/1.00    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.91/1.00    inference(rectify,[],[f39])).
% 3.91/1.00  
% 3.91/1.00  fof(f42,plain,(
% 3.91/1.00    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4 & v3_pre_topc(sK1(X0,X1,X4),X0) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.91/1.00    introduced(choice_axiom,[])).
% 3.91/1.00  
% 3.91/1.00  fof(f41,plain,(
% 3.91/1.00    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.91/1.00    introduced(choice_axiom,[])).
% 3.91/1.00  
% 3.91/1.00  fof(f43,plain,(
% 3.91/1.00    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4 & v3_pre_topc(sK1(X0,X1,X4),X0) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.91/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).
% 3.91/1.00  
% 3.91/1.00  fof(f76,plain,(
% 3.91/1.00    ( ! [X4,X0,X1] : (m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.91/1.00    inference(cnf_transformation,[],[f43])).
% 3.91/1.00  
% 3.91/1.00  fof(f77,plain,(
% 3.91/1.00    ( ! [X4,X0,X1] : (v3_pre_topc(sK1(X0,X1,X4),X0) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.91/1.00    inference(cnf_transformation,[],[f43])).
% 3.91/1.00  
% 3.91/1.00  fof(f7,axiom,(
% 3.91/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 3.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/1.00  
% 3.91/1.00  fof(f21,plain,(
% 3.91/1.00    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.91/1.00    inference(ennf_transformation,[],[f7])).
% 3.91/1.00  
% 3.91/1.00  fof(f22,plain,(
% 3.91/1.00    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.91/1.00    inference(flattening,[],[f21])).
% 3.91/1.00  
% 3.91/1.00  fof(f44,plain,(
% 3.91/1.00    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.91/1.00    inference(nnf_transformation,[],[f22])).
% 3.91/1.00  
% 3.91/1.00  fof(f45,plain,(
% 3.91/1.00    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.91/1.00    inference(flattening,[],[f44])).
% 3.91/1.00  
% 3.91/1.00  fof(f46,plain,(
% 3.91/1.00    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.91/1.00    inference(rectify,[],[f45])).
% 3.91/1.00  
% 3.91/1.00  fof(f47,plain,(
% 3.91/1.00    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.91/1.00    introduced(choice_axiom,[])).
% 3.91/1.00  
% 3.91/1.00  fof(f48,plain,(
% 3.91/1.00    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.91/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f46,f47])).
% 3.91/1.00  
% 3.91/1.00  fof(f82,plain,(
% 3.91/1.00    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.91/1.00    inference(cnf_transformation,[],[f48])).
% 3.91/1.00  
% 3.91/1.00  fof(f3,axiom,(
% 3.91/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/1.00  
% 3.91/1.00  fof(f37,plain,(
% 3.91/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.91/1.00    inference(nnf_transformation,[],[f3])).
% 3.91/1.00  
% 3.91/1.00  fof(f70,plain,(
% 3.91/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.91/1.00    inference(cnf_transformation,[],[f37])).
% 3.91/1.00  
% 3.91/1.00  fof(f11,axiom,(
% 3.91/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 3.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/1.00  
% 3.91/1.00  fof(f29,plain,(
% 3.91/1.00    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.91/1.00    inference(ennf_transformation,[],[f11])).
% 3.91/1.00  
% 3.91/1.00  fof(f30,plain,(
% 3.91/1.00    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.91/1.00    inference(flattening,[],[f29])).
% 3.91/1.00  
% 3.91/1.00  fof(f60,plain,(
% 3.91/1.00    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.91/1.00    inference(nnf_transformation,[],[f30])).
% 3.91/1.00  
% 3.91/1.00  fof(f61,plain,(
% 3.91/1.00    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.91/1.00    inference(rectify,[],[f60])).
% 3.91/1.00  
% 3.91/1.00  fof(f62,plain,(
% 3.91/1.00    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK7(X0,X1))) != sK7(X0,X1) & r1_tarski(sK7(X0,X1),X1) & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.91/1.00    introduced(choice_axiom,[])).
% 3.91/1.00  
% 3.91/1.00  fof(f63,plain,(
% 3.91/1.00    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK7(X0,X1))) != sK7(X0,X1) & r1_tarski(sK7(X0,X1),X1) & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.91/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f61,f62])).
% 3.91/1.00  
% 3.91/1.00  fof(f100,plain,(
% 3.91/1.00    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.91/1.00    inference(cnf_transformation,[],[f63])).
% 3.91/1.00  
% 3.91/1.00  fof(f78,plain,(
% 3.91/1.00    ( ! [X4,X0,X1] : (k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4 | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.91/1.00    inference(cnf_transformation,[],[f43])).
% 3.91/1.00  
% 3.91/1.00  fof(f71,plain,(
% 3.91/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.91/1.00    inference(cnf_transformation,[],[f37])).
% 3.91/1.00  
% 3.91/1.00  fof(f91,plain,(
% 3.91/1.00    ( ! [X0] : (v1_tdlat_3(X0) | ~v3_pre_topc(sK3(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.91/1.00    inference(cnf_transformation,[],[f51])).
% 3.91/1.00  
% 3.91/1.00  fof(f73,plain,(
% 3.91/1.00    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.91/1.00    inference(cnf_transformation,[],[f17])).
% 3.91/1.00  
% 3.91/1.00  cnf(c_42,negated_conjecture,
% 3.91/1.00      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
% 3.91/1.00      inference(cnf_transformation,[],[f111]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_3836,plain,
% 3.91/1.00      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_5,plain,
% 3.91/1.00      ( ~ v4_pre_topc(X0,X1)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | ~ l1_pre_topc(X1)
% 3.91/1.00      | k2_pre_topc(X1,X0) = X0 ),
% 3.91/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_27,plain,
% 3.91/1.00      ( ~ v3_pre_topc(X0,X1)
% 3.91/1.00      | v4_pre_topc(X0,X1)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | ~ v3_tdlat_3(X1)
% 3.91/1.00      | ~ l1_pre_topc(X1)
% 3.91/1.00      | ~ v2_pre_topc(X1) ),
% 3.91/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_45,negated_conjecture,
% 3.91/1.00      ( v2_pre_topc(sK8) ),
% 3.91/1.00      inference(cnf_transformation,[],[f108]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_889,plain,
% 3.91/1.00      ( ~ v3_pre_topc(X0,X1)
% 3.91/1.00      | v4_pre_topc(X0,X1)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | ~ v3_tdlat_3(X1)
% 3.91/1.00      | ~ l1_pre_topc(X1)
% 3.91/1.00      | sK8 != X1 ),
% 3.91/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_45]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_890,plain,
% 3.91/1.00      ( ~ v3_pre_topc(X0,sK8)
% 3.91/1.00      | v4_pre_topc(X0,sK8)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | ~ v3_tdlat_3(sK8)
% 3.91/1.00      | ~ l1_pre_topc(sK8) ),
% 3.91/1.00      inference(unflattening,[status(thm)],[c_889]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_44,negated_conjecture,
% 3.91/1.00      ( v3_tdlat_3(sK8) ),
% 3.91/1.00      inference(cnf_transformation,[],[f109]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_43,negated_conjecture,
% 3.91/1.00      ( l1_pre_topc(sK8) ),
% 3.91/1.00      inference(cnf_transformation,[],[f110]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_894,plain,
% 3.91/1.00      ( ~ v3_pre_topc(X0,sK8)
% 3.91/1.00      | v4_pre_topc(X0,sK8)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) ),
% 3.91/1.00      inference(global_propositional_subsumption,
% 3.91/1.00                [status(thm)],
% 3.91/1.00                [c_890,c_44,c_43]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_974,plain,
% 3.91/1.00      ( ~ v3_pre_topc(X0,sK8)
% 3.91/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | ~ l1_pre_topc(X2)
% 3.91/1.00      | X0 != X1
% 3.91/1.00      | k2_pre_topc(X2,X1) = X1
% 3.91/1.00      | sK8 != X2 ),
% 3.91/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_894]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_975,plain,
% 3.91/1.00      ( ~ v3_pre_topc(X0,sK8)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | ~ l1_pre_topc(sK8)
% 3.91/1.00      | k2_pre_topc(sK8,X0) = X0 ),
% 3.91/1.00      inference(unflattening,[status(thm)],[c_974]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_979,plain,
% 3.91/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | ~ v3_pre_topc(X0,sK8)
% 3.91/1.00      | k2_pre_topc(sK8,X0) = X0 ),
% 3.91/1.00      inference(global_propositional_subsumption,
% 3.91/1.00                [status(thm)],
% 3.91/1.00                [c_975,c_43]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_980,plain,
% 3.91/1.00      ( ~ v3_pre_topc(X0,sK8)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | k2_pre_topc(sK8,X0) = X0 ),
% 3.91/1.00      inference(renaming,[status(thm)],[c_979]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_3826,plain,
% 3.91/1.00      ( k2_pre_topc(sK8,X0) = X0
% 3.91/1.00      | v3_pre_topc(X0,sK8) != iProver_top
% 3.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_980]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_5923,plain,
% 3.91/1.00      ( k2_pre_topc(sK8,sK9) = sK9
% 3.91/1.00      | v3_pre_topc(sK9,sK8) != iProver_top ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_3836,c_3826]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_36,plain,
% 3.91/1.00      ( ~ v3_tex_2(X0,X1)
% 3.91/1.00      | ~ v3_pre_topc(X0,X1)
% 3.91/1.00      | v1_tops_1(X0,X1)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | v2_struct_0(X1)
% 3.91/1.00      | ~ l1_pre_topc(X1)
% 3.91/1.00      | ~ v2_pre_topc(X1) ),
% 3.91/1.00      inference(cnf_transformation,[],[f104]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_7,plain,
% 3.91/1.00      ( ~ v1_tops_1(X0,X1)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | ~ l1_pre_topc(X1)
% 3.91/1.00      | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
% 3.91/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_583,plain,
% 3.91/1.00      ( ~ v3_tex_2(X0,X1)
% 3.91/1.00      | ~ v3_pre_topc(X0,X1)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | v2_struct_0(X1)
% 3.91/1.00      | ~ l1_pre_topc(X1)
% 3.91/1.00      | ~ v2_pre_topc(X1)
% 3.91/1.00      | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
% 3.91/1.00      inference(resolution,[status(thm)],[c_36,c_7]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_46,negated_conjecture,
% 3.91/1.00      ( ~ v2_struct_0(sK8) ),
% 3.91/1.00      inference(cnf_transformation,[],[f107]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_668,plain,
% 3.91/1.00      ( ~ v3_tex_2(X0,X1)
% 3.91/1.00      | ~ v3_pre_topc(X0,X1)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | ~ l1_pre_topc(X1)
% 3.91/1.00      | ~ v2_pre_topc(X1)
% 3.91/1.00      | k2_pre_topc(X1,X0) = u1_struct_0(X1)
% 3.91/1.00      | sK8 != X1 ),
% 3.91/1.00      inference(resolution_lifted,[status(thm)],[c_583,c_46]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_669,plain,
% 3.91/1.00      ( ~ v3_tex_2(X0,sK8)
% 3.91/1.00      | ~ v3_pre_topc(X0,sK8)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | ~ l1_pre_topc(sK8)
% 3.91/1.00      | ~ v2_pre_topc(sK8)
% 3.91/1.00      | k2_pre_topc(sK8,X0) = u1_struct_0(sK8) ),
% 3.91/1.00      inference(unflattening,[status(thm)],[c_668]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_673,plain,
% 3.91/1.00      ( ~ v3_tex_2(X0,sK8)
% 3.91/1.00      | ~ v3_pre_topc(X0,sK8)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | k2_pre_topc(sK8,X0) = u1_struct_0(sK8) ),
% 3.91/1.00      inference(global_propositional_subsumption,
% 3.91/1.00                [status(thm)],
% 3.91/1.00                [c_669,c_45,c_43]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_3835,plain,
% 3.91/1.00      ( k2_pre_topc(sK8,X0) = u1_struct_0(sK8)
% 3.91/1.00      | v3_tex_2(X0,sK8) != iProver_top
% 3.91/1.00      | v3_pre_topc(X0,sK8) != iProver_top
% 3.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_673]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_4390,plain,
% 3.91/1.00      ( k2_pre_topc(sK8,sK9) = u1_struct_0(sK8)
% 3.91/1.00      | v3_tex_2(sK9,sK8) != iProver_top
% 3.91/1.00      | v3_pre_topc(sK9,sK8) != iProver_top ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_3836,c_3835]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_40,negated_conjecture,
% 3.91/1.00      ( v3_tex_2(sK9,sK8) ),
% 3.91/1.00      inference(cnf_transformation,[],[f113]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_41,negated_conjecture,
% 3.91/1.00      ( v3_pre_topc(sK9,sK8) | v4_pre_topc(sK9,sK8) ),
% 3.91/1.00      inference(cnf_transformation,[],[f112]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_31,plain,
% 3.91/1.00      ( v3_pre_topc(X0,X1)
% 3.91/1.00      | ~ v4_pre_topc(X0,X1)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | ~ v3_tdlat_3(X1)
% 3.91/1.00      | ~ l1_pre_topc(X1)
% 3.91/1.00      | ~ v2_pre_topc(X1) ),
% 3.91/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_868,plain,
% 3.91/1.00      ( v3_pre_topc(X0,X1)
% 3.91/1.00      | ~ v4_pre_topc(X0,X1)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | ~ v3_tdlat_3(X1)
% 3.91/1.00      | ~ l1_pre_topc(X1)
% 3.91/1.00      | sK8 != X1 ),
% 3.91/1.00      inference(resolution_lifted,[status(thm)],[c_31,c_45]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_869,plain,
% 3.91/1.00      ( v3_pre_topc(X0,sK8)
% 3.91/1.00      | ~ v4_pre_topc(X0,sK8)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | ~ v3_tdlat_3(sK8)
% 3.91/1.00      | ~ l1_pre_topc(sK8) ),
% 3.91/1.00      inference(unflattening,[status(thm)],[c_868]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_873,plain,
% 3.91/1.00      ( v3_pre_topc(X0,sK8)
% 3.91/1.00      | ~ v4_pre_topc(X0,sK8)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) ),
% 3.91/1.00      inference(global_propositional_subsumption,
% 3.91/1.00                [status(thm)],
% 3.91/1.00                [c_869,c_44,c_43]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_995,plain,
% 3.91/1.00      ( v3_pre_topc(X0,sK8)
% 3.91/1.00      | v3_pre_topc(sK9,sK8)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | sK8 != sK8
% 3.91/1.00      | sK9 != X0 ),
% 3.91/1.00      inference(resolution_lifted,[status(thm)],[c_41,c_873]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_996,plain,
% 3.91/1.00      ( v3_pre_topc(sK9,sK8)
% 3.91/1.00      | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
% 3.91/1.00      inference(unflattening,[status(thm)],[c_995]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_998,plain,
% 3.91/1.00      ( v3_pre_topc(sK9,sK8) ),
% 3.91/1.00      inference(global_propositional_subsumption,
% 3.91/1.00                [status(thm)],
% 3.91/1.00                [c_996,c_42]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1378,plain,
% 3.91/1.00      ( ~ v3_tex_2(X0,sK8)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | k2_pre_topc(sK8,X0) = u1_struct_0(sK8)
% 3.91/1.00      | sK8 != sK8
% 3.91/1.00      | sK9 != X0 ),
% 3.91/1.00      inference(resolution_lifted,[status(thm)],[c_998,c_673]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1379,plain,
% 3.91/1.00      ( ~ v3_tex_2(sK9,sK8)
% 3.91/1.00      | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | k2_pre_topc(sK8,sK9) = u1_struct_0(sK8) ),
% 3.91/1.00      inference(unflattening,[status(thm)],[c_1378]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_4398,plain,
% 3.91/1.00      ( k2_pre_topc(sK8,sK9) = u1_struct_0(sK8) ),
% 3.91/1.00      inference(global_propositional_subsumption,
% 3.91/1.00                [status(thm)],
% 3.91/1.00                [c_4390,c_42,c_40,c_1379]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_5930,plain,
% 3.91/1.00      ( u1_struct_0(sK8) = sK9 | v3_pre_topc(sK9,sK8) != iProver_top ),
% 3.91/1.00      inference(demodulation,[status(thm)],[c_5923,c_4398]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_51,plain,
% 3.91/1.00      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_997,plain,
% 3.91/1.00      ( v3_pre_topc(sK9,sK8) = iProver_top
% 3.91/1.00      | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_996]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_6075,plain,
% 3.91/1.00      ( u1_struct_0(sK8) = sK9 ),
% 3.91/1.00      inference(global_propositional_subsumption,
% 3.91/1.00                [status(thm)],
% 3.91/1.00                [c_5930,c_51,c_997]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_23,plain,
% 3.91/1.00      ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.91/1.00      | v1_tdlat_3(X0)
% 3.91/1.00      | ~ l1_pre_topc(X0)
% 3.91/1.00      | ~ v2_pre_topc(X0) ),
% 3.91/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_38,plain,
% 3.91/1.00      ( ~ v1_subset_1(X0,u1_struct_0(X1))
% 3.91/1.00      | ~ v3_tex_2(X0,X1)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | v2_struct_0(X1)
% 3.91/1.00      | ~ v1_tdlat_3(X1)
% 3.91/1.00      | ~ l1_pre_topc(X1)
% 3.91/1.00      | ~ v2_pre_topc(X1) ),
% 3.91/1.00      inference(cnf_transformation,[],[f105]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_39,negated_conjecture,
% 3.91/1.00      ( v1_subset_1(sK9,u1_struct_0(sK8)) ),
% 3.91/1.00      inference(cnf_transformation,[],[f114]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_619,plain,
% 3.91/1.00      ( ~ v3_tex_2(X0,X1)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | v2_struct_0(X1)
% 3.91/1.00      | ~ v1_tdlat_3(X1)
% 3.91/1.00      | ~ l1_pre_topc(X1)
% 3.91/1.00      | ~ v2_pre_topc(X1)
% 3.91/1.00      | u1_struct_0(X1) != u1_struct_0(sK8)
% 3.91/1.00      | sK9 != X0 ),
% 3.91/1.00      inference(resolution_lifted,[status(thm)],[c_38,c_39]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_620,plain,
% 3.91/1.00      ( ~ v3_tex_2(sK9,X0)
% 3.91/1.00      | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0)))
% 3.91/1.00      | v2_struct_0(X0)
% 3.91/1.00      | ~ v1_tdlat_3(X0)
% 3.91/1.00      | ~ l1_pre_topc(X0)
% 3.91/1.00      | ~ v2_pre_topc(X0)
% 3.91/1.00      | u1_struct_0(X0) != u1_struct_0(sK8) ),
% 3.91/1.00      inference(unflattening,[status(thm)],[c_619]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_654,plain,
% 3.91/1.00      ( ~ v3_tex_2(sK9,X0)
% 3.91/1.00      | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0)))
% 3.91/1.00      | ~ v1_tdlat_3(X0)
% 3.91/1.00      | ~ l1_pre_topc(X0)
% 3.91/1.00      | ~ v2_pre_topc(X0)
% 3.91/1.00      | u1_struct_0(X0) != u1_struct_0(sK8)
% 3.91/1.00      | sK8 != X0 ),
% 3.91/1.00      inference(resolution_lifted,[status(thm)],[c_620,c_46]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_655,plain,
% 3.91/1.00      ( ~ v3_tex_2(sK9,sK8)
% 3.91/1.00      | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | ~ v1_tdlat_3(sK8)
% 3.91/1.00      | ~ l1_pre_topc(sK8)
% 3.91/1.00      | ~ v2_pre_topc(sK8)
% 3.91/1.00      | u1_struct_0(sK8) != u1_struct_0(sK8) ),
% 3.91/1.00      inference(unflattening,[status(thm)],[c_654]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_622,plain,
% 3.91/1.00      ( ~ v3_tex_2(sK9,sK8)
% 3.91/1.00      | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | v2_struct_0(sK8)
% 3.91/1.00      | ~ v1_tdlat_3(sK8)
% 3.91/1.00      | ~ l1_pre_topc(sK8)
% 3.91/1.00      | ~ v2_pre_topc(sK8)
% 3.91/1.00      | u1_struct_0(sK8) != u1_struct_0(sK8) ),
% 3.91/1.00      inference(instantiation,[status(thm)],[c_620]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_657,plain,
% 3.91/1.00      ( ~ v1_tdlat_3(sK8) | u1_struct_0(sK8) != u1_struct_0(sK8) ),
% 3.91/1.00      inference(global_propositional_subsumption,
% 3.91/1.00                [status(thm)],
% 3.91/1.00                [c_655,c_46,c_45,c_43,c_42,c_40,c_622]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_808,plain,
% 3.91/1.00      ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.91/1.00      | ~ l1_pre_topc(X0)
% 3.91/1.00      | ~ v2_pre_topc(X0)
% 3.91/1.00      | u1_struct_0(sK8) != u1_struct_0(sK8)
% 3.91/1.00      | sK8 != X0 ),
% 3.91/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_657]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_809,plain,
% 3.91/1.00      ( m1_subset_1(sK3(sK8),k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | ~ l1_pre_topc(sK8)
% 3.91/1.00      | ~ v2_pre_topc(sK8) ),
% 3.91/1.00      inference(unflattening,[status(thm)],[c_808]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_811,plain,
% 3.91/1.00      ( m1_subset_1(sK3(sK8),k1_zfmisc_1(u1_struct_0(sK8))) ),
% 3.91/1.00      inference(global_propositional_subsumption,
% 3.91/1.00                [status(thm)],
% 3.91/1.00                [c_809,c_45,c_43]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_3830,plain,
% 3.91/1.00      ( m1_subset_1(sK3(sK8),k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_811]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_6084,plain,
% 3.91/1.00      ( m1_subset_1(sK3(sK8),k1_zfmisc_1(sK9)) = iProver_top ),
% 3.91/1.00      inference(demodulation,[status(thm)],[c_6075,c_3830]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1,plain,
% 3.91/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.91/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_3840,plain,
% 3.91/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_0,plain,
% 3.91/1.00      ( k2_subset_1(X0) = X0 ),
% 3.91/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_3841,plain,
% 3.91/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.91/1.00      inference(light_normalisation,[status(thm)],[c_3840,c_0]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_13,plain,
% 3.91/1.00      ( ~ v2_tex_2(X0,X1)
% 3.91/1.00      | ~ r1_tarski(X2,X0)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | ~ l1_pre_topc(X1) ),
% 3.91/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1148,plain,
% 3.91/1.00      ( ~ v2_tex_2(X0,X1)
% 3.91/1.00      | ~ r1_tarski(X2,X0)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | sK8 != X1 ),
% 3.91/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_43]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1149,plain,
% 3.91/1.00      ( ~ v2_tex_2(X0,sK8)
% 3.91/1.00      | ~ r1_tarski(X1,X0)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | m1_subset_1(sK1(sK8,X0,X1),k1_zfmisc_1(u1_struct_0(sK8))) ),
% 3.91/1.00      inference(unflattening,[status(thm)],[c_1148]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_3817,plain,
% 3.91/1.00      ( v2_tex_2(X0,sK8) != iProver_top
% 3.91/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 3.91/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 3.91/1.00      | m1_subset_1(sK1(sK8,X0,X1),k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_1149]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_6098,plain,
% 3.91/1.00      ( v2_tex_2(X0,sK8) != iProver_top
% 3.91/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(sK9)) != iProver_top
% 3.91/1.00      | m1_subset_1(X1,k1_zfmisc_1(sK9)) != iProver_top
% 3.91/1.00      | m1_subset_1(sK1(sK8,X0,X1),k1_zfmisc_1(sK9)) = iProver_top ),
% 3.91/1.00      inference(demodulation,[status(thm)],[c_6075,c_3817]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_5927,plain,
% 3.91/1.00      ( k2_pre_topc(sK8,sK1(sK8,X0,X1)) = sK1(sK8,X0,X1)
% 3.91/1.00      | v3_pre_topc(sK1(sK8,X0,X1),sK8) != iProver_top
% 3.91/1.00      | v2_tex_2(X0,sK8) != iProver_top
% 3.91/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 3.91/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_3817,c_3826]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_12,plain,
% 3.91/1.00      ( v3_pre_topc(sK1(X0,X1,X2),X0)
% 3.91/1.00      | ~ v2_tex_2(X1,X0)
% 3.91/1.00      | ~ r1_tarski(X2,X1)
% 3.91/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.91/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 3.91/1.00      | ~ l1_pre_topc(X0) ),
% 3.91/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1016,plain,
% 3.91/1.00      ( v3_pre_topc(sK1(X0,X1,X2),X0)
% 3.91/1.00      | ~ v2_tex_2(X1,X0)
% 3.91/1.00      | ~ r1_tarski(X2,X1)
% 3.91/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.91/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 3.91/1.00      | sK8 != X0 ),
% 3.91/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_43]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1017,plain,
% 3.91/1.00      ( v3_pre_topc(sK1(sK8,X0,X1),sK8)
% 3.91/1.00      | ~ v2_tex_2(X0,sK8)
% 3.91/1.00      | ~ r1_tarski(X1,X0)
% 3.91/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) ),
% 3.91/1.00      inference(unflattening,[status(thm)],[c_1016]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1445,plain,
% 3.91/1.00      ( ~ v2_tex_2(X0,sK8)
% 3.91/1.00      | ~ r1_tarski(X1,X0)
% 3.91/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | sK1(sK8,X0,X1) != X2
% 3.91/1.00      | k2_pre_topc(sK8,X2) = X2
% 3.91/1.00      | sK8 != sK8 ),
% 3.91/1.00      inference(resolution_lifted,[status(thm)],[c_980,c_1017]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1446,plain,
% 3.91/1.00      ( ~ v2_tex_2(X0,sK8)
% 3.91/1.00      | ~ r1_tarski(X1,X0)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | ~ m1_subset_1(sK1(sK8,X0,X1),k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | k2_pre_topc(sK8,sK1(sK8,X0,X1)) = sK1(sK8,X0,X1) ),
% 3.91/1.00      inference(unflattening,[status(thm)],[c_1445]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1450,plain,
% 3.91/1.00      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | ~ r1_tarski(X1,X0)
% 3.91/1.00      | ~ v2_tex_2(X0,sK8)
% 3.91/1.00      | k2_pre_topc(sK8,sK1(sK8,X0,X1)) = sK1(sK8,X0,X1) ),
% 3.91/1.00      inference(global_propositional_subsumption,
% 3.91/1.00                [status(thm)],
% 3.91/1.00                [c_1446,c_1149]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1451,plain,
% 3.91/1.00      ( ~ v2_tex_2(X0,sK8)
% 3.91/1.00      | ~ r1_tarski(X1,X0)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | k2_pre_topc(sK8,sK1(sK8,X0,X1)) = sK1(sK8,X0,X1) ),
% 3.91/1.00      inference(renaming,[status(thm)],[c_1450]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1452,plain,
% 3.91/1.00      ( k2_pre_topc(sK8,sK1(sK8,X0,X1)) = sK1(sK8,X0,X1)
% 3.91/1.00      | v2_tex_2(X0,sK8) != iProver_top
% 3.91/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 3.91/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_1451]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_8270,plain,
% 3.91/1.00      ( k2_pre_topc(sK8,sK1(sK8,X0,X1)) = sK1(sK8,X0,X1)
% 3.91/1.00      | v2_tex_2(X0,sK8) != iProver_top
% 3.91/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 3.91/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
% 3.91/1.00      inference(global_propositional_subsumption,
% 3.91/1.00                [status(thm)],
% 3.91/1.00                [c_5927,c_1452]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_8274,plain,
% 3.91/1.00      ( k2_pre_topc(sK8,sK1(sK8,X0,X1)) = sK1(sK8,X0,X1)
% 3.91/1.00      | v2_tex_2(X0,sK8) != iProver_top
% 3.91/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(sK9)) != iProver_top
% 3.91/1.00      | m1_subset_1(X1,k1_zfmisc_1(sK9)) != iProver_top ),
% 3.91/1.00      inference(light_normalisation,[status(thm)],[c_8270,c_6075]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_8279,plain,
% 3.91/1.00      ( k2_pre_topc(sK8,sK1(sK8,sK9,X0)) = sK1(sK8,sK9,X0)
% 3.91/1.00      | v2_tex_2(sK9,sK8) != iProver_top
% 3.91/1.00      | r1_tarski(X0,sK9) != iProver_top
% 3.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(sK9)) != iProver_top ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_3841,c_8274]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_19,plain,
% 3.91/1.00      ( ~ v3_tex_2(X0,X1)
% 3.91/1.00      | v2_tex_2(X0,X1)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | ~ l1_pre_topc(X1) ),
% 3.91/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1037,plain,
% 3.91/1.00      ( ~ v3_tex_2(X0,X1)
% 3.91/1.00      | v2_tex_2(X0,X1)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | sK8 != X1 ),
% 3.91/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_43]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1038,plain,
% 3.91/1.00      ( ~ v3_tex_2(X0,sK8)
% 3.91/1.00      | v2_tex_2(X0,sK8)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) ),
% 3.91/1.00      inference(unflattening,[status(thm)],[c_1037]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1755,plain,
% 3.91/1.00      ( v2_tex_2(X0,sK8)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | sK8 != sK8
% 3.91/1.00      | sK9 != X0 ),
% 3.91/1.00      inference(resolution_lifted,[status(thm)],[c_40,c_1038]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1756,plain,
% 3.91/1.00      ( v2_tex_2(sK9,sK8)
% 3.91/1.00      | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
% 3.91/1.00      inference(unflattening,[status(thm)],[c_1755]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1757,plain,
% 3.91/1.00      ( v2_tex_2(sK9,sK8) = iProver_top
% 3.91/1.00      | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_1756]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_3,plain,
% 3.91/1.00      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.91/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_4415,plain,
% 3.91/1.00      ( r1_tarski(X0,sK9) | ~ m1_subset_1(X0,k1_zfmisc_1(sK9)) ),
% 3.91/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_4416,plain,
% 3.91/1.00      ( r1_tarski(X0,sK9) = iProver_top
% 3.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(sK9)) != iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_4415]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_8422,plain,
% 3.91/1.00      ( k2_pre_topc(sK8,sK1(sK8,sK9,X0)) = sK1(sK8,sK9,X0)
% 3.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(sK9)) != iProver_top ),
% 3.91/1.00      inference(global_propositional_subsumption,
% 3.91/1.00                [status(thm)],
% 3.91/1.00                [c_8279,c_51,c_1757,c_4416]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_8430,plain,
% 3.91/1.00      ( k2_pre_topc(sK8,sK1(sK8,sK9,sK1(sK8,X0,X1))) = sK1(sK8,sK9,sK1(sK8,X0,X1))
% 3.91/1.00      | v2_tex_2(X0,sK8) != iProver_top
% 3.91/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(sK9)) != iProver_top
% 3.91/1.00      | m1_subset_1(X1,k1_zfmisc_1(sK9)) != iProver_top ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_6098,c_8422]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_13191,plain,
% 3.91/1.00      ( k2_pre_topc(sK8,sK1(sK8,sK9,sK1(sK8,sK9,X0))) = sK1(sK8,sK9,sK1(sK8,sK9,X0))
% 3.91/1.00      | v2_tex_2(sK9,sK8) != iProver_top
% 3.91/1.00      | r1_tarski(X0,sK9) != iProver_top
% 3.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(sK9)) != iProver_top ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_3841,c_8430]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_14096,plain,
% 3.91/1.00      ( k2_pre_topc(sK8,sK1(sK8,sK9,sK1(sK8,sK9,X0))) = sK1(sK8,sK9,sK1(sK8,sK9,X0))
% 3.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(sK9)) != iProver_top ),
% 3.91/1.00      inference(global_propositional_subsumption,
% 3.91/1.00                [status(thm)],
% 3.91/1.00                [c_13191,c_51,c_1757,c_4416]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_14104,plain,
% 3.91/1.00      ( k2_pre_topc(sK8,sK1(sK8,sK9,sK1(sK8,sK9,sK3(sK8)))) = sK1(sK8,sK9,sK1(sK8,sK9,sK3(sK8))) ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_6084,c_14096]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_35,plain,
% 3.91/1.00      ( ~ v2_tex_2(X0,X1)
% 3.91/1.00      | ~ r1_tarski(X2,X0)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | v2_struct_0(X1)
% 3.91/1.00      | ~ l1_pre_topc(X1)
% 3.91/1.00      | ~ v2_pre_topc(X1)
% 3.91/1.00      | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2 ),
% 3.91/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_692,plain,
% 3.91/1.00      ( ~ v2_tex_2(X0,X1)
% 3.91/1.00      | ~ r1_tarski(X2,X0)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | ~ l1_pre_topc(X1)
% 3.91/1.00      | ~ v2_pre_topc(X1)
% 3.91/1.00      | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2
% 3.91/1.00      | sK8 != X1 ),
% 3.91/1.00      inference(resolution_lifted,[status(thm)],[c_35,c_46]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_693,plain,
% 3.91/1.00      ( ~ v2_tex_2(X0,sK8)
% 3.91/1.00      | ~ r1_tarski(X1,X0)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | ~ l1_pre_topc(sK8)
% 3.91/1.00      | ~ v2_pre_topc(sK8)
% 3.91/1.00      | k9_subset_1(u1_struct_0(sK8),X0,k2_pre_topc(sK8,X1)) = X1 ),
% 3.91/1.00      inference(unflattening,[status(thm)],[c_692]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_697,plain,
% 3.91/1.00      ( ~ v2_tex_2(X0,sK8)
% 3.91/1.00      | ~ r1_tarski(X1,X0)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | k9_subset_1(u1_struct_0(sK8),X0,k2_pre_topc(sK8,X1)) = X1 ),
% 3.91/1.00      inference(global_propositional_subsumption,
% 3.91/1.00                [status(thm)],
% 3.91/1.00                [c_693,c_45,c_43]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_3834,plain,
% 3.91/1.00      ( k9_subset_1(u1_struct_0(sK8),X0,k2_pre_topc(sK8,X1)) = X1
% 3.91/1.00      | v2_tex_2(X0,sK8) != iProver_top
% 3.91/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 3.91/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_697]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_4434,plain,
% 3.91/1.00      ( k9_subset_1(u1_struct_0(sK8),sK9,k2_pre_topc(sK8,X0)) = X0
% 3.91/1.00      | v2_tex_2(sK9,sK8) != iProver_top
% 3.91/1.00      | r1_tarski(X0,sK9) != iProver_top
% 3.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_3836,c_3834]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_4567,plain,
% 3.91/1.00      ( k9_subset_1(u1_struct_0(sK8),sK9,k2_pre_topc(sK8,X0)) = X0
% 3.91/1.00      | r1_tarski(X0,sK9) != iProver_top
% 3.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
% 3.91/1.00      inference(global_propositional_subsumption,
% 3.91/1.00                [status(thm)],
% 3.91/1.00                [c_4434,c_51,c_1757,c_4059]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_6104,plain,
% 3.91/1.00      ( k9_subset_1(sK9,sK9,k2_pre_topc(sK8,X0)) = X0
% 3.91/1.00      | r1_tarski(X0,sK9) != iProver_top
% 3.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(sK9)) != iProver_top ),
% 3.91/1.00      inference(demodulation,[status(thm)],[c_6075,c_4567]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_6484,plain,
% 3.91/1.00      ( k9_subset_1(sK9,sK9,k2_pre_topc(sK8,X0)) = X0
% 3.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(sK9)) != iProver_top ),
% 3.91/1.00      inference(global_propositional_subsumption,
% 3.91/1.00                [status(thm)],
% 3.91/1.00                [c_6104,c_4416]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_7790,plain,
% 3.91/1.00      ( k9_subset_1(sK9,sK9,k2_pre_topc(sK8,sK1(sK8,X0,X1))) = sK1(sK8,X0,X1)
% 3.91/1.00      | v2_tex_2(X0,sK8) != iProver_top
% 3.91/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(sK9)) != iProver_top
% 3.91/1.00      | m1_subset_1(X1,k1_zfmisc_1(sK9)) != iProver_top ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_6098,c_6484]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_13014,plain,
% 3.91/1.00      ( k9_subset_1(sK9,sK9,k2_pre_topc(sK8,sK1(sK8,sK9,X0))) = sK1(sK8,sK9,X0)
% 3.91/1.00      | v2_tex_2(sK9,sK8) != iProver_top
% 3.91/1.00      | r1_tarski(X0,sK9) != iProver_top
% 3.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(sK9)) != iProver_top ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_3841,c_7790]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_13358,plain,
% 3.91/1.00      ( k9_subset_1(sK9,sK9,k2_pre_topc(sK8,sK1(sK8,sK9,X0))) = sK1(sK8,sK9,X0)
% 3.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(sK9)) != iProver_top ),
% 3.91/1.00      inference(global_propositional_subsumption,
% 3.91/1.00                [status(thm)],
% 3.91/1.00                [c_13014,c_51,c_1757,c_4416]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_13366,plain,
% 3.91/1.00      ( k9_subset_1(sK9,sK9,k2_pre_topc(sK8,sK1(sK8,sK9,sK3(sK8)))) = sK1(sK8,sK9,sK3(sK8)) ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_6084,c_13358]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_11,plain,
% 3.91/1.00      ( ~ v2_tex_2(X0,X1)
% 3.91/1.00      | ~ r1_tarski(X2,X0)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | ~ l1_pre_topc(X1)
% 3.91/1.00      | k9_subset_1(u1_struct_0(X1),X0,sK1(X1,X0,X2)) = X2 ),
% 3.91/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1169,plain,
% 3.91/1.00      ( ~ v2_tex_2(X0,X1)
% 3.91/1.00      | ~ r1_tarski(X2,X0)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | k9_subset_1(u1_struct_0(X1),X0,sK1(X1,X0,X2)) = X2
% 3.91/1.00      | sK8 != X1 ),
% 3.91/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_43]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1170,plain,
% 3.91/1.00      ( ~ v2_tex_2(X0,sK8)
% 3.91/1.00      | ~ r1_tarski(X1,X0)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | k9_subset_1(u1_struct_0(sK8),X0,sK1(sK8,X0,X1)) = X1 ),
% 3.91/1.00      inference(unflattening,[status(thm)],[c_1169]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_3816,plain,
% 3.91/1.00      ( k9_subset_1(u1_struct_0(sK8),X0,sK1(sK8,X0,X1)) = X1
% 3.91/1.00      | v2_tex_2(X0,sK8) != iProver_top
% 3.91/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 3.91/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_1170]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_4584,plain,
% 3.91/1.00      ( k9_subset_1(u1_struct_0(sK8),sK9,sK1(sK8,sK9,X0)) = X0
% 3.91/1.00      | v2_tex_2(sK9,sK8) != iProver_top
% 3.91/1.00      | r1_tarski(X0,sK9) != iProver_top
% 3.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_3836,c_3816]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_4650,plain,
% 3.91/1.00      ( k9_subset_1(u1_struct_0(sK8),sK9,sK1(sK8,sK9,X0)) = X0
% 3.91/1.00      | r1_tarski(X0,sK9) != iProver_top
% 3.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
% 3.91/1.00      inference(global_propositional_subsumption,
% 3.91/1.00                [status(thm)],
% 3.91/1.00                [c_4584,c_51,c_1757,c_4063]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_5606,plain,
% 3.91/1.00      ( k9_subset_1(u1_struct_0(sK8),sK9,sK1(sK8,sK9,sK3(sK8))) = sK3(sK8)
% 3.91/1.00      | r1_tarski(sK3(sK8),sK9) != iProver_top ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_3830,c_4650]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_3838,plain,
% 3.91/1.00      ( r1_tarski(X0,X1) = iProver_top
% 3.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_5599,plain,
% 3.91/1.00      ( r1_tarski(sK3(sK8),u1_struct_0(sK8)) = iProver_top ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_3830,c_3838]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_6080,plain,
% 3.91/1.00      ( r1_tarski(sK3(sK8),sK9) = iProver_top ),
% 3.91/1.00      inference(demodulation,[status(thm)],[c_6075,c_5599]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_6265,plain,
% 3.91/1.00      ( k9_subset_1(u1_struct_0(sK8),sK9,sK1(sK8,sK9,sK3(sK8))) = sK3(sK8) ),
% 3.91/1.00      inference(global_propositional_subsumption,
% 3.91/1.00                [status(thm)],
% 3.91/1.00                [c_5606,c_6080]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_6267,plain,
% 3.91/1.00      ( k9_subset_1(sK9,sK9,sK1(sK8,sK9,sK3(sK8))) = sK3(sK8) ),
% 3.91/1.00      inference(light_normalisation,[status(thm)],[c_6265,c_6075]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_2,plain,
% 3.91/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.91/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_3839,plain,
% 3.91/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_8428,plain,
% 3.91/1.00      ( k2_pre_topc(sK8,sK1(sK8,sK9,X0)) = sK1(sK8,sK9,X0)
% 3.91/1.00      | r1_tarski(X0,sK9) != iProver_top ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_3839,c_8422]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_9623,plain,
% 3.91/1.00      ( k2_pre_topc(sK8,sK1(sK8,sK9,sK3(sK8))) = sK1(sK8,sK9,sK3(sK8)) ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_6080,c_8428]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_13371,plain,
% 3.91/1.00      ( sK1(sK8,sK9,sK3(sK8)) = sK3(sK8) ),
% 3.91/1.00      inference(light_normalisation,
% 3.91/1.00                [status(thm)],
% 3.91/1.00                [c_13366,c_6267,c_9623]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_14109,plain,
% 3.91/1.00      ( k2_pre_topc(sK8,sK3(sK8)) = sK3(sK8) ),
% 3.91/1.00      inference(light_normalisation,[status(thm)],[c_14104,c_13371]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_20,plain,
% 3.91/1.00      ( ~ v3_pre_topc(sK3(X0),X0)
% 3.91/1.00      | v1_tdlat_3(X0)
% 3.91/1.00      | ~ l1_pre_topc(X0)
% 3.91/1.00      | ~ v2_pre_topc(X0) ),
% 3.91/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_838,plain,
% 3.91/1.00      ( ~ v3_pre_topc(sK3(X0),X0)
% 3.91/1.00      | ~ l1_pre_topc(X0)
% 3.91/1.00      | ~ v2_pre_topc(X0)
% 3.91/1.00      | u1_struct_0(sK8) != u1_struct_0(sK8)
% 3.91/1.00      | sK8 != X0 ),
% 3.91/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_657]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_839,plain,
% 3.91/1.00      ( ~ v3_pre_topc(sK3(sK8),sK8)
% 3.91/1.00      | ~ l1_pre_topc(sK8)
% 3.91/1.00      | ~ v2_pre_topc(sK8) ),
% 3.91/1.00      inference(unflattening,[status(thm)],[c_838]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_841,plain,
% 3.91/1.00      ( ~ v3_pre_topc(sK3(sK8),sK8) ),
% 3.91/1.00      inference(global_propositional_subsumption,
% 3.91/1.00                [status(thm)],
% 3.91/1.00                [c_839,c_45,c_43]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_4,plain,
% 3.91/1.00      ( v4_pre_topc(X0,X1)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | ~ l1_pre_topc(X1)
% 3.91/1.00      | ~ v2_pre_topc(X1)
% 3.91/1.00      | k2_pre_topc(X1,X0) != X0 ),
% 3.91/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_910,plain,
% 3.91/1.00      ( v4_pre_topc(X0,X1)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | ~ l1_pre_topc(X1)
% 3.91/1.00      | k2_pre_topc(X1,X0) != X0
% 3.91/1.00      | sK8 != X1 ),
% 3.91/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_45]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_911,plain,
% 3.91/1.00      ( v4_pre_topc(X0,sK8)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | ~ l1_pre_topc(sK8)
% 3.91/1.00      | k2_pre_topc(sK8,X0) != X0 ),
% 3.91/1.00      inference(unflattening,[status(thm)],[c_910]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_915,plain,
% 3.91/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | v4_pre_topc(X0,sK8)
% 3.91/1.00      | k2_pre_topc(sK8,X0) != X0 ),
% 3.91/1.00      inference(global_propositional_subsumption,
% 3.91/1.00                [status(thm)],
% 3.91/1.00                [c_911,c_43]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_916,plain,
% 3.91/1.00      ( v4_pre_topc(X0,sK8)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | k2_pre_topc(sK8,X0) != X0 ),
% 3.91/1.00      inference(renaming,[status(thm)],[c_915]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_943,plain,
% 3.91/1.00      ( v3_pre_topc(X0,sK8)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | k2_pre_topc(sK8,X0) != X0 ),
% 3.91/1.00      inference(resolution,[status(thm)],[c_916,c_873]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1386,plain,
% 3.91/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | k2_pre_topc(sK8,X0) != X0
% 3.91/1.00      | sK3(sK8) != X0
% 3.91/1.00      | sK8 != sK8 ),
% 3.91/1.00      inference(resolution_lifted,[status(thm)],[c_841,c_943]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1387,plain,
% 3.91/1.00      ( ~ m1_subset_1(sK3(sK8),k1_zfmisc_1(u1_struct_0(sK8)))
% 3.91/1.00      | k2_pre_topc(sK8,sK3(sK8)) != sK3(sK8) ),
% 3.91/1.00      inference(unflattening,[status(thm)],[c_1386]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(contradiction,plain,
% 3.91/1.00      ( $false ),
% 3.91/1.00      inference(minisat,[status(thm)],[c_14109,c_1387,c_809,c_43,c_45]) ).
% 3.91/1.00  
% 3.91/1.00  
% 3.91/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.91/1.00  
% 3.91/1.00  ------                               Statistics
% 3.91/1.00  
% 3.91/1.00  ------ General
% 3.91/1.00  
% 3.91/1.00  abstr_ref_over_cycles:                  0
% 3.91/1.00  abstr_ref_under_cycles:                 0
% 3.91/1.00  gc_basic_clause_elim:                   0
% 3.91/1.00  forced_gc_time:                         0
% 3.91/1.00  parsing_time:                           0.01
% 3.91/1.00  unif_index_cands_time:                  0.
% 3.91/1.00  unif_index_add_time:                    0.
% 3.91/1.00  orderings_time:                         0.
% 3.91/1.00  out_proof_time:                         0.015
% 3.91/1.00  total_time:                             0.472
% 3.91/1.00  num_of_symbols:                         60
% 3.91/1.00  num_of_terms:                           10041
% 3.91/1.00  
% 3.91/1.00  ------ Preprocessing
% 3.91/1.00  
% 3.91/1.00  num_of_splits:                          0
% 3.91/1.00  num_of_split_atoms:                     0
% 3.91/1.00  num_of_reused_defs:                     0
% 3.91/1.00  num_eq_ax_congr_red:                    34
% 3.91/1.00  num_of_sem_filtered_clauses:            1
% 3.91/1.00  num_of_subtypes:                        0
% 3.91/1.00  monotx_restored_types:                  0
% 3.91/1.00  sat_num_of_epr_types:                   0
% 3.91/1.00  sat_num_of_non_cyclic_types:            0
% 3.91/1.00  sat_guarded_non_collapsed_types:        0
% 3.91/1.00  num_pure_diseq_elim:                    0
% 3.91/1.00  simp_replaced_by:                       0
% 3.91/1.00  res_preprocessed:                       174
% 3.91/1.00  prep_upred:                             0
% 3.91/1.00  prep_unflattend:                        147
% 3.91/1.00  smt_new_axioms:                         0
% 3.91/1.00  pred_elim_cands:                        5
% 3.91/1.00  pred_elim:                              8
% 3.91/1.00  pred_elim_cl:                           17
% 3.91/1.00  pred_elim_cycles:                       14
% 3.91/1.00  merged_defs:                            8
% 3.91/1.00  merged_defs_ncl:                        0
% 3.91/1.00  bin_hyper_res:                          8
% 3.91/1.00  prep_cycles:                            4
% 3.91/1.00  pred_elim_time:                         0.062
% 3.91/1.00  splitting_time:                         0.
% 3.91/1.00  sem_filter_time:                        0.
% 3.91/1.00  monotx_time:                            0.001
% 3.91/1.00  subtype_inf_time:                       0.
% 3.91/1.00  
% 3.91/1.00  ------ Problem properties
% 3.91/1.00  
% 3.91/1.00  clauses:                                30
% 3.91/1.00  conjectures:                            2
% 3.91/1.00  epr:                                    2
% 3.91/1.00  horn:                                   23
% 3.91/1.00  ground:                                 7
% 3.91/1.00  unary:                                  9
% 3.91/1.00  binary:                                 2
% 3.91/1.00  lits:                                   88
% 3.91/1.00  lits_eq:                                11
% 3.91/1.00  fd_pure:                                0
% 3.91/1.00  fd_pseudo:                              0
% 3.91/1.00  fd_cond:                                0
% 3.91/1.00  fd_pseudo_cond:                         1
% 3.91/1.00  ac_symbols:                             0
% 3.91/1.00  
% 3.91/1.00  ------ Propositional Solver
% 3.91/1.00  
% 3.91/1.00  prop_solver_calls:                      30
% 3.91/1.00  prop_fast_solver_calls:                 2952
% 3.91/1.00  smt_solver_calls:                       0
% 3.91/1.00  smt_fast_solver_calls:                  0
% 3.91/1.00  prop_num_of_clauses:                    5536
% 3.91/1.00  prop_preprocess_simplified:             11959
% 3.91/1.00  prop_fo_subsumed:                       128
% 3.91/1.00  prop_solver_time:                       0.
% 3.91/1.00  smt_solver_time:                        0.
% 3.91/1.00  smt_fast_solver_time:                   0.
% 3.91/1.00  prop_fast_solver_time:                  0.
% 3.91/1.00  prop_unsat_core_time:                   0.
% 3.91/1.00  
% 3.91/1.00  ------ QBF
% 3.91/1.00  
% 3.91/1.00  qbf_q_res:                              0
% 3.91/1.00  qbf_num_tautologies:                    0
% 3.91/1.00  qbf_prep_cycles:                        0
% 3.91/1.00  
% 3.91/1.00  ------ BMC1
% 3.91/1.00  
% 3.91/1.00  bmc1_current_bound:                     -1
% 3.91/1.00  bmc1_last_solved_bound:                 -1
% 3.91/1.00  bmc1_unsat_core_size:                   -1
% 3.91/1.00  bmc1_unsat_core_parents_size:           -1
% 3.91/1.00  bmc1_merge_next_fun:                    0
% 3.91/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.91/1.00  
% 3.91/1.00  ------ Instantiation
% 3.91/1.00  
% 3.91/1.00  inst_num_of_clauses:                    1492
% 3.91/1.00  inst_num_in_passive:                    319
% 3.91/1.00  inst_num_in_active:                     758
% 3.91/1.00  inst_num_in_unprocessed:                415
% 3.91/1.00  inst_num_of_loops:                      960
% 3.91/1.00  inst_num_of_learning_restarts:          0
% 3.91/1.00  inst_num_moves_active_passive:          197
% 3.91/1.00  inst_lit_activity:                      0
% 3.91/1.00  inst_lit_activity_moves:                0
% 3.91/1.00  inst_num_tautologies:                   0
% 3.91/1.00  inst_num_prop_implied:                  0
% 3.91/1.00  inst_num_existing_simplified:           0
% 3.91/1.00  inst_num_eq_res_simplified:             0
% 3.91/1.00  inst_num_child_elim:                    0
% 3.91/1.00  inst_num_of_dismatching_blockings:      428
% 3.91/1.00  inst_num_of_non_proper_insts:           1973
% 3.91/1.00  inst_num_of_duplicates:                 0
% 3.91/1.00  inst_inst_num_from_inst_to_res:         0
% 3.91/1.00  inst_dismatching_checking_time:         0.
% 3.91/1.00  
% 3.91/1.00  ------ Resolution
% 3.91/1.00  
% 3.91/1.00  res_num_of_clauses:                     0
% 3.91/1.00  res_num_in_passive:                     0
% 3.91/1.00  res_num_in_active:                      0
% 3.91/1.00  res_num_of_loops:                       178
% 3.91/1.00  res_forward_subset_subsumed:            185
% 3.91/1.00  res_backward_subset_subsumed:           1
% 3.91/1.00  res_forward_subsumed:                   0
% 3.91/1.00  res_backward_subsumed:                  0
% 3.91/1.00  res_forward_subsumption_resolution:     1
% 3.91/1.00  res_backward_subsumption_resolution:    0
% 3.91/1.00  res_clause_to_clause_subsumption:       2246
% 3.91/1.00  res_orphan_elimination:                 0
% 3.91/1.00  res_tautology_del:                      152
% 3.91/1.00  res_num_eq_res_simplified:              0
% 3.91/1.00  res_num_sel_changes:                    0
% 3.91/1.00  res_moves_from_active_to_pass:          0
% 3.91/1.00  
% 3.91/1.00  ------ Superposition
% 3.91/1.00  
% 3.91/1.00  sup_time_total:                         0.
% 3.91/1.00  sup_time_generating:                    0.
% 3.91/1.00  sup_time_sim_full:                      0.
% 3.91/1.00  sup_time_sim_immed:                     0.
% 3.91/1.00  
% 3.91/1.00  sup_num_of_clauses:                     393
% 3.91/1.00  sup_num_in_active:                      149
% 3.91/1.00  sup_num_in_passive:                     244
% 3.91/1.00  sup_num_of_loops:                       190
% 3.91/1.00  sup_fw_superposition:                   449
% 3.91/1.00  sup_bw_superposition:                   253
% 3.91/1.00  sup_immediate_simplified:               144
% 3.91/1.00  sup_given_eliminated:                   0
% 3.91/1.00  comparisons_done:                       0
% 3.91/1.00  comparisons_avoided:                    0
% 3.91/1.00  
% 3.91/1.00  ------ Simplifications
% 3.91/1.00  
% 3.91/1.00  
% 3.91/1.00  sim_fw_subset_subsumed:                 85
% 3.91/1.00  sim_bw_subset_subsumed:                 10
% 3.91/1.00  sim_fw_subsumed:                        43
% 3.91/1.00  sim_bw_subsumed:                        12
% 3.91/1.00  sim_fw_subsumption_res:                 0
% 3.91/1.00  sim_bw_subsumption_res:                 0
% 3.91/1.00  sim_tautology_del:                      77
% 3.91/1.00  sim_eq_tautology_del:                   10
% 3.91/1.00  sim_eq_res_simp:                        0
% 3.91/1.00  sim_fw_demodulated:                     3
% 3.91/1.00  sim_bw_demodulated:                     38
% 3.91/1.00  sim_light_normalised:                   84
% 3.91/1.00  sim_joinable_taut:                      0
% 3.91/1.00  sim_joinable_simp:                      0
% 3.91/1.00  sim_ac_normalised:                      0
% 3.91/1.00  sim_smt_subsumption:                    0
% 3.91/1.00  
%------------------------------------------------------------------------------
