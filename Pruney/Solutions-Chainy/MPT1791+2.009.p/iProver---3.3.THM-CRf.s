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
% DateTime   : Thu Dec  3 12:23:51 EST 2020

% Result     : Theorem 0.85s
% Output     : CNFRefutation 0.85s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_351)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,sK1)
          | ~ v3_pre_topc(sK1,X0) )
        & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,sK1)
          | v3_pre_topc(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f28,f27])).

fof(f47,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f46,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f43,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f44,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f30,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f41,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f42,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | u1_pre_topc(X0) != k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f48,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) = u1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_14,negated_conjecture,
    ( v3_pre_topc(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_143,plain,
    ( v3_pre_topc(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_14])).

cnf(c_299,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_143])).

cnf(c_300,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_299])).

cnf(c_16,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_302,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_300,c_16,c_15])).

cnf(c_348,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) = u1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | u1_pre_topc(X1) != u1_pre_topc(sK0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_302])).

cnf(c_349,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k5_tmap_1(X0,sK1) = u1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | u1_pre_topc(X0) != u1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_348])).

cnf(c_18,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_391,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k5_tmap_1(X0,sK1) = u1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | u1_pre_topc(X0) != u1_pre_topc(sK0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_349,c_18])).

cnf(c_392,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | u1_pre_topc(sK0) != u1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_17,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_394,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | u1_pre_topc(sK0) != u1_pre_topc(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_392,c_18,c_17,c_16,c_15,c_351])).

cnf(c_589,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_394])).

cnf(c_607,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_589])).

cnf(c_893,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k6_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_455,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k6_tmap_1(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_18])).

cnf(c_456,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_pre_topc(k6_tmap_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_460,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_pre_topc(k6_tmap_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_456,c_17,c_16])).

cnf(c_530,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(sK0,X0) != X1
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_460])).

cnf(c_531,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(k6_tmap_1(sK0,X0))
    | g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0)),u1_pre_topc(k6_tmap_1(sK0,X0))) = k6_tmap_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_530])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_491,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_18])).

cnf(c_492,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | l1_pre_topc(k6_tmap_1(sK0,X0))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_491])).

cnf(c_496,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_492,c_17,c_16])).

cnf(c_497,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | l1_pre_topc(k6_tmap_1(sK0,X0)) ),
    inference(renaming,[status(thm)],[c_496])).

cnf(c_535,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0)),u1_pre_topc(k6_tmap_1(sK0,X0))) = k6_tmap_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_531,c_17,c_16,c_492])).

cnf(c_890,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0)),u1_pre_topc(k6_tmap_1(sK0,X0))) = k6_tmap_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_535])).

cnf(c_1496,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1))) = k6_tmap_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_893,c_890])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_419,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_18])).

cnf(c_420,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(k6_tmap_1(sK0,X0)) = u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_419])).

cnf(c_424,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(k6_tmap_1(sK0,X0)) = u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_420,c_17,c_16])).

cnf(c_892,plain,
    ( u1_struct_0(k6_tmap_1(sK0,X0)) = u1_struct_0(sK0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_424])).

cnf(c_994,plain,
    ( u1_struct_0(k6_tmap_1(sK0,sK1)) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_893,c_892])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_437,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_438,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | u1_pre_topc(k6_tmap_1(sK0,X0)) = k5_tmap_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_442,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_pre_topc(k6_tmap_1(sK0,X0)) = k5_tmap_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_438,c_17,c_16])).

cnf(c_891,plain,
    ( u1_pre_topc(k6_tmap_1(sK0,X0)) = k5_tmap_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_442])).

cnf(c_1092,plain,
    ( u1_pre_topc(k6_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_893,c_891])).

cnf(c_1497,plain,
    ( g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) = k6_tmap_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_1496,c_994,c_1092])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X0
    | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_895,plain,
    ( X0 = X1
    | g1_pre_topc(X2,X0) != g1_pre_topc(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1501,plain,
    ( k5_tmap_1(sK0,sK1) = X0
    | g1_pre_topc(X1,X0) != k6_tmap_1(sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1497,c_895])).

cnf(c_22,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_558,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | k6_tmap_1(sK0,X0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_497])).

cnf(c_559,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(u1_pre_topc(k6_tmap_1(sK0,X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X0))))) ),
    inference(unflattening,[status(thm)],[c_558])).

cnf(c_888,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(u1_pre_topc(k6_tmap_1(sK0,X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X0))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_559])).

cnf(c_1177,plain,
    ( m1_subset_1(u1_pre_topc(k6_tmap_1(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_994,c_888])).

cnf(c_1180,plain,
    ( m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1177,c_1092])).

cnf(c_1502,plain,
    ( k5_tmap_1(sK0,sK1) = X0
    | g1_pre_topc(X1,X0) != k6_tmap_1(sK0,sK1)
    | m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1497,c_895])).

cnf(c_1625,plain,
    ( g1_pre_topc(X1,X0) != k6_tmap_1(sK0,sK1)
    | k5_tmap_1(sK0,sK1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1501,c_22,c_1180,c_1502])).

cnf(c_1626,plain,
    ( k5_tmap_1(sK0,sK1) = X0
    | g1_pre_topc(X1,X0) != k6_tmap_1(sK0,sK1) ),
    inference(renaming,[status(thm)],[c_1625])).

cnf(c_1630,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0) ),
    inference(superposition,[status(thm)],[c_607,c_1626])).

cnf(c_1691,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_1630,c_1497])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) != u1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_13,negated_conjecture,
    ( ~ v3_pre_topc(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_141,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_285,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_141])).

cnf(c_286,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_285])).

cnf(c_288,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_286,c_16,c_15])).

cnf(c_321,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) != u1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | u1_pre_topc(X1) != u1_pre_topc(sK0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_288])).

cnf(c_322,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k5_tmap_1(X0,sK1) != u1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | u1_pre_topc(X0) != u1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_321])).

cnf(c_405,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k5_tmap_1(X0,sK1) != u1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | u1_pre_topc(X0) != u1_pre_topc(sK0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_322,c_18])).

cnf(c_406,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | u1_pre_topc(sK0) != u1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_405])).

cnf(c_408,plain,
    ( k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | u1_pre_topc(sK0) != u1_pre_topc(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_406,c_18,c_17,c_16,c_15,c_324])).

cnf(c_588,plain,
    ( k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_408])).

cnf(c_605,plain,
    ( k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_588])).

cnf(c_1692,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | u1_pre_topc(sK0) != u1_pre_topc(sK0) ),
    inference(demodulation,[status(thm)],[c_1630,c_605])).

cnf(c_1697,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_1692])).

cnf(c_1701,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1691,c_1697])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:52:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 0.85/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.85/1.03  
% 0.85/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.85/1.03  
% 0.85/1.03  ------  iProver source info
% 0.85/1.03  
% 0.85/1.03  git: date: 2020-06-30 10:37:57 +0100
% 0.85/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.85/1.03  git: non_committed_changes: false
% 0.85/1.03  git: last_make_outside_of_git: false
% 0.85/1.03  
% 0.85/1.03  ------ 
% 0.85/1.03  
% 0.85/1.03  ------ Input Options
% 0.85/1.03  
% 0.85/1.03  --out_options                           all
% 0.85/1.03  --tptp_safe_out                         true
% 0.85/1.03  --problem_path                          ""
% 0.85/1.03  --include_path                          ""
% 0.85/1.03  --clausifier                            res/vclausify_rel
% 0.85/1.03  --clausifier_options                    --mode clausify
% 0.85/1.03  --stdin                                 false
% 0.85/1.03  --stats_out                             all
% 0.85/1.03  
% 0.85/1.03  ------ General Options
% 0.85/1.03  
% 0.85/1.03  --fof                                   false
% 0.85/1.03  --time_out_real                         305.
% 0.85/1.03  --time_out_virtual                      -1.
% 0.85/1.03  --symbol_type_check                     false
% 0.85/1.03  --clausify_out                          false
% 0.85/1.03  --sig_cnt_out                           false
% 0.85/1.03  --trig_cnt_out                          false
% 0.85/1.03  --trig_cnt_out_tolerance                1.
% 0.85/1.03  --trig_cnt_out_sk_spl                   false
% 0.85/1.03  --abstr_cl_out                          false
% 0.85/1.03  
% 0.85/1.03  ------ Global Options
% 0.85/1.03  
% 0.85/1.03  --schedule                              default
% 0.85/1.03  --add_important_lit                     false
% 0.85/1.03  --prop_solver_per_cl                    1000
% 0.85/1.03  --min_unsat_core                        false
% 0.85/1.03  --soft_assumptions                      false
% 0.85/1.03  --soft_lemma_size                       3
% 0.85/1.03  --prop_impl_unit_size                   0
% 0.85/1.03  --prop_impl_unit                        []
% 0.85/1.03  --share_sel_clauses                     true
% 0.85/1.03  --reset_solvers                         false
% 0.85/1.03  --bc_imp_inh                            [conj_cone]
% 0.85/1.03  --conj_cone_tolerance                   3.
% 0.85/1.03  --extra_neg_conj                        none
% 0.85/1.03  --large_theory_mode                     true
% 0.85/1.03  --prolific_symb_bound                   200
% 0.85/1.03  --lt_threshold                          2000
% 0.85/1.03  --clause_weak_htbl                      true
% 0.85/1.03  --gc_record_bc_elim                     false
% 0.85/1.03  
% 0.85/1.03  ------ Preprocessing Options
% 0.85/1.03  
% 0.85/1.03  --preprocessing_flag                    true
% 0.85/1.03  --time_out_prep_mult                    0.1
% 0.85/1.03  --splitting_mode                        input
% 0.85/1.03  --splitting_grd                         true
% 0.85/1.03  --splitting_cvd                         false
% 0.85/1.03  --splitting_cvd_svl                     false
% 0.85/1.03  --splitting_nvd                         32
% 0.85/1.03  --sub_typing                            true
% 0.85/1.03  --prep_gs_sim                           true
% 0.85/1.03  --prep_unflatten                        true
% 0.85/1.03  --prep_res_sim                          true
% 0.85/1.03  --prep_upred                            true
% 0.85/1.03  --prep_sem_filter                       exhaustive
% 0.85/1.03  --prep_sem_filter_out                   false
% 0.85/1.03  --pred_elim                             true
% 0.85/1.03  --res_sim_input                         true
% 0.85/1.03  --eq_ax_congr_red                       true
% 0.85/1.03  --pure_diseq_elim                       true
% 0.85/1.03  --brand_transform                       false
% 0.85/1.03  --non_eq_to_eq                          false
% 0.85/1.03  --prep_def_merge                        true
% 0.85/1.03  --prep_def_merge_prop_impl              false
% 0.85/1.03  --prep_def_merge_mbd                    true
% 0.85/1.03  --prep_def_merge_tr_red                 false
% 0.85/1.03  --prep_def_merge_tr_cl                  false
% 0.85/1.03  --smt_preprocessing                     true
% 0.85/1.03  --smt_ac_axioms                         fast
% 0.85/1.03  --preprocessed_out                      false
% 0.85/1.03  --preprocessed_stats                    false
% 0.85/1.03  
% 0.85/1.03  ------ Abstraction refinement Options
% 0.85/1.03  
% 0.85/1.03  --abstr_ref                             []
% 0.85/1.03  --abstr_ref_prep                        false
% 0.85/1.03  --abstr_ref_until_sat                   false
% 0.85/1.03  --abstr_ref_sig_restrict                funpre
% 0.85/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 0.85/1.03  --abstr_ref_under                       []
% 0.85/1.03  
% 0.85/1.03  ------ SAT Options
% 0.85/1.03  
% 0.85/1.03  --sat_mode                              false
% 0.85/1.03  --sat_fm_restart_options                ""
% 0.85/1.03  --sat_gr_def                            false
% 0.85/1.03  --sat_epr_types                         true
% 0.85/1.03  --sat_non_cyclic_types                  false
% 0.85/1.03  --sat_finite_models                     false
% 0.85/1.03  --sat_fm_lemmas                         false
% 0.85/1.03  --sat_fm_prep                           false
% 0.85/1.03  --sat_fm_uc_incr                        true
% 0.85/1.03  --sat_out_model                         small
% 0.85/1.03  --sat_out_clauses                       false
% 0.85/1.03  
% 0.85/1.03  ------ QBF Options
% 0.85/1.03  
% 0.85/1.03  --qbf_mode                              false
% 0.85/1.03  --qbf_elim_univ                         false
% 0.85/1.03  --qbf_dom_inst                          none
% 0.85/1.03  --qbf_dom_pre_inst                      false
% 0.85/1.03  --qbf_sk_in                             false
% 0.85/1.03  --qbf_pred_elim                         true
% 0.85/1.03  --qbf_split                             512
% 0.85/1.03  
% 0.85/1.03  ------ BMC1 Options
% 0.85/1.03  
% 0.85/1.03  --bmc1_incremental                      false
% 0.85/1.03  --bmc1_axioms                           reachable_all
% 0.85/1.03  --bmc1_min_bound                        0
% 0.85/1.03  --bmc1_max_bound                        -1
% 0.85/1.03  --bmc1_max_bound_default                -1
% 0.85/1.03  --bmc1_symbol_reachability              true
% 0.85/1.03  --bmc1_property_lemmas                  false
% 0.85/1.03  --bmc1_k_induction                      false
% 0.85/1.03  --bmc1_non_equiv_states                 false
% 0.85/1.03  --bmc1_deadlock                         false
% 0.85/1.03  --bmc1_ucm                              false
% 0.85/1.03  --bmc1_add_unsat_core                   none
% 0.85/1.03  --bmc1_unsat_core_children              false
% 0.85/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 0.85/1.03  --bmc1_out_stat                         full
% 0.85/1.03  --bmc1_ground_init                      false
% 0.85/1.03  --bmc1_pre_inst_next_state              false
% 0.85/1.03  --bmc1_pre_inst_state                   false
% 0.85/1.03  --bmc1_pre_inst_reach_state             false
% 0.85/1.03  --bmc1_out_unsat_core                   false
% 0.85/1.03  --bmc1_aig_witness_out                  false
% 0.85/1.03  --bmc1_verbose                          false
% 0.85/1.03  --bmc1_dump_clauses_tptp                false
% 0.85/1.03  --bmc1_dump_unsat_core_tptp             false
% 0.85/1.03  --bmc1_dump_file                        -
% 0.85/1.03  --bmc1_ucm_expand_uc_limit              128
% 0.85/1.03  --bmc1_ucm_n_expand_iterations          6
% 0.85/1.03  --bmc1_ucm_extend_mode                  1
% 0.85/1.03  --bmc1_ucm_init_mode                    2
% 0.85/1.03  --bmc1_ucm_cone_mode                    none
% 0.85/1.03  --bmc1_ucm_reduced_relation_type        0
% 0.85/1.03  --bmc1_ucm_relax_model                  4
% 0.85/1.03  --bmc1_ucm_full_tr_after_sat            true
% 0.85/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 0.85/1.03  --bmc1_ucm_layered_model                none
% 0.85/1.03  --bmc1_ucm_max_lemma_size               10
% 0.85/1.03  
% 0.85/1.03  ------ AIG Options
% 0.85/1.03  
% 0.85/1.03  --aig_mode                              false
% 0.85/1.03  
% 0.85/1.03  ------ Instantiation Options
% 0.85/1.03  
% 0.85/1.03  --instantiation_flag                    true
% 0.85/1.03  --inst_sos_flag                         false
% 0.85/1.03  --inst_sos_phase                        true
% 0.85/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.85/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.85/1.03  --inst_lit_sel_side                     num_symb
% 0.85/1.03  --inst_solver_per_active                1400
% 0.85/1.03  --inst_solver_calls_frac                1.
% 0.85/1.03  --inst_passive_queue_type               priority_queues
% 0.85/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.85/1.03  --inst_passive_queues_freq              [25;2]
% 0.85/1.03  --inst_dismatching                      true
% 0.85/1.03  --inst_eager_unprocessed_to_passive     true
% 0.85/1.03  --inst_prop_sim_given                   true
% 0.85/1.03  --inst_prop_sim_new                     false
% 0.85/1.03  --inst_subs_new                         false
% 0.85/1.03  --inst_eq_res_simp                      false
% 0.85/1.03  --inst_subs_given                       false
% 0.85/1.03  --inst_orphan_elimination               true
% 0.85/1.03  --inst_learning_loop_flag               true
% 0.85/1.03  --inst_learning_start                   3000
% 0.85/1.03  --inst_learning_factor                  2
% 0.85/1.03  --inst_start_prop_sim_after_learn       3
% 0.85/1.03  --inst_sel_renew                        solver
% 0.85/1.03  --inst_lit_activity_flag                true
% 0.85/1.03  --inst_restr_to_given                   false
% 0.85/1.03  --inst_activity_threshold               500
% 0.85/1.03  --inst_out_proof                        true
% 0.85/1.03  
% 0.85/1.03  ------ Resolution Options
% 0.85/1.03  
% 0.85/1.03  --resolution_flag                       true
% 0.85/1.03  --res_lit_sel                           adaptive
% 0.85/1.03  --res_lit_sel_side                      none
% 0.85/1.03  --res_ordering                          kbo
% 0.85/1.03  --res_to_prop_solver                    active
% 0.85/1.03  --res_prop_simpl_new                    false
% 0.85/1.03  --res_prop_simpl_given                  true
% 0.85/1.03  --res_passive_queue_type                priority_queues
% 0.85/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.85/1.03  --res_passive_queues_freq               [15;5]
% 0.85/1.03  --res_forward_subs                      full
% 0.85/1.03  --res_backward_subs                     full
% 0.85/1.03  --res_forward_subs_resolution           true
% 0.85/1.03  --res_backward_subs_resolution          true
% 0.85/1.03  --res_orphan_elimination                true
% 0.85/1.03  --res_time_limit                        2.
% 0.85/1.03  --res_out_proof                         true
% 0.85/1.03  
% 0.85/1.03  ------ Superposition Options
% 0.85/1.03  
% 0.85/1.03  --superposition_flag                    true
% 0.85/1.03  --sup_passive_queue_type                priority_queues
% 0.85/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.85/1.03  --sup_passive_queues_freq               [8;1;4]
% 0.85/1.03  --demod_completeness_check              fast
% 0.85/1.03  --demod_use_ground                      true
% 0.85/1.03  --sup_to_prop_solver                    passive
% 0.85/1.03  --sup_prop_simpl_new                    true
% 0.85/1.03  --sup_prop_simpl_given                  true
% 0.85/1.03  --sup_fun_splitting                     false
% 0.85/1.03  --sup_smt_interval                      50000
% 0.85/1.03  
% 0.85/1.03  ------ Superposition Simplification Setup
% 0.85/1.03  
% 0.85/1.03  --sup_indices_passive                   []
% 0.85/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.85/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.85/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.85/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 0.85/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.85/1.03  --sup_full_bw                           [BwDemod]
% 0.85/1.03  --sup_immed_triv                        [TrivRules]
% 0.85/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.85/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.85/1.03  --sup_immed_bw_main                     []
% 0.85/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.85/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 0.85/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.85/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.85/1.03  
% 0.85/1.03  ------ Combination Options
% 0.85/1.03  
% 0.85/1.03  --comb_res_mult                         3
% 0.85/1.03  --comb_sup_mult                         2
% 0.85/1.03  --comb_inst_mult                        10
% 0.85/1.03  
% 0.85/1.03  ------ Debug Options
% 0.85/1.03  
% 0.85/1.03  --dbg_backtrace                         false
% 0.85/1.03  --dbg_dump_prop_clauses                 false
% 0.85/1.03  --dbg_dump_prop_clauses_file            -
% 0.85/1.03  --dbg_out_stat                          false
% 0.85/1.03  ------ Parsing...
% 0.85/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.85/1.03  
% 0.85/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 0.85/1.03  
% 0.85/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.85/1.03  
% 0.85/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.85/1.03  ------ Proving...
% 0.85/1.03  ------ Problem Properties 
% 0.85/1.03  
% 0.85/1.03  
% 0.85/1.03  clauses                                 10
% 0.85/1.03  conjectures                             1
% 0.85/1.03  EPR                                     0
% 0.85/1.03  Horn                                    9
% 0.85/1.03  unary                                   2
% 0.85/1.03  binary                                  6
% 0.85/1.03  lits                                    20
% 0.85/1.03  lits eq                                 11
% 0.85/1.03  fd_pure                                 0
% 0.85/1.03  fd_pseudo                               0
% 0.85/1.03  fd_cond                                 0
% 0.85/1.03  fd_pseudo_cond                          2
% 0.85/1.03  AC symbols                              0
% 0.85/1.03  
% 0.85/1.03  ------ Schedule dynamic 5 is on 
% 0.85/1.03  
% 0.85/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.85/1.03  
% 0.85/1.03  
% 0.85/1.03  ------ 
% 0.85/1.03  Current options:
% 0.85/1.03  ------ 
% 0.85/1.03  
% 0.85/1.03  ------ Input Options
% 0.85/1.03  
% 0.85/1.03  --out_options                           all
% 0.85/1.03  --tptp_safe_out                         true
% 0.85/1.03  --problem_path                          ""
% 0.85/1.03  --include_path                          ""
% 0.85/1.03  --clausifier                            res/vclausify_rel
% 0.85/1.03  --clausifier_options                    --mode clausify
% 0.85/1.03  --stdin                                 false
% 0.85/1.03  --stats_out                             all
% 0.85/1.03  
% 0.85/1.03  ------ General Options
% 0.85/1.03  
% 0.85/1.03  --fof                                   false
% 0.85/1.03  --time_out_real                         305.
% 0.85/1.03  --time_out_virtual                      -1.
% 0.85/1.03  --symbol_type_check                     false
% 0.85/1.03  --clausify_out                          false
% 0.85/1.03  --sig_cnt_out                           false
% 0.85/1.03  --trig_cnt_out                          false
% 0.85/1.03  --trig_cnt_out_tolerance                1.
% 0.85/1.03  --trig_cnt_out_sk_spl                   false
% 0.85/1.03  --abstr_cl_out                          false
% 0.85/1.03  
% 0.85/1.03  ------ Global Options
% 0.85/1.03  
% 0.85/1.03  --schedule                              default
% 0.85/1.03  --add_important_lit                     false
% 0.85/1.03  --prop_solver_per_cl                    1000
% 0.85/1.03  --min_unsat_core                        false
% 0.85/1.03  --soft_assumptions                      false
% 0.85/1.03  --soft_lemma_size                       3
% 0.85/1.03  --prop_impl_unit_size                   0
% 0.85/1.03  --prop_impl_unit                        []
% 0.85/1.03  --share_sel_clauses                     true
% 0.85/1.03  --reset_solvers                         false
% 0.85/1.03  --bc_imp_inh                            [conj_cone]
% 0.85/1.03  --conj_cone_tolerance                   3.
% 0.85/1.03  --extra_neg_conj                        none
% 0.85/1.03  --large_theory_mode                     true
% 0.85/1.03  --prolific_symb_bound                   200
% 0.85/1.03  --lt_threshold                          2000
% 0.85/1.03  --clause_weak_htbl                      true
% 0.85/1.03  --gc_record_bc_elim                     false
% 0.85/1.03  
% 0.85/1.03  ------ Preprocessing Options
% 0.85/1.03  
% 0.85/1.03  --preprocessing_flag                    true
% 0.85/1.03  --time_out_prep_mult                    0.1
% 0.85/1.03  --splitting_mode                        input
% 0.85/1.03  --splitting_grd                         true
% 0.85/1.03  --splitting_cvd                         false
% 0.85/1.03  --splitting_cvd_svl                     false
% 0.85/1.03  --splitting_nvd                         32
% 0.85/1.03  --sub_typing                            true
% 0.85/1.03  --prep_gs_sim                           true
% 0.85/1.03  --prep_unflatten                        true
% 0.85/1.03  --prep_res_sim                          true
% 0.85/1.03  --prep_upred                            true
% 0.85/1.03  --prep_sem_filter                       exhaustive
% 0.85/1.03  --prep_sem_filter_out                   false
% 0.85/1.03  --pred_elim                             true
% 0.85/1.03  --res_sim_input                         true
% 0.85/1.03  --eq_ax_congr_red                       true
% 0.85/1.03  --pure_diseq_elim                       true
% 0.85/1.03  --brand_transform                       false
% 0.85/1.03  --non_eq_to_eq                          false
% 0.85/1.03  --prep_def_merge                        true
% 0.85/1.03  --prep_def_merge_prop_impl              false
% 0.85/1.03  --prep_def_merge_mbd                    true
% 0.85/1.03  --prep_def_merge_tr_red                 false
% 0.85/1.03  --prep_def_merge_tr_cl                  false
% 0.85/1.03  --smt_preprocessing                     true
% 0.85/1.03  --smt_ac_axioms                         fast
% 0.85/1.03  --preprocessed_out                      false
% 0.85/1.03  --preprocessed_stats                    false
% 0.85/1.03  
% 0.85/1.03  ------ Abstraction refinement Options
% 0.85/1.03  
% 0.85/1.03  --abstr_ref                             []
% 0.85/1.03  --abstr_ref_prep                        false
% 0.85/1.03  --abstr_ref_until_sat                   false
% 0.85/1.03  --abstr_ref_sig_restrict                funpre
% 0.85/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 0.85/1.03  --abstr_ref_under                       []
% 0.85/1.03  
% 0.85/1.03  ------ SAT Options
% 0.85/1.03  
% 0.85/1.03  --sat_mode                              false
% 0.85/1.03  --sat_fm_restart_options                ""
% 0.85/1.03  --sat_gr_def                            false
% 0.85/1.03  --sat_epr_types                         true
% 0.85/1.03  --sat_non_cyclic_types                  false
% 0.85/1.03  --sat_finite_models                     false
% 0.85/1.03  --sat_fm_lemmas                         false
% 0.85/1.03  --sat_fm_prep                           false
% 0.85/1.03  --sat_fm_uc_incr                        true
% 0.85/1.03  --sat_out_model                         small
% 0.85/1.03  --sat_out_clauses                       false
% 0.85/1.03  
% 0.85/1.03  ------ QBF Options
% 0.85/1.03  
% 0.85/1.03  --qbf_mode                              false
% 0.85/1.03  --qbf_elim_univ                         false
% 0.85/1.03  --qbf_dom_inst                          none
% 0.85/1.03  --qbf_dom_pre_inst                      false
% 0.85/1.03  --qbf_sk_in                             false
% 0.85/1.03  --qbf_pred_elim                         true
% 0.85/1.03  --qbf_split                             512
% 0.85/1.03  
% 0.85/1.03  ------ BMC1 Options
% 0.85/1.03  
% 0.85/1.03  --bmc1_incremental                      false
% 0.85/1.03  --bmc1_axioms                           reachable_all
% 0.85/1.03  --bmc1_min_bound                        0
% 0.85/1.03  --bmc1_max_bound                        -1
% 0.85/1.03  --bmc1_max_bound_default                -1
% 0.85/1.04  --bmc1_symbol_reachability              true
% 0.85/1.04  --bmc1_property_lemmas                  false
% 0.85/1.04  --bmc1_k_induction                      false
% 0.85/1.04  --bmc1_non_equiv_states                 false
% 0.85/1.04  --bmc1_deadlock                         false
% 0.85/1.04  --bmc1_ucm                              false
% 0.85/1.04  --bmc1_add_unsat_core                   none
% 0.85/1.04  --bmc1_unsat_core_children              false
% 0.85/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 0.85/1.04  --bmc1_out_stat                         full
% 0.85/1.04  --bmc1_ground_init                      false
% 0.85/1.04  --bmc1_pre_inst_next_state              false
% 0.85/1.04  --bmc1_pre_inst_state                   false
% 0.85/1.04  --bmc1_pre_inst_reach_state             false
% 0.85/1.04  --bmc1_out_unsat_core                   false
% 0.85/1.04  --bmc1_aig_witness_out                  false
% 0.85/1.04  --bmc1_verbose                          false
% 0.85/1.04  --bmc1_dump_clauses_tptp                false
% 0.85/1.04  --bmc1_dump_unsat_core_tptp             false
% 0.85/1.04  --bmc1_dump_file                        -
% 0.85/1.04  --bmc1_ucm_expand_uc_limit              128
% 0.85/1.04  --bmc1_ucm_n_expand_iterations          6
% 0.85/1.04  --bmc1_ucm_extend_mode                  1
% 0.85/1.04  --bmc1_ucm_init_mode                    2
% 0.85/1.04  --bmc1_ucm_cone_mode                    none
% 0.85/1.04  --bmc1_ucm_reduced_relation_type        0
% 0.85/1.04  --bmc1_ucm_relax_model                  4
% 0.85/1.04  --bmc1_ucm_full_tr_after_sat            true
% 0.85/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 0.85/1.04  --bmc1_ucm_layered_model                none
% 0.85/1.04  --bmc1_ucm_max_lemma_size               10
% 0.85/1.04  
% 0.85/1.04  ------ AIG Options
% 0.85/1.04  
% 0.85/1.04  --aig_mode                              false
% 0.85/1.04  
% 0.85/1.04  ------ Instantiation Options
% 0.85/1.04  
% 0.85/1.04  --instantiation_flag                    true
% 0.85/1.04  --inst_sos_flag                         false
% 0.85/1.04  --inst_sos_phase                        true
% 0.85/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.85/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.85/1.04  --inst_lit_sel_side                     none
% 0.85/1.04  --inst_solver_per_active                1400
% 0.85/1.04  --inst_solver_calls_frac                1.
% 0.85/1.04  --inst_passive_queue_type               priority_queues
% 0.85/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.85/1.04  --inst_passive_queues_freq              [25;2]
% 0.85/1.04  --inst_dismatching                      true
% 0.85/1.04  --inst_eager_unprocessed_to_passive     true
% 0.85/1.04  --inst_prop_sim_given                   true
% 0.85/1.04  --inst_prop_sim_new                     false
% 0.85/1.04  --inst_subs_new                         false
% 0.85/1.04  --inst_eq_res_simp                      false
% 0.85/1.04  --inst_subs_given                       false
% 0.85/1.04  --inst_orphan_elimination               true
% 0.85/1.04  --inst_learning_loop_flag               true
% 0.85/1.04  --inst_learning_start                   3000
% 0.85/1.04  --inst_learning_factor                  2
% 0.85/1.04  --inst_start_prop_sim_after_learn       3
% 0.85/1.04  --inst_sel_renew                        solver
% 0.85/1.04  --inst_lit_activity_flag                true
% 0.85/1.04  --inst_restr_to_given                   false
% 0.85/1.04  --inst_activity_threshold               500
% 0.85/1.04  --inst_out_proof                        true
% 0.85/1.04  
% 0.85/1.04  ------ Resolution Options
% 0.85/1.04  
% 0.85/1.04  --resolution_flag                       false
% 0.85/1.04  --res_lit_sel                           adaptive
% 0.85/1.04  --res_lit_sel_side                      none
% 0.85/1.04  --res_ordering                          kbo
% 0.85/1.04  --res_to_prop_solver                    active
% 0.85/1.04  --res_prop_simpl_new                    false
% 0.85/1.04  --res_prop_simpl_given                  true
% 0.85/1.04  --res_passive_queue_type                priority_queues
% 0.85/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.85/1.04  --res_passive_queues_freq               [15;5]
% 0.85/1.04  --res_forward_subs                      full
% 0.85/1.04  --res_backward_subs                     full
% 0.85/1.04  --res_forward_subs_resolution           true
% 0.85/1.04  --res_backward_subs_resolution          true
% 0.85/1.04  --res_orphan_elimination                true
% 0.85/1.04  --res_time_limit                        2.
% 0.85/1.04  --res_out_proof                         true
% 0.85/1.04  
% 0.85/1.04  ------ Superposition Options
% 0.85/1.04  
% 0.85/1.04  --superposition_flag                    true
% 0.85/1.04  --sup_passive_queue_type                priority_queues
% 0.85/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.85/1.04  --sup_passive_queues_freq               [8;1;4]
% 0.85/1.04  --demod_completeness_check              fast
% 0.85/1.04  --demod_use_ground                      true
% 0.85/1.04  --sup_to_prop_solver                    passive
% 0.85/1.04  --sup_prop_simpl_new                    true
% 0.85/1.04  --sup_prop_simpl_given                  true
% 0.85/1.04  --sup_fun_splitting                     false
% 0.85/1.04  --sup_smt_interval                      50000
% 0.85/1.04  
% 0.85/1.04  ------ Superposition Simplification Setup
% 0.85/1.04  
% 0.85/1.04  --sup_indices_passive                   []
% 0.85/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.85/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.85/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.85/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 0.85/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.85/1.04  --sup_full_bw                           [BwDemod]
% 0.85/1.04  --sup_immed_triv                        [TrivRules]
% 0.85/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.85/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.85/1.04  --sup_immed_bw_main                     []
% 0.85/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.85/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 0.85/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.85/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.85/1.04  
% 0.85/1.04  ------ Combination Options
% 0.85/1.04  
% 0.85/1.04  --comb_res_mult                         3
% 0.85/1.04  --comb_sup_mult                         2
% 0.85/1.04  --comb_inst_mult                        10
% 0.85/1.04  
% 0.85/1.04  ------ Debug Options
% 0.85/1.04  
% 0.85/1.04  --dbg_backtrace                         false
% 0.85/1.04  --dbg_dump_prop_clauses                 false
% 0.85/1.04  --dbg_dump_prop_clauses_file            -
% 0.85/1.04  --dbg_out_stat                          false
% 0.85/1.04  
% 0.85/1.04  
% 0.85/1.04  
% 0.85/1.04  
% 0.85/1.04  ------ Proving...
% 0.85/1.04  
% 0.85/1.04  
% 0.85/1.04  % SZS status Theorem for theBenchmark.p
% 0.85/1.04  
% 0.85/1.04   Resolution empty clause
% 0.85/1.04  
% 0.85/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 0.85/1.04  
% 0.85/1.04  fof(f6,axiom,(
% 0.85/1.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 0.85/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.85/1.04  
% 0.85/1.04  fof(f17,plain,(
% 0.85/1.04    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.85/1.04    inference(ennf_transformation,[],[f6])).
% 0.85/1.04  
% 0.85/1.04  fof(f18,plain,(
% 0.85/1.04    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.85/1.04    inference(flattening,[],[f17])).
% 0.85/1.04  
% 0.85/1.04  fof(f24,plain,(
% 0.85/1.04    ! [X0] : (! [X1] : (((r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1)) & (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.85/1.04    inference(nnf_transformation,[],[f18])).
% 0.85/1.04  
% 0.85/1.04  fof(f39,plain,(
% 0.85/1.04    ( ! [X0,X1] : (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.85/1.04    inference(cnf_transformation,[],[f24])).
% 0.85/1.04  
% 0.85/1.04  fof(f2,axiom,(
% 0.85/1.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.85/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.85/1.04  
% 0.85/1.04  fof(f12,plain,(
% 0.85/1.04    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.85/1.04    inference(ennf_transformation,[],[f2])).
% 0.85/1.04  
% 0.85/1.04  fof(f23,plain,(
% 0.85/1.04    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.85/1.04    inference(nnf_transformation,[],[f12])).
% 0.85/1.04  
% 0.85/1.04  fof(f31,plain,(
% 0.85/1.04    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.85/1.04    inference(cnf_transformation,[],[f23])).
% 0.85/1.04  
% 0.85/1.04  fof(f8,conjecture,(
% 0.85/1.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 0.85/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.85/1.04  
% 0.85/1.04  fof(f9,negated_conjecture,(
% 0.85/1.04    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 0.85/1.04    inference(negated_conjecture,[],[f8])).
% 0.85/1.04  
% 0.85/1.04  fof(f21,plain,(
% 0.85/1.04    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.85/1.04    inference(ennf_transformation,[],[f9])).
% 0.85/1.04  
% 0.85/1.04  fof(f22,plain,(
% 0.85/1.04    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.85/1.04    inference(flattening,[],[f21])).
% 0.85/1.04  
% 0.85/1.04  fof(f25,plain,(
% 0.85/1.04    ? [X0] : (? [X1] : (((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.85/1.04    inference(nnf_transformation,[],[f22])).
% 0.85/1.04  
% 0.85/1.04  fof(f26,plain,(
% 0.85/1.04    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.85/1.04    inference(flattening,[],[f25])).
% 0.85/1.04  
% 0.85/1.04  fof(f28,plain,(
% 0.85/1.04    ( ! [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,sK1) | ~v3_pre_topc(sK1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,sK1) | v3_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 0.85/1.04    introduced(choice_axiom,[])).
% 0.85/1.04  
% 0.85/1.04  fof(f27,plain,(
% 0.85/1.04    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X1) | ~v3_pre_topc(X1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.85/1.04    introduced(choice_axiom,[])).
% 0.85/1.04  
% 0.85/1.04  fof(f29,plain,(
% 0.85/1.04    ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.85/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f28,f27])).
% 0.85/1.04  
% 0.85/1.04  fof(f47,plain,(
% 0.85/1.04    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)),
% 0.85/1.04    inference(cnf_transformation,[],[f29])).
% 0.85/1.04  
% 0.85/1.04  fof(f45,plain,(
% 0.85/1.04    l1_pre_topc(sK0)),
% 0.85/1.04    inference(cnf_transformation,[],[f29])).
% 0.85/1.04  
% 0.85/1.04  fof(f46,plain,(
% 0.85/1.04    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.85/1.04    inference(cnf_transformation,[],[f29])).
% 0.85/1.04  
% 0.85/1.04  fof(f43,plain,(
% 0.85/1.04    ~v2_struct_0(sK0)),
% 0.85/1.04    inference(cnf_transformation,[],[f29])).
% 0.85/1.04  
% 0.85/1.04  fof(f44,plain,(
% 0.85/1.04    v2_pre_topc(sK0)),
% 0.85/1.04    inference(cnf_transformation,[],[f29])).
% 0.85/1.04  
% 0.85/1.04  fof(f1,axiom,(
% 0.85/1.04    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 0.85/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.85/1.04  
% 0.85/1.04  fof(f10,plain,(
% 0.85/1.04    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 0.85/1.04    inference(ennf_transformation,[],[f1])).
% 0.85/1.04  
% 0.85/1.04  fof(f11,plain,(
% 0.85/1.04    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.85/1.04    inference(flattening,[],[f10])).
% 0.85/1.04  
% 0.85/1.04  fof(f30,plain,(
% 0.85/1.04    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 0.85/1.04    inference(cnf_transformation,[],[f11])).
% 0.85/1.04  
% 0.85/1.04  fof(f5,axiom,(
% 0.85/1.04    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 0.85/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.85/1.04  
% 0.85/1.04  fof(f15,plain,(
% 0.85/1.04    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.85/1.04    inference(ennf_transformation,[],[f5])).
% 0.85/1.04  
% 0.85/1.04  fof(f16,plain,(
% 0.85/1.04    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.85/1.04    inference(flattening,[],[f15])).
% 0.85/1.04  
% 0.85/1.04  fof(f36,plain,(
% 0.85/1.04    ( ! [X0,X1] : (v1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.85/1.04    inference(cnf_transformation,[],[f16])).
% 0.85/1.04  
% 0.85/1.04  fof(f38,plain,(
% 0.85/1.04    ( ! [X0,X1] : (l1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.85/1.04    inference(cnf_transformation,[],[f16])).
% 0.85/1.04  
% 0.85/1.04  fof(f7,axiom,(
% 0.85/1.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 0.85/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.85/1.04  
% 0.85/1.04  fof(f19,plain,(
% 0.85/1.04    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.85/1.04    inference(ennf_transformation,[],[f7])).
% 0.85/1.04  
% 0.85/1.04  fof(f20,plain,(
% 0.85/1.04    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.85/1.04    inference(flattening,[],[f19])).
% 0.85/1.04  
% 0.85/1.04  fof(f41,plain,(
% 0.85/1.04    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.85/1.04    inference(cnf_transformation,[],[f20])).
% 0.85/1.04  
% 0.85/1.04  fof(f42,plain,(
% 0.85/1.04    ( ! [X0,X1] : (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.85/1.04    inference(cnf_transformation,[],[f20])).
% 0.85/1.04  
% 0.85/1.04  fof(f4,axiom,(
% 0.85/1.04    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.85/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.85/1.04  
% 0.85/1.04  fof(f14,plain,(
% 0.85/1.04    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.85/1.04    inference(ennf_transformation,[],[f4])).
% 0.85/1.04  
% 0.85/1.04  fof(f35,plain,(
% 0.85/1.04    ( ! [X2,X0,X3,X1] : (X1 = X3 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.85/1.04    inference(cnf_transformation,[],[f14])).
% 0.85/1.04  
% 0.85/1.04  fof(f3,axiom,(
% 0.85/1.04    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.85/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.85/1.04  
% 0.85/1.04  fof(f13,plain,(
% 0.85/1.04    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.85/1.04    inference(ennf_transformation,[],[f3])).
% 0.85/1.04  
% 0.85/1.04  fof(f33,plain,(
% 0.85/1.04    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.85/1.04    inference(cnf_transformation,[],[f13])).
% 0.85/1.04  
% 0.85/1.04  fof(f40,plain,(
% 0.85/1.04    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.85/1.04    inference(cnf_transformation,[],[f24])).
% 0.85/1.04  
% 0.85/1.04  fof(f32,plain,(
% 0.85/1.04    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.85/1.04    inference(cnf_transformation,[],[f23])).
% 0.85/1.04  
% 0.85/1.04  fof(f48,plain,(
% 0.85/1.04    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 0.85/1.04    inference(cnf_transformation,[],[f29])).
% 0.85/1.04  
% 0.85/1.04  cnf(c_10,plain,
% 0.85/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.85/1.04      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 0.85/1.04      | v2_struct_0(X1)
% 0.85/1.04      | ~ v2_pre_topc(X1)
% 0.85/1.04      | ~ l1_pre_topc(X1)
% 0.85/1.04      | k5_tmap_1(X1,X0) = u1_pre_topc(X1) ),
% 0.85/1.04      inference(cnf_transformation,[],[f39]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_2,plain,
% 0.85/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.85/1.04      | r2_hidden(X0,u1_pre_topc(X1))
% 0.85/1.04      | ~ v3_pre_topc(X0,X1)
% 0.85/1.04      | ~ l1_pre_topc(X1) ),
% 0.85/1.04      inference(cnf_transformation,[],[f31]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_14,negated_conjecture,
% 0.85/1.04      ( v3_pre_topc(sK1,sK0)
% 0.85/1.04      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 0.85/1.04      inference(cnf_transformation,[],[f47]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_143,plain,
% 0.85/1.04      ( v3_pre_topc(sK1,sK0)
% 0.85/1.04      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 0.85/1.04      inference(prop_impl,[status(thm)],[c_14]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_299,plain,
% 0.85/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.85/1.04      | r2_hidden(X0,u1_pre_topc(X1))
% 0.85/1.04      | ~ l1_pre_topc(X1)
% 0.85/1.04      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
% 0.85/1.04      | sK1 != X0
% 0.85/1.04      | sK0 != X1 ),
% 0.85/1.04      inference(resolution_lifted,[status(thm)],[c_2,c_143]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_300,plain,
% 0.85/1.04      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.85/1.04      | r2_hidden(sK1,u1_pre_topc(sK0))
% 0.85/1.04      | ~ l1_pre_topc(sK0)
% 0.85/1.04      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 0.85/1.04      inference(unflattening,[status(thm)],[c_299]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_16,negated_conjecture,
% 0.85/1.04      ( l1_pre_topc(sK0) ),
% 0.85/1.04      inference(cnf_transformation,[],[f45]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_15,negated_conjecture,
% 0.85/1.04      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 0.85/1.04      inference(cnf_transformation,[],[f46]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_302,plain,
% 0.85/1.04      ( r2_hidden(sK1,u1_pre_topc(sK0))
% 0.85/1.04      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 0.85/1.04      inference(global_propositional_subsumption,
% 0.85/1.04                [status(thm)],
% 0.85/1.04                [c_300,c_16,c_15]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_348,plain,
% 0.85/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.85/1.04      | v2_struct_0(X1)
% 0.85/1.04      | ~ v2_pre_topc(X1)
% 0.85/1.04      | ~ l1_pre_topc(X1)
% 0.85/1.04      | k5_tmap_1(X1,X0) = u1_pre_topc(X1)
% 0.85/1.04      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
% 0.85/1.04      | u1_pre_topc(X1) != u1_pre_topc(sK0)
% 0.85/1.04      | sK1 != X0 ),
% 0.85/1.04      inference(resolution_lifted,[status(thm)],[c_10,c_302]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_349,plain,
% 0.85/1.04      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
% 0.85/1.04      | v2_struct_0(X0)
% 0.85/1.04      | ~ v2_pre_topc(X0)
% 0.85/1.04      | ~ l1_pre_topc(X0)
% 0.85/1.04      | k5_tmap_1(X0,sK1) = u1_pre_topc(X0)
% 0.85/1.04      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
% 0.85/1.04      | u1_pre_topc(X0) != u1_pre_topc(sK0) ),
% 0.85/1.04      inference(unflattening,[status(thm)],[c_348]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_18,negated_conjecture,
% 0.85/1.04      ( ~ v2_struct_0(sK0) ),
% 0.85/1.04      inference(cnf_transformation,[],[f43]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_391,plain,
% 0.85/1.04      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
% 0.85/1.04      | ~ v2_pre_topc(X0)
% 0.85/1.04      | ~ l1_pre_topc(X0)
% 0.85/1.04      | k5_tmap_1(X0,sK1) = u1_pre_topc(X0)
% 0.85/1.04      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
% 0.85/1.04      | u1_pre_topc(X0) != u1_pre_topc(sK0)
% 0.85/1.04      | sK0 != X0 ),
% 0.85/1.04      inference(resolution_lifted,[status(thm)],[c_349,c_18]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_392,plain,
% 0.85/1.04      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.85/1.04      | ~ v2_pre_topc(sK0)
% 0.85/1.04      | ~ l1_pre_topc(sK0)
% 0.85/1.04      | k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 0.85/1.04      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
% 0.85/1.04      | u1_pre_topc(sK0) != u1_pre_topc(sK0) ),
% 0.85/1.04      inference(unflattening,[status(thm)],[c_391]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_17,negated_conjecture,
% 0.85/1.04      ( v2_pre_topc(sK0) ),
% 0.85/1.04      inference(cnf_transformation,[],[f44]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_394,plain,
% 0.85/1.04      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 0.85/1.04      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
% 0.85/1.04      | u1_pre_topc(sK0) != u1_pre_topc(sK0) ),
% 0.85/1.04      inference(global_propositional_subsumption,
% 0.85/1.04                [status(thm)],
% 0.85/1.04                [c_392,c_18,c_17,c_16,c_15,c_351]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_589,plain,
% 0.85/1.04      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 0.85/1.04      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 0.85/1.04      inference(equality_resolution_simp,[status(thm)],[c_394]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_607,plain,
% 0.85/1.04      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 0.85/1.04      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 0.85/1.04      inference(prop_impl,[status(thm)],[c_589]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_893,plain,
% 0.85/1.04      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 0.85/1.04      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_0,plain,
% 0.85/1.04      ( ~ l1_pre_topc(X0)
% 0.85/1.04      | ~ v1_pre_topc(X0)
% 0.85/1.04      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 0.85/1.04      inference(cnf_transformation,[],[f30]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_8,plain,
% 0.85/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.85/1.04      | v2_struct_0(X1)
% 0.85/1.04      | ~ v2_pre_topc(X1)
% 0.85/1.04      | ~ l1_pre_topc(X1)
% 0.85/1.04      | v1_pre_topc(k6_tmap_1(X1,X0)) ),
% 0.85/1.04      inference(cnf_transformation,[],[f36]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_455,plain,
% 0.85/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.85/1.04      | ~ v2_pre_topc(X1)
% 0.85/1.04      | ~ l1_pre_topc(X1)
% 0.85/1.04      | v1_pre_topc(k6_tmap_1(X1,X0))
% 0.85/1.04      | sK0 != X1 ),
% 0.85/1.04      inference(resolution_lifted,[status(thm)],[c_8,c_18]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_456,plain,
% 0.85/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.85/1.04      | ~ v2_pre_topc(sK0)
% 0.85/1.04      | ~ l1_pre_topc(sK0)
% 0.85/1.04      | v1_pre_topc(k6_tmap_1(sK0,X0)) ),
% 0.85/1.04      inference(unflattening,[status(thm)],[c_455]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_460,plain,
% 0.85/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.85/1.04      | v1_pre_topc(k6_tmap_1(sK0,X0)) ),
% 0.85/1.04      inference(global_propositional_subsumption,
% 0.85/1.04                [status(thm)],
% 0.85/1.04                [c_456,c_17,c_16]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_530,plain,
% 0.85/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.85/1.04      | ~ l1_pre_topc(X1)
% 0.85/1.04      | k6_tmap_1(sK0,X0) != X1
% 0.85/1.04      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X1 ),
% 0.85/1.04      inference(resolution_lifted,[status(thm)],[c_0,c_460]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_531,plain,
% 0.85/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.85/1.04      | ~ l1_pre_topc(k6_tmap_1(sK0,X0))
% 0.85/1.04      | g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0)),u1_pre_topc(k6_tmap_1(sK0,X0))) = k6_tmap_1(sK0,X0) ),
% 0.85/1.04      inference(unflattening,[status(thm)],[c_530]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_6,plain,
% 0.85/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.85/1.04      | v2_struct_0(X1)
% 0.85/1.04      | ~ v2_pre_topc(X1)
% 0.85/1.04      | ~ l1_pre_topc(X1)
% 0.85/1.04      | l1_pre_topc(k6_tmap_1(X1,X0)) ),
% 0.85/1.04      inference(cnf_transformation,[],[f38]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_491,plain,
% 0.85/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.85/1.04      | ~ v2_pre_topc(X1)
% 0.85/1.04      | ~ l1_pre_topc(X1)
% 0.85/1.04      | l1_pre_topc(k6_tmap_1(X1,X0))
% 0.85/1.04      | sK0 != X1 ),
% 0.85/1.04      inference(resolution_lifted,[status(thm)],[c_6,c_18]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_492,plain,
% 0.85/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.85/1.04      | ~ v2_pre_topc(sK0)
% 0.85/1.04      | l1_pre_topc(k6_tmap_1(sK0,X0))
% 0.85/1.04      | ~ l1_pre_topc(sK0) ),
% 0.85/1.04      inference(unflattening,[status(thm)],[c_491]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_496,plain,
% 0.85/1.04      ( l1_pre_topc(k6_tmap_1(sK0,X0))
% 0.85/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 0.85/1.04      inference(global_propositional_subsumption,
% 0.85/1.04                [status(thm)],
% 0.85/1.04                [c_492,c_17,c_16]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_497,plain,
% 0.85/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.85/1.04      | l1_pre_topc(k6_tmap_1(sK0,X0)) ),
% 0.85/1.04      inference(renaming,[status(thm)],[c_496]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_535,plain,
% 0.85/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.85/1.04      | g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0)),u1_pre_topc(k6_tmap_1(sK0,X0))) = k6_tmap_1(sK0,X0) ),
% 0.85/1.04      inference(global_propositional_subsumption,
% 0.85/1.04                [status(thm)],
% 0.85/1.04                [c_531,c_17,c_16,c_492]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_890,plain,
% 0.85/1.04      ( g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0)),u1_pre_topc(k6_tmap_1(sK0,X0))) = k6_tmap_1(sK0,X0)
% 0.85/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 0.85/1.04      inference(predicate_to_equality,[status(thm)],[c_535]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_1496,plain,
% 0.85/1.04      ( g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1))) = k6_tmap_1(sK0,sK1) ),
% 0.85/1.04      inference(superposition,[status(thm)],[c_893,c_890]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_12,plain,
% 0.85/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.85/1.04      | v2_struct_0(X1)
% 0.85/1.04      | ~ v2_pre_topc(X1)
% 0.85/1.04      | ~ l1_pre_topc(X1)
% 0.85/1.04      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 0.85/1.04      inference(cnf_transformation,[],[f41]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_419,plain,
% 0.85/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.85/1.04      | ~ v2_pre_topc(X1)
% 0.85/1.04      | ~ l1_pre_topc(X1)
% 0.85/1.04      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
% 0.85/1.04      | sK0 != X1 ),
% 0.85/1.04      inference(resolution_lifted,[status(thm)],[c_12,c_18]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_420,plain,
% 0.85/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.85/1.04      | ~ v2_pre_topc(sK0)
% 0.85/1.04      | ~ l1_pre_topc(sK0)
% 0.85/1.04      | u1_struct_0(k6_tmap_1(sK0,X0)) = u1_struct_0(sK0) ),
% 0.85/1.04      inference(unflattening,[status(thm)],[c_419]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_424,plain,
% 0.85/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.85/1.04      | u1_struct_0(k6_tmap_1(sK0,X0)) = u1_struct_0(sK0) ),
% 0.85/1.04      inference(global_propositional_subsumption,
% 0.85/1.04                [status(thm)],
% 0.85/1.04                [c_420,c_17,c_16]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_892,plain,
% 0.85/1.04      ( u1_struct_0(k6_tmap_1(sK0,X0)) = u1_struct_0(sK0)
% 0.85/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 0.85/1.04      inference(predicate_to_equality,[status(thm)],[c_424]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_994,plain,
% 0.85/1.04      ( u1_struct_0(k6_tmap_1(sK0,sK1)) = u1_struct_0(sK0) ),
% 0.85/1.04      inference(superposition,[status(thm)],[c_893,c_892]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_11,plain,
% 0.85/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.85/1.04      | v2_struct_0(X1)
% 0.85/1.04      | ~ v2_pre_topc(X1)
% 0.85/1.04      | ~ l1_pre_topc(X1)
% 0.85/1.04      | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
% 0.85/1.04      inference(cnf_transformation,[],[f42]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_437,plain,
% 0.85/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.85/1.04      | ~ v2_pre_topc(X1)
% 0.85/1.04      | ~ l1_pre_topc(X1)
% 0.85/1.04      | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0)
% 0.85/1.04      | sK0 != X1 ),
% 0.85/1.04      inference(resolution_lifted,[status(thm)],[c_11,c_18]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_438,plain,
% 0.85/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.85/1.04      | ~ v2_pre_topc(sK0)
% 0.85/1.04      | ~ l1_pre_topc(sK0)
% 0.85/1.04      | u1_pre_topc(k6_tmap_1(sK0,X0)) = k5_tmap_1(sK0,X0) ),
% 0.85/1.04      inference(unflattening,[status(thm)],[c_437]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_442,plain,
% 0.85/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.85/1.04      | u1_pre_topc(k6_tmap_1(sK0,X0)) = k5_tmap_1(sK0,X0) ),
% 0.85/1.04      inference(global_propositional_subsumption,
% 0.85/1.04                [status(thm)],
% 0.85/1.04                [c_438,c_17,c_16]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_891,plain,
% 0.85/1.04      ( u1_pre_topc(k6_tmap_1(sK0,X0)) = k5_tmap_1(sK0,X0)
% 0.85/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 0.85/1.04      inference(predicate_to_equality,[status(thm)],[c_442]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_1092,plain,
% 0.85/1.04      ( u1_pre_topc(k6_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,sK1) ),
% 0.85/1.04      inference(superposition,[status(thm)],[c_893,c_891]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_1497,plain,
% 0.85/1.04      ( g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) = k6_tmap_1(sK0,sK1) ),
% 0.85/1.04      inference(light_normalisation,[status(thm)],[c_1496,c_994,c_1092]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_4,plain,
% 0.85/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 0.85/1.04      | X2 = X0
% 0.85/1.04      | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
% 0.85/1.04      inference(cnf_transformation,[],[f35]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_895,plain,
% 0.85/1.04      ( X0 = X1
% 0.85/1.04      | g1_pre_topc(X2,X0) != g1_pre_topc(X3,X1)
% 0.85/1.04      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) != iProver_top ),
% 0.85/1.04      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_1501,plain,
% 0.85/1.04      ( k5_tmap_1(sK0,sK1) = X0
% 0.85/1.04      | g1_pre_topc(X1,X0) != k6_tmap_1(sK0,sK1)
% 0.85/1.04      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 0.85/1.04      inference(superposition,[status(thm)],[c_1497,c_895]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_22,plain,
% 0.85/1.04      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 0.85/1.04      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_3,plain,
% 0.85/1.04      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 0.85/1.04      | ~ l1_pre_topc(X0) ),
% 0.85/1.04      inference(cnf_transformation,[],[f33]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_558,plain,
% 0.85/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.85/1.04      | m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 0.85/1.04      | k6_tmap_1(sK0,X0) != X1 ),
% 0.85/1.04      inference(resolution_lifted,[status(thm)],[c_3,c_497]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_559,plain,
% 0.85/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.85/1.04      | m1_subset_1(u1_pre_topc(k6_tmap_1(sK0,X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X0))))) ),
% 0.85/1.04      inference(unflattening,[status(thm)],[c_558]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_888,plain,
% 0.85/1.04      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 0.85/1.04      | m1_subset_1(u1_pre_topc(k6_tmap_1(sK0,X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X0))))) = iProver_top ),
% 0.85/1.04      inference(predicate_to_equality,[status(thm)],[c_559]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_1177,plain,
% 0.85/1.04      ( m1_subset_1(u1_pre_topc(k6_tmap_1(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 0.85/1.04      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 0.85/1.04      inference(superposition,[status(thm)],[c_994,c_888]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_1180,plain,
% 0.85/1.04      ( m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 0.85/1.04      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 0.85/1.04      inference(light_normalisation,[status(thm)],[c_1177,c_1092]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_1502,plain,
% 0.85/1.04      ( k5_tmap_1(sK0,sK1) = X0
% 0.85/1.04      | g1_pre_topc(X1,X0) != k6_tmap_1(sK0,sK1)
% 0.85/1.04      | m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 0.85/1.04      inference(superposition,[status(thm)],[c_1497,c_895]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_1625,plain,
% 0.85/1.04      ( g1_pre_topc(X1,X0) != k6_tmap_1(sK0,sK1) | k5_tmap_1(sK0,sK1) = X0 ),
% 0.85/1.04      inference(global_propositional_subsumption,
% 0.85/1.04                [status(thm)],
% 0.85/1.04                [c_1501,c_22,c_1180,c_1502]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_1626,plain,
% 0.85/1.04      ( k5_tmap_1(sK0,sK1) = X0 | g1_pre_topc(X1,X0) != k6_tmap_1(sK0,sK1) ),
% 0.85/1.04      inference(renaming,[status(thm)],[c_1625]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_1630,plain,
% 0.85/1.04      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0) ),
% 0.85/1.04      inference(superposition,[status(thm)],[c_607,c_1626]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_1691,plain,
% 0.85/1.04      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 0.85/1.04      inference(demodulation,[status(thm)],[c_1630,c_1497]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_9,plain,
% 0.85/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.85/1.04      | r2_hidden(X0,u1_pre_topc(X1))
% 0.85/1.04      | v2_struct_0(X1)
% 0.85/1.04      | ~ v2_pre_topc(X1)
% 0.85/1.04      | ~ l1_pre_topc(X1)
% 0.85/1.04      | k5_tmap_1(X1,X0) != u1_pre_topc(X1) ),
% 0.85/1.04      inference(cnf_transformation,[],[f40]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_1,plain,
% 0.85/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.85/1.04      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 0.85/1.04      | v3_pre_topc(X0,X1)
% 0.85/1.04      | ~ l1_pre_topc(X1) ),
% 0.85/1.04      inference(cnf_transformation,[],[f32]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_13,negated_conjecture,
% 0.85/1.04      ( ~ v3_pre_topc(sK1,sK0)
% 0.85/1.04      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 0.85/1.04      inference(cnf_transformation,[],[f48]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_141,plain,
% 0.85/1.04      ( ~ v3_pre_topc(sK1,sK0)
% 0.85/1.04      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 0.85/1.04      inference(prop_impl,[status(thm)],[c_13]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_285,plain,
% 0.85/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.85/1.04      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 0.85/1.04      | ~ l1_pre_topc(X1)
% 0.85/1.04      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
% 0.85/1.04      | sK1 != X0
% 0.85/1.04      | sK0 != X1 ),
% 0.85/1.04      inference(resolution_lifted,[status(thm)],[c_1,c_141]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_286,plain,
% 0.85/1.04      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.85/1.04      | ~ r2_hidden(sK1,u1_pre_topc(sK0))
% 0.85/1.04      | ~ l1_pre_topc(sK0)
% 0.85/1.04      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 0.85/1.04      inference(unflattening,[status(thm)],[c_285]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_288,plain,
% 0.85/1.04      ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
% 0.85/1.04      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 0.85/1.04      inference(global_propositional_subsumption,
% 0.85/1.04                [status(thm)],
% 0.85/1.04                [c_286,c_16,c_15]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_321,plain,
% 0.85/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.85/1.04      | v2_struct_0(X1)
% 0.85/1.04      | ~ v2_pre_topc(X1)
% 0.85/1.04      | ~ l1_pre_topc(X1)
% 0.85/1.04      | k5_tmap_1(X1,X0) != u1_pre_topc(X1)
% 0.85/1.04      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
% 0.85/1.04      | u1_pre_topc(X1) != u1_pre_topc(sK0)
% 0.85/1.04      | sK1 != X0 ),
% 0.85/1.04      inference(resolution_lifted,[status(thm)],[c_9,c_288]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_322,plain,
% 0.85/1.04      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
% 0.85/1.04      | v2_struct_0(X0)
% 0.85/1.04      | ~ v2_pre_topc(X0)
% 0.85/1.04      | ~ l1_pre_topc(X0)
% 0.85/1.04      | k5_tmap_1(X0,sK1) != u1_pre_topc(X0)
% 0.85/1.04      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
% 0.85/1.04      | u1_pre_topc(X0) != u1_pre_topc(sK0) ),
% 0.85/1.04      inference(unflattening,[status(thm)],[c_321]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_405,plain,
% 0.85/1.04      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
% 0.85/1.04      | ~ v2_pre_topc(X0)
% 0.85/1.04      | ~ l1_pre_topc(X0)
% 0.85/1.04      | k5_tmap_1(X0,sK1) != u1_pre_topc(X0)
% 0.85/1.04      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
% 0.85/1.04      | u1_pre_topc(X0) != u1_pre_topc(sK0)
% 0.85/1.04      | sK0 != X0 ),
% 0.85/1.04      inference(resolution_lifted,[status(thm)],[c_322,c_18]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_406,plain,
% 0.85/1.04      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.85/1.04      | ~ v2_pre_topc(sK0)
% 0.85/1.04      | ~ l1_pre_topc(sK0)
% 0.85/1.04      | k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0)
% 0.85/1.04      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
% 0.85/1.04      | u1_pre_topc(sK0) != u1_pre_topc(sK0) ),
% 0.85/1.04      inference(unflattening,[status(thm)],[c_405]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_408,plain,
% 0.85/1.04      ( k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0)
% 0.85/1.04      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
% 0.85/1.04      | u1_pre_topc(sK0) != u1_pre_topc(sK0) ),
% 0.85/1.04      inference(global_propositional_subsumption,
% 0.85/1.04                [status(thm)],
% 0.85/1.04                [c_406,c_18,c_17,c_16,c_15,c_324]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_588,plain,
% 0.85/1.04      ( k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0)
% 0.85/1.04      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 0.85/1.04      inference(equality_resolution_simp,[status(thm)],[c_408]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_605,plain,
% 0.85/1.04      ( k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0)
% 0.85/1.04      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 0.85/1.04      inference(prop_impl,[status(thm)],[c_588]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_1692,plain,
% 0.85/1.04      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
% 0.85/1.04      | u1_pre_topc(sK0) != u1_pre_topc(sK0) ),
% 0.85/1.04      inference(demodulation,[status(thm)],[c_1630,c_605]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_1697,plain,
% 0.85/1.04      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 0.85/1.04      inference(equality_resolution_simp,[status(thm)],[c_1692]) ).
% 0.85/1.04  
% 0.85/1.04  cnf(c_1701,plain,
% 0.85/1.04      ( $false ),
% 0.85/1.04      inference(forward_subsumption_resolution,[status(thm)],[c_1691,c_1697]) ).
% 0.85/1.04  
% 0.85/1.04  
% 0.85/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 0.85/1.04  
% 0.85/1.04  ------                               Statistics
% 0.85/1.04  
% 0.85/1.04  ------ General
% 0.85/1.04  
% 0.85/1.04  abstr_ref_over_cycles:                  0
% 0.85/1.04  abstr_ref_under_cycles:                 0
% 0.85/1.04  gc_basic_clause_elim:                   0
% 0.85/1.04  forced_gc_time:                         0
% 0.85/1.04  parsing_time:                           0.01
% 0.85/1.04  unif_index_cands_time:                  0.
% 0.85/1.04  unif_index_add_time:                    0.
% 0.85/1.04  orderings_time:                         0.
% 0.85/1.04  out_proof_time:                         0.021
% 0.85/1.04  total_time:                             0.099
% 0.85/1.04  num_of_symbols:                         46
% 0.85/1.04  num_of_terms:                           1536
% 0.85/1.04  
% 0.85/1.04  ------ Preprocessing
% 0.85/1.04  
% 0.85/1.04  num_of_splits:                          0
% 0.85/1.04  num_of_split_atoms:                     0
% 0.85/1.04  num_of_reused_defs:                     0
% 0.85/1.04  num_eq_ax_congr_red:                    3
% 0.85/1.04  num_of_sem_filtered_clauses:            1
% 0.85/1.04  num_of_subtypes:                        0
% 0.85/1.04  monotx_restored_types:                  0
% 0.85/1.04  sat_num_of_epr_types:                   0
% 0.85/1.04  sat_num_of_non_cyclic_types:            0
% 0.85/1.04  sat_guarded_non_collapsed_types:        0
% 0.85/1.04  num_pure_diseq_elim:                    0
% 0.85/1.04  simp_replaced_by:                       0
% 0.85/1.04  res_preprocessed:                       68
% 0.85/1.04  prep_upred:                             0
% 0.85/1.04  prep_unflattend:                        17
% 0.85/1.04  smt_new_axioms:                         0
% 0.85/1.04  pred_elim_cands:                        1
% 0.85/1.04  pred_elim:                              6
% 0.85/1.04  pred_elim_cl:                           9
% 0.85/1.04  pred_elim_cycles:                       9
% 0.85/1.04  merged_defs:                            8
% 0.85/1.04  merged_defs_ncl:                        0
% 0.85/1.04  bin_hyper_res:                          8
% 0.85/1.04  prep_cycles:                            4
% 0.85/1.04  pred_elim_time:                         0.006
% 0.85/1.04  splitting_time:                         0.
% 0.85/1.04  sem_filter_time:                        0.
% 0.85/1.04  monotx_time:                            0.
% 0.85/1.04  subtype_inf_time:                       0.
% 0.85/1.04  
% 0.85/1.04  ------ Problem properties
% 0.85/1.04  
% 0.85/1.04  clauses:                                10
% 0.85/1.04  conjectures:                            1
% 0.85/1.04  epr:                                    0
% 0.85/1.04  horn:                                   9
% 0.85/1.04  ground:                                 4
% 0.85/1.04  unary:                                  2
% 0.85/1.04  binary:                                 6
% 0.85/1.04  lits:                                   20
% 0.85/1.04  lits_eq:                                11
% 0.85/1.04  fd_pure:                                0
% 0.85/1.04  fd_pseudo:                              0
% 0.85/1.04  fd_cond:                                0
% 0.85/1.04  fd_pseudo_cond:                         2
% 0.85/1.04  ac_symbols:                             0
% 0.85/1.04  
% 0.85/1.04  ------ Propositional Solver
% 0.85/1.04  
% 0.85/1.04  prop_solver_calls:                      26
% 0.85/1.04  prop_fast_solver_calls:                 472
% 0.85/1.04  smt_solver_calls:                       0
% 0.85/1.04  smt_fast_solver_calls:                  0
% 0.85/1.04  prop_num_of_clauses:                    580
% 0.85/1.04  prop_preprocess_simplified:             2185
% 0.85/1.04  prop_fo_subsumed:                       25
% 0.85/1.04  prop_solver_time:                       0.
% 0.85/1.04  smt_solver_time:                        0.
% 0.85/1.04  smt_fast_solver_time:                   0.
% 0.85/1.04  prop_fast_solver_time:                  0.
% 0.85/1.04  prop_unsat_core_time:                   0.
% 0.85/1.04  
% 0.85/1.04  ------ QBF
% 0.85/1.04  
% 0.85/1.04  qbf_q_res:                              0
% 0.85/1.04  qbf_num_tautologies:                    0
% 0.85/1.04  qbf_prep_cycles:                        0
% 0.85/1.04  
% 0.85/1.04  ------ BMC1
% 0.85/1.04  
% 0.85/1.04  bmc1_current_bound:                     -1
% 0.85/1.04  bmc1_last_solved_bound:                 -1
% 0.85/1.04  bmc1_unsat_core_size:                   -1
% 0.85/1.04  bmc1_unsat_core_parents_size:           -1
% 0.85/1.04  bmc1_merge_next_fun:                    0
% 0.85/1.04  bmc1_unsat_core_clauses_time:           0.
% 0.85/1.04  
% 0.85/1.04  ------ Instantiation
% 0.85/1.04  
% 0.85/1.04  inst_num_of_clauses:                    158
% 0.85/1.04  inst_num_in_passive:                    67
% 0.85/1.04  inst_num_in_active:                     87
% 0.85/1.04  inst_num_in_unprocessed:                4
% 0.85/1.04  inst_num_of_loops:                      90
% 0.85/1.04  inst_num_of_learning_restarts:          0
% 0.85/1.04  inst_num_moves_active_passive:          0
% 0.85/1.04  inst_lit_activity:                      0
% 0.85/1.04  inst_lit_activity_moves:                0
% 0.85/1.04  inst_num_tautologies:                   0
% 0.85/1.04  inst_num_prop_implied:                  0
% 0.85/1.04  inst_num_existing_simplified:           0
% 0.85/1.04  inst_num_eq_res_simplified:             0
% 0.85/1.04  inst_num_child_elim:                    0
% 0.85/1.04  inst_num_of_dismatching_blockings:      16
% 0.85/1.04  inst_num_of_non_proper_insts:           147
% 0.85/1.04  inst_num_of_duplicates:                 0
% 0.85/1.04  inst_inst_num_from_inst_to_res:         0
% 0.85/1.04  inst_dismatching_checking_time:         0.
% 0.85/1.04  
% 0.85/1.04  ------ Resolution
% 0.85/1.04  
% 0.85/1.04  res_num_of_clauses:                     0
% 0.85/1.04  res_num_in_passive:                     0
% 0.85/1.04  res_num_in_active:                      0
% 0.85/1.04  res_num_of_loops:                       72
% 0.85/1.04  res_forward_subset_subsumed:            17
% 0.85/1.04  res_backward_subset_subsumed:           0
% 0.85/1.04  res_forward_subsumed:                   0
% 0.85/1.04  res_backward_subsumed:                  0
% 0.85/1.04  res_forward_subsumption_resolution:     0
% 0.85/1.04  res_backward_subsumption_resolution:    0
% 0.85/1.04  res_clause_to_clause_subsumption:       33
% 0.85/1.04  res_orphan_elimination:                 0
% 0.85/1.04  res_tautology_del:                      39
% 0.85/1.04  res_num_eq_res_simplified:              2
% 0.85/1.04  res_num_sel_changes:                    0
% 0.85/1.04  res_moves_from_active_to_pass:          0
% 0.85/1.04  
% 0.85/1.04  ------ Superposition
% 0.85/1.04  
% 0.85/1.04  sup_time_total:                         0.
% 0.85/1.04  sup_time_generating:                    0.
% 0.85/1.04  sup_time_sim_full:                      0.
% 0.85/1.04  sup_time_sim_immed:                     0.
% 0.85/1.04  
% 0.85/1.04  sup_num_of_clauses:                     13
% 0.85/1.04  sup_num_in_active:                      10
% 0.85/1.04  sup_num_in_passive:                     3
% 0.85/1.04  sup_num_of_loops:                       16
% 0.85/1.04  sup_fw_superposition:                   13
% 0.85/1.04  sup_bw_superposition:                   5
% 0.85/1.04  sup_immediate_simplified:               3
% 0.85/1.04  sup_given_eliminated:                   1
% 0.85/1.04  comparisons_done:                       0
% 0.85/1.04  comparisons_avoided:                    3
% 0.85/1.04  
% 0.85/1.04  ------ Simplifications
% 0.85/1.04  
% 0.85/1.04  
% 0.85/1.04  sim_fw_subset_subsumed:                 0
% 0.85/1.04  sim_bw_subset_subsumed:                 7
% 0.85/1.04  sim_fw_subsumed:                        0
% 0.85/1.04  sim_bw_subsumed:                        0
% 0.85/1.04  sim_fw_subsumption_res:                 1
% 0.85/1.04  sim_bw_subsumption_res:                 0
% 0.85/1.04  sim_tautology_del:                      1
% 0.85/1.04  sim_eq_tautology_del:                   5
% 0.85/1.04  sim_eq_res_simp:                        1
% 0.85/1.04  sim_fw_demodulated:                     0
% 0.85/1.04  sim_bw_demodulated:                     5
% 0.85/1.04  sim_light_normalised:                   3
% 0.85/1.04  sim_joinable_taut:                      0
% 0.85/1.04  sim_joinable_simp:                      0
% 0.85/1.04  sim_ac_normalised:                      0
% 0.85/1.04  sim_smt_subsumption:                    0
% 0.85/1.04  
%------------------------------------------------------------------------------
