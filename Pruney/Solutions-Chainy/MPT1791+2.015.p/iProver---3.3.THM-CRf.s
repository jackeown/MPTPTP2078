%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:52 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_399)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f42,plain,(
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

fof(f41,plain,
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

fof(f43,plain,
    ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).

fof(f64,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f65,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f66,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f59,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f68,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f67,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & v1_tops_2(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            | ~ v1_tops_2(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & v1_tops_2(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            | ~ v1_tops_2(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_tops_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f61,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ~ r1_tarski(X1,u1_pre_topc(X0)) )
            & ( r1_tarski(X1,u1_pre_topc(X0))
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,u1_pre_topc(X0))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f62,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f58,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f71,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ r1_tarski(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
      | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f55,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | u1_pre_topc(X0) != k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f69,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k5_tmap_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_557,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k5_tmap_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_25])).

cnf(c_558,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k5_tmap_1(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_557])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_562,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k5_tmap_1(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_558,c_24,c_23])).

cnf(c_1459,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k5_tmap_1(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_562])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) = u1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_21,negated_conjecture,
    ( v3_pre_topc(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_197,plain,
    ( v3_pre_topc(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_21])).

cnf(c_347,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_197])).

cnf(c_348,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_347])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_350,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_348,c_23,c_22])).

cnf(c_396,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) = u1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | u1_pre_topc(X1) != u1_pre_topc(sK0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_350])).

cnf(c_397,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k5_tmap_1(X0,sK1) = u1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | u1_pre_topc(X0) != u1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_439,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k5_tmap_1(X0,sK1) = u1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | u1_pre_topc(X0) != u1_pre_topc(sK0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_397,c_25])).

cnf(c_440,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | u1_pre_topc(sK0) != u1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_439])).

cnf(c_442,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | u1_pre_topc(sK0) != u1_pre_topc(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_440,c_25,c_24,c_23,c_22,c_399])).

cnf(c_827,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_442])).

cnf(c_858,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_827])).

cnf(c_10,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_593,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_25])).

cnf(c_594,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_tops_2(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_593])).

cnf(c_598,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_tops_2(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_594,c_24,c_23])).

cnf(c_1457,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
    | v1_tops_2(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_598])).

cnf(c_2078,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | v1_tops_2(X0,k6_tmap_1(sK0,sK1)) = iProver_top
    | v1_tops_2(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_858,c_1457])).

cnf(c_2397,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | v1_tops_2(k5_tmap_1(sK0,X0),k6_tmap_1(sK0,sK1)) = iProver_top
    | v1_tops_2(k5_tmap_1(sK0,X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1459,c_2078])).

cnf(c_1465,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_485,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_25])).

cnf(c_486,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(k6_tmap_1(sK0,X0)) = u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_485])).

cnf(c_490,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(k6_tmap_1(sK0,X0)) = u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_486,c_24,c_23])).

cnf(c_1462,plain,
    ( u1_struct_0(k6_tmap_1(sK0,X0)) = u1_struct_0(sK0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_490])).

cnf(c_1647,plain,
    ( u1_struct_0(k6_tmap_1(sK0,sK1)) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1465,c_1462])).

cnf(c_6,plain,
    ( ~ v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r1_tarski(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1466,plain,
    ( v1_tops_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
    | r1_tarski(X0,u1_pre_topc(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2264,plain,
    ( v1_tops_2(X0,k6_tmap_1(sK0,sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(X0,u1_pre_topc(k6_tmap_1(sK0,sK1))) = iProver_top
    | l1_pre_topc(k6_tmap_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1647,c_1466])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_503,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_504,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | u1_pre_topc(k6_tmap_1(sK0,X0)) = k5_tmap_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_503])).

cnf(c_508,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_pre_topc(k6_tmap_1(sK0,X0)) = k5_tmap_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_504,c_24,c_23])).

cnf(c_1461,plain,
    ( u1_pre_topc(k6_tmap_1(sK0,X0)) = k5_tmap_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_508])).

cnf(c_1680,plain,
    ( u1_pre_topc(k6_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1465,c_1461])).

cnf(c_2269,plain,
    ( v1_tops_2(X0,k6_tmap_1(sK0,sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(X0,k5_tmap_1(sK0,sK1)) = iProver_top
    | l1_pre_topc(k6_tmap_1(sK0,sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2264,c_1680])).

cnf(c_29,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_539,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_25])).

cnf(c_540,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | l1_pre_topc(k6_tmap_1(sK0,X0))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_539])).

cnf(c_544,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_540,c_24,c_23])).

cnf(c_545,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | l1_pre_topc(k6_tmap_1(sK0,X0)) ),
    inference(renaming,[status(thm)],[c_544])).

cnf(c_1596,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_545])).

cnf(c_1597,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1596])).

cnf(c_2588,plain,
    ( r1_tarski(X0,k5_tmap_1(sK0,sK1)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | v1_tops_2(X0,k6_tmap_1(sK0,sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2269,c_29,c_1597])).

cnf(c_2589,plain,
    ( v1_tops_2(X0,k6_tmap_1(sK0,sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(X0,k5_tmap_1(sK0,sK1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2588])).

cnf(c_2597,plain,
    ( v1_tops_2(k5_tmap_1(sK0,X0),k6_tmap_1(sK0,sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k5_tmap_1(sK0,X0),k5_tmap_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1459,c_2589])).

cnf(c_2986,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | v1_tops_2(k5_tmap_1(sK0,X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k5_tmap_1(sK0,X0),k5_tmap_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2397,c_2597])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1468,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5,plain,
    ( v1_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1467,plain,
    ( v1_tops_2(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
    | r1_tarski(X0,u1_pre_topc(X1)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2308,plain,
    ( v1_tops_2(X0,k6_tmap_1(sK0,sK1)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(X0,u1_pre_topc(k6_tmap_1(sK0,sK1))) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1647,c_1467])).

cnf(c_2313,plain,
    ( v1_tops_2(X0,k6_tmap_1(sK0,sK1)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(X0,k5_tmap_1(sK0,sK1)) != iProver_top
    | l1_pre_topc(k6_tmap_1(sK0,sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2308,c_1680])).

cnf(c_2711,plain,
    ( r1_tarski(X0,k5_tmap_1(sK0,sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | v1_tops_2(X0,k6_tmap_1(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2313,c_29,c_1597])).

cnf(c_2712,plain,
    ( v1_tops_2(X0,k6_tmap_1(sK0,sK1)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(X0,k5_tmap_1(sK0,sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2711])).

cnf(c_2720,plain,
    ( v1_tops_2(k5_tmap_1(sK0,X0),k6_tmap_1(sK0,sK1)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k5_tmap_1(sK0,X0),k5_tmap_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1459,c_2712])).

cnf(c_2728,plain,
    ( v1_tops_2(k5_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_2720])).

cnf(c_3148,plain,
    ( v1_tops_2(k5_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2728,c_29])).

cnf(c_8,plain,
    ( v1_tops_2(X0,X1)
    | ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_635,plain,
    ( v1_tops_2(X0,X1)
    | ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_25])).

cnf(c_636,plain,
    ( ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_tops_2(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_635])).

cnf(c_640,plain,
    ( ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_tops_2(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_636,c_24,c_23])).

cnf(c_1455,plain,
    ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | v1_tops_2(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_640])).

cnf(c_2176,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | v1_tops_2(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_858,c_1455])).

cnf(c_2181,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
    | v1_tops_2(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2176,c_1647])).

cnf(c_2885,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | v1_tops_2(X0,k6_tmap_1(sK0,sK1)) != iProver_top
    | v1_tops_2(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_858,c_2181])).

cnf(c_2995,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | v1_tops_2(k5_tmap_1(sK0,X0),k6_tmap_1(sK0,sK1)) != iProver_top
    | v1_tops_2(k5_tmap_1(sK0,X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1459,c_2885])).

cnf(c_3159,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | v1_tops_2(k5_tmap_1(sK0,sK1),sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3148,c_2995])).

cnf(c_28,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_84,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_88,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1030,plain,
    ( X0 != X1
    | u1_pre_topc(X0) = u1_pre_topc(X1) ),
    theory(equality)).

cnf(c_1040,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(sK0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1030])).

cnf(c_1599,plain,
    ( m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_562])).

cnf(c_1600,plain,
    ( m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1599])).

cnf(c_1629,plain,
    ( r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1631,plain,
    ( r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1629])).

cnf(c_1633,plain,
    ( r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1631])).

cnf(c_1029,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1624,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,u1_pre_topc(X3))
    | X2 != X0
    | u1_pre_topc(X3) != X1 ),
    inference(instantiation,[status(thm)],[c_1029])).

cnf(c_1685,plain,
    ( ~ r1_tarski(X0,u1_pre_topc(X1))
    | r1_tarski(X2,u1_pre_topc(X1))
    | X2 != X0
    | u1_pre_topc(X1) != u1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_1624])).

cnf(c_1898,plain,
    ( r1_tarski(X0,u1_pre_topc(X1))
    | ~ r1_tarski(u1_pre_topc(X1),u1_pre_topc(X1))
    | X0 != u1_pre_topc(X1)
    | u1_pre_topc(X1) != u1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_1685])).

cnf(c_3219,plain,
    ( r1_tarski(k5_tmap_1(sK0,sK1),u1_pre_topc(sK0))
    | ~ r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK0))
    | k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0)
    | u1_pre_topc(sK0) != u1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1898])).

cnf(c_3222,plain,
    ( k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0)
    | u1_pre_topc(sK0) != u1_pre_topc(sK0)
    | r1_tarski(k5_tmap_1(sK0,sK1),u1_pre_topc(sK0)) = iProver_top
    | r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3219])).

cnf(c_3390,plain,
    ( v1_tops_2(k5_tmap_1(sK0,sK1),X0)
    | ~ m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ r1_tarski(k5_tmap_1(sK0,sK1),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3391,plain,
    ( v1_tops_2(k5_tmap_1(sK0,sK1),X0) = iProver_top
    | m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
    | r1_tarski(k5_tmap_1(sK0,sK1),u1_pre_topc(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3390])).

cnf(c_3393,plain,
    ( v1_tops_2(k5_tmap_1(sK0,sK1),sK0) = iProver_top
    | m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(k5_tmap_1(sK0,sK1),u1_pre_topc(sK0)) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3391])).

cnf(c_3622,plain,
    ( v1_tops_2(k5_tmap_1(sK0,sK1),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3159,c_28,c_29,c_84,c_88,c_1040,c_1600,c_1633,c_3222,c_3393])).

cnf(c_2262,plain,
    ( v1_tops_2(k5_tmap_1(sK0,X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k5_tmap_1(sK0,X0),u1_pre_topc(sK0)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1459,c_1466])).

cnf(c_2470,plain,
    ( r1_tarski(k5_tmap_1(sK0,X0),u1_pre_topc(sK0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v1_tops_2(k5_tmap_1(sK0,X0),sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2262,c_28])).

cnf(c_2471,plain,
    ( v1_tops_2(k5_tmap_1(sK0,X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k5_tmap_1(sK0,X0),u1_pre_topc(sK0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2470])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(u1_pre_topc(X1),k5_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_467,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(u1_pre_topc(X1),k5_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_25])).

cnf(c_468,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(u1_pre_topc(sK0),k5_tmap_1(sK0,X0))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_467])).

cnf(c_472,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(u1_pre_topc(sK0),k5_tmap_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_468,c_24,c_23])).

cnf(c_1463,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(u1_pre_topc(sK0),k5_tmap_1(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_472])).

cnf(c_1469,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1912,plain,
    ( k5_tmap_1(sK0,X0) = u1_pre_topc(sK0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k5_tmap_1(sK0,X0),u1_pre_topc(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1463,c_1469])).

cnf(c_2480,plain,
    ( k5_tmap_1(sK0,X0) = u1_pre_topc(sK0)
    | v1_tops_2(k5_tmap_1(sK0,X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2471,c_1912])).

cnf(c_3627,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3622,c_2480])).

cnf(c_3718,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2986,c_29,c_3627])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X0)) = k6_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_575,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X0)) = k6_tmap_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_25])).

cnf(c_576,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) = k6_tmap_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_575])).

cnf(c_580,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) = k6_tmap_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_576,c_24,c_23])).

cnf(c_1458,plain,
    ( g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) = k6_tmap_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_580])).

cnf(c_1919,plain,
    ( g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) = k6_tmap_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1465,c_1458])).

cnf(c_3727,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_3718,c_1919])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) != u1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_20,negated_conjecture,
    ( ~ v3_pre_topc(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_195,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_20])).

cnf(c_333,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_195])).

cnf(c_334,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_333])).

cnf(c_336,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_334,c_23,c_22])).

cnf(c_369,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) != u1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | u1_pre_topc(X1) != u1_pre_topc(sK0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_336])).

cnf(c_370,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k5_tmap_1(X0,sK1) != u1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | u1_pre_topc(X0) != u1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_369])).

cnf(c_453,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k5_tmap_1(X0,sK1) != u1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | u1_pre_topc(X0) != u1_pre_topc(sK0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_370,c_25])).

cnf(c_454,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | u1_pre_topc(sK0) != u1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_453])).

cnf(c_456,plain,
    ( k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | u1_pre_topc(sK0) != u1_pre_topc(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_454,c_25,c_24,c_23,c_22,c_372])).

cnf(c_826,plain,
    ( k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_456])).

cnf(c_856,plain,
    ( k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_826])).

cnf(c_3728,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | u1_pre_topc(sK0) != u1_pre_topc(sK0) ),
    inference(demodulation,[status(thm)],[c_3718,c_856])).

cnf(c_3732,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_3728])).

cnf(c_3736,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3727,c_3732])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:38:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.53/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/0.98  
% 2.53/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.53/0.98  
% 2.53/0.98  ------  iProver source info
% 2.53/0.98  
% 2.53/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.53/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.53/0.98  git: non_committed_changes: false
% 2.53/0.98  git: last_make_outside_of_git: false
% 2.53/0.98  
% 2.53/0.98  ------ 
% 2.53/0.98  
% 2.53/0.98  ------ Input Options
% 2.53/0.98  
% 2.53/0.98  --out_options                           all
% 2.53/0.98  --tptp_safe_out                         true
% 2.53/0.98  --problem_path                          ""
% 2.53/0.98  --include_path                          ""
% 2.53/0.98  --clausifier                            res/vclausify_rel
% 2.53/0.98  --clausifier_options                    --mode clausify
% 2.53/0.98  --stdin                                 false
% 2.53/0.98  --stats_out                             all
% 2.53/0.98  
% 2.53/0.98  ------ General Options
% 2.53/0.98  
% 2.53/0.98  --fof                                   false
% 2.53/0.98  --time_out_real                         305.
% 2.53/0.98  --time_out_virtual                      -1.
% 2.53/0.98  --symbol_type_check                     false
% 2.53/0.98  --clausify_out                          false
% 2.53/0.98  --sig_cnt_out                           false
% 2.53/0.98  --trig_cnt_out                          false
% 2.53/0.98  --trig_cnt_out_tolerance                1.
% 2.53/0.98  --trig_cnt_out_sk_spl                   false
% 2.53/0.98  --abstr_cl_out                          false
% 2.53/0.98  
% 2.53/0.98  ------ Global Options
% 2.53/0.98  
% 2.53/0.98  --schedule                              default
% 2.53/0.98  --add_important_lit                     false
% 2.53/0.98  --prop_solver_per_cl                    1000
% 2.53/0.98  --min_unsat_core                        false
% 2.53/0.98  --soft_assumptions                      false
% 2.53/0.98  --soft_lemma_size                       3
% 2.53/0.98  --prop_impl_unit_size                   0
% 2.53/0.98  --prop_impl_unit                        []
% 2.53/0.98  --share_sel_clauses                     true
% 2.53/0.98  --reset_solvers                         false
% 2.53/0.98  --bc_imp_inh                            [conj_cone]
% 2.53/0.98  --conj_cone_tolerance                   3.
% 2.53/0.98  --extra_neg_conj                        none
% 2.53/0.98  --large_theory_mode                     true
% 2.53/0.98  --prolific_symb_bound                   200
% 2.53/0.98  --lt_threshold                          2000
% 2.53/0.98  --clause_weak_htbl                      true
% 2.53/0.98  --gc_record_bc_elim                     false
% 2.53/0.98  
% 2.53/0.98  ------ Preprocessing Options
% 2.53/0.98  
% 2.53/0.98  --preprocessing_flag                    true
% 2.53/0.98  --time_out_prep_mult                    0.1
% 2.53/0.98  --splitting_mode                        input
% 2.53/0.98  --splitting_grd                         true
% 2.53/0.98  --splitting_cvd                         false
% 2.53/0.98  --splitting_cvd_svl                     false
% 2.53/0.98  --splitting_nvd                         32
% 2.53/0.98  --sub_typing                            true
% 2.53/0.98  --prep_gs_sim                           true
% 2.53/0.98  --prep_unflatten                        true
% 2.53/0.98  --prep_res_sim                          true
% 2.53/0.98  --prep_upred                            true
% 2.53/0.98  --prep_sem_filter                       exhaustive
% 2.53/0.98  --prep_sem_filter_out                   false
% 2.53/0.98  --pred_elim                             true
% 2.53/0.98  --res_sim_input                         true
% 2.53/0.98  --eq_ax_congr_red                       true
% 2.53/0.98  --pure_diseq_elim                       true
% 2.53/0.98  --brand_transform                       false
% 2.53/0.98  --non_eq_to_eq                          false
% 2.53/0.98  --prep_def_merge                        true
% 2.53/0.98  --prep_def_merge_prop_impl              false
% 2.53/0.98  --prep_def_merge_mbd                    true
% 2.53/0.98  --prep_def_merge_tr_red                 false
% 2.53/0.98  --prep_def_merge_tr_cl                  false
% 2.53/0.98  --smt_preprocessing                     true
% 2.53/0.98  --smt_ac_axioms                         fast
% 2.53/0.98  --preprocessed_out                      false
% 2.53/0.98  --preprocessed_stats                    false
% 2.53/0.98  
% 2.53/0.98  ------ Abstraction refinement Options
% 2.53/0.98  
% 2.53/0.98  --abstr_ref                             []
% 2.53/0.98  --abstr_ref_prep                        false
% 2.53/0.98  --abstr_ref_until_sat                   false
% 2.53/0.98  --abstr_ref_sig_restrict                funpre
% 2.53/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.53/0.98  --abstr_ref_under                       []
% 2.53/0.98  
% 2.53/0.98  ------ SAT Options
% 2.53/0.98  
% 2.53/0.98  --sat_mode                              false
% 2.53/0.98  --sat_fm_restart_options                ""
% 2.53/0.98  --sat_gr_def                            false
% 2.53/0.98  --sat_epr_types                         true
% 2.53/0.98  --sat_non_cyclic_types                  false
% 2.53/0.98  --sat_finite_models                     false
% 2.53/0.98  --sat_fm_lemmas                         false
% 2.53/0.98  --sat_fm_prep                           false
% 2.53/0.98  --sat_fm_uc_incr                        true
% 2.53/0.98  --sat_out_model                         small
% 2.53/0.98  --sat_out_clauses                       false
% 2.53/0.98  
% 2.53/0.98  ------ QBF Options
% 2.53/0.98  
% 2.53/0.98  --qbf_mode                              false
% 2.53/0.98  --qbf_elim_univ                         false
% 2.53/0.98  --qbf_dom_inst                          none
% 2.53/0.98  --qbf_dom_pre_inst                      false
% 2.53/0.98  --qbf_sk_in                             false
% 2.53/0.98  --qbf_pred_elim                         true
% 2.53/0.98  --qbf_split                             512
% 2.53/0.98  
% 2.53/0.98  ------ BMC1 Options
% 2.53/0.98  
% 2.53/0.98  --bmc1_incremental                      false
% 2.53/0.98  --bmc1_axioms                           reachable_all
% 2.53/0.98  --bmc1_min_bound                        0
% 2.53/0.98  --bmc1_max_bound                        -1
% 2.53/0.98  --bmc1_max_bound_default                -1
% 2.53/0.98  --bmc1_symbol_reachability              true
% 2.53/0.98  --bmc1_property_lemmas                  false
% 2.53/0.98  --bmc1_k_induction                      false
% 2.53/0.98  --bmc1_non_equiv_states                 false
% 2.53/0.98  --bmc1_deadlock                         false
% 2.53/0.98  --bmc1_ucm                              false
% 2.53/0.98  --bmc1_add_unsat_core                   none
% 2.53/0.98  --bmc1_unsat_core_children              false
% 2.53/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.53/0.98  --bmc1_out_stat                         full
% 2.53/0.98  --bmc1_ground_init                      false
% 2.53/0.98  --bmc1_pre_inst_next_state              false
% 2.53/0.98  --bmc1_pre_inst_state                   false
% 2.53/0.98  --bmc1_pre_inst_reach_state             false
% 2.53/0.98  --bmc1_out_unsat_core                   false
% 2.53/0.98  --bmc1_aig_witness_out                  false
% 2.53/0.98  --bmc1_verbose                          false
% 2.53/0.98  --bmc1_dump_clauses_tptp                false
% 2.53/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.53/0.98  --bmc1_dump_file                        -
% 2.53/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.53/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.53/0.98  --bmc1_ucm_extend_mode                  1
% 2.53/0.98  --bmc1_ucm_init_mode                    2
% 2.53/0.98  --bmc1_ucm_cone_mode                    none
% 2.53/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.53/0.98  --bmc1_ucm_relax_model                  4
% 2.53/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.53/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.53/0.98  --bmc1_ucm_layered_model                none
% 2.53/0.98  --bmc1_ucm_max_lemma_size               10
% 2.53/0.98  
% 2.53/0.98  ------ AIG Options
% 2.53/0.98  
% 2.53/0.98  --aig_mode                              false
% 2.53/0.98  
% 2.53/0.98  ------ Instantiation Options
% 2.53/0.98  
% 2.53/0.98  --instantiation_flag                    true
% 2.53/0.98  --inst_sos_flag                         false
% 2.53/0.98  --inst_sos_phase                        true
% 2.53/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.53/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.53/0.98  --inst_lit_sel_side                     num_symb
% 2.53/0.98  --inst_solver_per_active                1400
% 2.53/0.98  --inst_solver_calls_frac                1.
% 2.53/0.98  --inst_passive_queue_type               priority_queues
% 2.53/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.53/0.98  --inst_passive_queues_freq              [25;2]
% 2.53/0.98  --inst_dismatching                      true
% 2.53/0.98  --inst_eager_unprocessed_to_passive     true
% 2.53/0.98  --inst_prop_sim_given                   true
% 2.53/0.98  --inst_prop_sim_new                     false
% 2.53/0.98  --inst_subs_new                         false
% 2.53/0.98  --inst_eq_res_simp                      false
% 2.53/0.98  --inst_subs_given                       false
% 2.53/0.98  --inst_orphan_elimination               true
% 2.53/0.98  --inst_learning_loop_flag               true
% 2.53/0.98  --inst_learning_start                   3000
% 2.53/0.98  --inst_learning_factor                  2
% 2.53/0.98  --inst_start_prop_sim_after_learn       3
% 2.53/0.98  --inst_sel_renew                        solver
% 2.53/0.98  --inst_lit_activity_flag                true
% 2.53/0.98  --inst_restr_to_given                   false
% 2.53/0.98  --inst_activity_threshold               500
% 2.53/0.98  --inst_out_proof                        true
% 2.53/0.98  
% 2.53/0.98  ------ Resolution Options
% 2.53/0.98  
% 2.53/0.98  --resolution_flag                       true
% 2.53/0.98  --res_lit_sel                           adaptive
% 2.53/0.98  --res_lit_sel_side                      none
% 2.53/0.98  --res_ordering                          kbo
% 2.53/0.98  --res_to_prop_solver                    active
% 2.53/0.98  --res_prop_simpl_new                    false
% 2.53/0.98  --res_prop_simpl_given                  true
% 2.53/0.98  --res_passive_queue_type                priority_queues
% 2.53/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.53/0.98  --res_passive_queues_freq               [15;5]
% 2.53/0.98  --res_forward_subs                      full
% 2.53/0.98  --res_backward_subs                     full
% 2.53/0.98  --res_forward_subs_resolution           true
% 2.53/0.98  --res_backward_subs_resolution          true
% 2.53/0.98  --res_orphan_elimination                true
% 2.53/0.98  --res_time_limit                        2.
% 2.53/0.98  --res_out_proof                         true
% 2.53/0.98  
% 2.53/0.98  ------ Superposition Options
% 2.53/0.98  
% 2.53/0.98  --superposition_flag                    true
% 2.53/0.98  --sup_passive_queue_type                priority_queues
% 2.53/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.53/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.53/0.98  --demod_completeness_check              fast
% 2.53/0.98  --demod_use_ground                      true
% 2.53/0.98  --sup_to_prop_solver                    passive
% 2.53/0.98  --sup_prop_simpl_new                    true
% 2.53/0.98  --sup_prop_simpl_given                  true
% 2.53/0.98  --sup_fun_splitting                     false
% 2.53/0.98  --sup_smt_interval                      50000
% 2.53/0.98  
% 2.53/0.98  ------ Superposition Simplification Setup
% 2.53/0.98  
% 2.53/0.98  --sup_indices_passive                   []
% 2.53/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.53/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/0.98  --sup_full_bw                           [BwDemod]
% 2.53/0.98  --sup_immed_triv                        [TrivRules]
% 2.53/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.53/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/0.98  --sup_immed_bw_main                     []
% 2.53/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.53/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/0.98  
% 2.53/0.98  ------ Combination Options
% 2.53/0.98  
% 2.53/0.98  --comb_res_mult                         3
% 2.53/0.98  --comb_sup_mult                         2
% 2.53/0.98  --comb_inst_mult                        10
% 2.53/0.98  
% 2.53/0.98  ------ Debug Options
% 2.53/0.98  
% 2.53/0.98  --dbg_backtrace                         false
% 2.53/0.98  --dbg_dump_prop_clauses                 false
% 2.53/0.98  --dbg_dump_prop_clauses_file            -
% 2.53/0.98  --dbg_out_stat                          false
% 2.53/0.98  ------ Parsing...
% 2.53/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.53/0.98  
% 2.53/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.53/0.98  
% 2.53/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.53/0.98  
% 2.53/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.53/0.98  ------ Proving...
% 2.53/0.98  ------ Problem Properties 
% 2.53/0.98  
% 2.53/0.98  
% 2.53/0.98  clauses                                 18
% 2.53/0.98  conjectures                             2
% 2.53/0.98  EPR                                     3
% 2.53/0.98  Horn                                    17
% 2.53/0.98  unary                                   3
% 2.53/0.98  binary                                  8
% 2.53/0.98  lits                                    42
% 2.53/0.98  lits eq                                 8
% 2.53/0.98  fd_pure                                 0
% 2.53/0.98  fd_pseudo                               0
% 2.53/0.98  fd_cond                                 0
% 2.53/0.98  fd_pseudo_cond                          1
% 2.53/0.98  AC symbols                              0
% 2.53/0.98  
% 2.53/0.98  ------ Schedule dynamic 5 is on 
% 2.53/0.98  
% 2.53/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.53/0.98  
% 2.53/0.98  
% 2.53/0.98  ------ 
% 2.53/0.98  Current options:
% 2.53/0.98  ------ 
% 2.53/0.98  
% 2.53/0.98  ------ Input Options
% 2.53/0.98  
% 2.53/0.98  --out_options                           all
% 2.53/0.98  --tptp_safe_out                         true
% 2.53/0.98  --problem_path                          ""
% 2.53/0.98  --include_path                          ""
% 2.53/0.98  --clausifier                            res/vclausify_rel
% 2.53/0.98  --clausifier_options                    --mode clausify
% 2.53/0.98  --stdin                                 false
% 2.53/0.98  --stats_out                             all
% 2.53/0.98  
% 2.53/0.98  ------ General Options
% 2.53/0.98  
% 2.53/0.98  --fof                                   false
% 2.53/0.98  --time_out_real                         305.
% 2.53/0.98  --time_out_virtual                      -1.
% 2.53/0.98  --symbol_type_check                     false
% 2.53/0.98  --clausify_out                          false
% 2.53/0.98  --sig_cnt_out                           false
% 2.53/0.98  --trig_cnt_out                          false
% 2.53/0.98  --trig_cnt_out_tolerance                1.
% 2.53/0.98  --trig_cnt_out_sk_spl                   false
% 2.53/0.98  --abstr_cl_out                          false
% 2.53/0.98  
% 2.53/0.98  ------ Global Options
% 2.53/0.98  
% 2.53/0.98  --schedule                              default
% 2.53/0.98  --add_important_lit                     false
% 2.53/0.98  --prop_solver_per_cl                    1000
% 2.53/0.98  --min_unsat_core                        false
% 2.53/0.98  --soft_assumptions                      false
% 2.53/0.98  --soft_lemma_size                       3
% 2.53/0.98  --prop_impl_unit_size                   0
% 2.53/0.98  --prop_impl_unit                        []
% 2.53/0.98  --share_sel_clauses                     true
% 2.53/0.98  --reset_solvers                         false
% 2.53/0.98  --bc_imp_inh                            [conj_cone]
% 2.53/0.98  --conj_cone_tolerance                   3.
% 2.53/0.98  --extra_neg_conj                        none
% 2.53/0.98  --large_theory_mode                     true
% 2.53/0.98  --prolific_symb_bound                   200
% 2.53/0.98  --lt_threshold                          2000
% 2.53/0.98  --clause_weak_htbl                      true
% 2.53/0.98  --gc_record_bc_elim                     false
% 2.53/0.98  
% 2.53/0.98  ------ Preprocessing Options
% 2.53/0.98  
% 2.53/0.98  --preprocessing_flag                    true
% 2.53/0.98  --time_out_prep_mult                    0.1
% 2.53/0.98  --splitting_mode                        input
% 2.53/0.98  --splitting_grd                         true
% 2.53/0.98  --splitting_cvd                         false
% 2.53/0.98  --splitting_cvd_svl                     false
% 2.53/0.98  --splitting_nvd                         32
% 2.53/0.98  --sub_typing                            true
% 2.53/0.98  --prep_gs_sim                           true
% 2.53/0.98  --prep_unflatten                        true
% 2.53/0.98  --prep_res_sim                          true
% 2.53/0.98  --prep_upred                            true
% 2.53/0.98  --prep_sem_filter                       exhaustive
% 2.53/0.98  --prep_sem_filter_out                   false
% 2.53/0.98  --pred_elim                             true
% 2.53/0.98  --res_sim_input                         true
% 2.53/0.99  --eq_ax_congr_red                       true
% 2.53/0.99  --pure_diseq_elim                       true
% 2.53/0.99  --brand_transform                       false
% 2.53/0.99  --non_eq_to_eq                          false
% 2.53/0.99  --prep_def_merge                        true
% 2.53/0.99  --prep_def_merge_prop_impl              false
% 2.53/0.99  --prep_def_merge_mbd                    true
% 2.53/0.99  --prep_def_merge_tr_red                 false
% 2.53/0.99  --prep_def_merge_tr_cl                  false
% 2.53/0.99  --smt_preprocessing                     true
% 2.53/0.99  --smt_ac_axioms                         fast
% 2.53/0.99  --preprocessed_out                      false
% 2.53/0.99  --preprocessed_stats                    false
% 2.53/0.99  
% 2.53/0.99  ------ Abstraction refinement Options
% 2.53/0.99  
% 2.53/0.99  --abstr_ref                             []
% 2.53/0.99  --abstr_ref_prep                        false
% 2.53/0.99  --abstr_ref_until_sat                   false
% 2.53/0.99  --abstr_ref_sig_restrict                funpre
% 2.53/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.53/0.99  --abstr_ref_under                       []
% 2.53/0.99  
% 2.53/0.99  ------ SAT Options
% 2.53/0.99  
% 2.53/0.99  --sat_mode                              false
% 2.53/0.99  --sat_fm_restart_options                ""
% 2.53/0.99  --sat_gr_def                            false
% 2.53/0.99  --sat_epr_types                         true
% 2.53/0.99  --sat_non_cyclic_types                  false
% 2.53/0.99  --sat_finite_models                     false
% 2.53/0.99  --sat_fm_lemmas                         false
% 2.53/0.99  --sat_fm_prep                           false
% 2.53/0.99  --sat_fm_uc_incr                        true
% 2.53/0.99  --sat_out_model                         small
% 2.53/0.99  --sat_out_clauses                       false
% 2.53/0.99  
% 2.53/0.99  ------ QBF Options
% 2.53/0.99  
% 2.53/0.99  --qbf_mode                              false
% 2.53/0.99  --qbf_elim_univ                         false
% 2.53/0.99  --qbf_dom_inst                          none
% 2.53/0.99  --qbf_dom_pre_inst                      false
% 2.53/0.99  --qbf_sk_in                             false
% 2.53/0.99  --qbf_pred_elim                         true
% 2.53/0.99  --qbf_split                             512
% 2.53/0.99  
% 2.53/0.99  ------ BMC1 Options
% 2.53/0.99  
% 2.53/0.99  --bmc1_incremental                      false
% 2.53/0.99  --bmc1_axioms                           reachable_all
% 2.53/0.99  --bmc1_min_bound                        0
% 2.53/0.99  --bmc1_max_bound                        -1
% 2.53/0.99  --bmc1_max_bound_default                -1
% 2.53/0.99  --bmc1_symbol_reachability              true
% 2.53/0.99  --bmc1_property_lemmas                  false
% 2.53/0.99  --bmc1_k_induction                      false
% 2.53/0.99  --bmc1_non_equiv_states                 false
% 2.53/0.99  --bmc1_deadlock                         false
% 2.53/0.99  --bmc1_ucm                              false
% 2.53/0.99  --bmc1_add_unsat_core                   none
% 2.53/0.99  --bmc1_unsat_core_children              false
% 2.53/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.53/0.99  --bmc1_out_stat                         full
% 2.53/0.99  --bmc1_ground_init                      false
% 2.53/0.99  --bmc1_pre_inst_next_state              false
% 2.53/0.99  --bmc1_pre_inst_state                   false
% 2.53/0.99  --bmc1_pre_inst_reach_state             false
% 2.53/0.99  --bmc1_out_unsat_core                   false
% 2.53/0.99  --bmc1_aig_witness_out                  false
% 2.53/0.99  --bmc1_verbose                          false
% 2.53/0.99  --bmc1_dump_clauses_tptp                false
% 2.53/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.53/0.99  --bmc1_dump_file                        -
% 2.53/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.53/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.53/0.99  --bmc1_ucm_extend_mode                  1
% 2.53/0.99  --bmc1_ucm_init_mode                    2
% 2.53/0.99  --bmc1_ucm_cone_mode                    none
% 2.53/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.53/0.99  --bmc1_ucm_relax_model                  4
% 2.53/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.53/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.53/0.99  --bmc1_ucm_layered_model                none
% 2.53/0.99  --bmc1_ucm_max_lemma_size               10
% 2.53/0.99  
% 2.53/0.99  ------ AIG Options
% 2.53/0.99  
% 2.53/0.99  --aig_mode                              false
% 2.53/0.99  
% 2.53/0.99  ------ Instantiation Options
% 2.53/0.99  
% 2.53/0.99  --instantiation_flag                    true
% 2.53/0.99  --inst_sos_flag                         false
% 2.53/0.99  --inst_sos_phase                        true
% 2.53/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.53/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.53/0.99  --inst_lit_sel_side                     none
% 2.53/0.99  --inst_solver_per_active                1400
% 2.53/0.99  --inst_solver_calls_frac                1.
% 2.53/0.99  --inst_passive_queue_type               priority_queues
% 2.53/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.53/0.99  --inst_passive_queues_freq              [25;2]
% 2.53/0.99  --inst_dismatching                      true
% 2.53/0.99  --inst_eager_unprocessed_to_passive     true
% 2.53/0.99  --inst_prop_sim_given                   true
% 2.53/0.99  --inst_prop_sim_new                     false
% 2.53/0.99  --inst_subs_new                         false
% 2.53/0.99  --inst_eq_res_simp                      false
% 2.53/0.99  --inst_subs_given                       false
% 2.53/0.99  --inst_orphan_elimination               true
% 2.53/0.99  --inst_learning_loop_flag               true
% 2.53/0.99  --inst_learning_start                   3000
% 2.53/0.99  --inst_learning_factor                  2
% 2.53/0.99  --inst_start_prop_sim_after_learn       3
% 2.53/0.99  --inst_sel_renew                        solver
% 2.53/0.99  --inst_lit_activity_flag                true
% 2.53/0.99  --inst_restr_to_given                   false
% 2.53/0.99  --inst_activity_threshold               500
% 2.53/0.99  --inst_out_proof                        true
% 2.53/0.99  
% 2.53/0.99  ------ Resolution Options
% 2.53/0.99  
% 2.53/0.99  --resolution_flag                       false
% 2.53/0.99  --res_lit_sel                           adaptive
% 2.53/0.99  --res_lit_sel_side                      none
% 2.53/0.99  --res_ordering                          kbo
% 2.53/0.99  --res_to_prop_solver                    active
% 2.53/0.99  --res_prop_simpl_new                    false
% 2.53/0.99  --res_prop_simpl_given                  true
% 2.53/0.99  --res_passive_queue_type                priority_queues
% 2.53/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.53/0.99  --res_passive_queues_freq               [15;5]
% 2.53/0.99  --res_forward_subs                      full
% 2.53/0.99  --res_backward_subs                     full
% 2.53/0.99  --res_forward_subs_resolution           true
% 2.53/0.99  --res_backward_subs_resolution          true
% 2.53/0.99  --res_orphan_elimination                true
% 2.53/0.99  --res_time_limit                        2.
% 2.53/0.99  --res_out_proof                         true
% 2.53/0.99  
% 2.53/0.99  ------ Superposition Options
% 2.53/0.99  
% 2.53/0.99  --superposition_flag                    true
% 2.53/0.99  --sup_passive_queue_type                priority_queues
% 2.53/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.53/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.53/0.99  --demod_completeness_check              fast
% 2.53/0.99  --demod_use_ground                      true
% 2.53/0.99  --sup_to_prop_solver                    passive
% 2.53/0.99  --sup_prop_simpl_new                    true
% 2.53/0.99  --sup_prop_simpl_given                  true
% 2.53/0.99  --sup_fun_splitting                     false
% 2.53/0.99  --sup_smt_interval                      50000
% 2.53/0.99  
% 2.53/0.99  ------ Superposition Simplification Setup
% 2.53/0.99  
% 2.53/0.99  --sup_indices_passive                   []
% 2.53/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.53/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/0.99  --sup_full_bw                           [BwDemod]
% 2.53/0.99  --sup_immed_triv                        [TrivRules]
% 2.53/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.53/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/0.99  --sup_immed_bw_main                     []
% 2.53/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.53/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/0.99  
% 2.53/0.99  ------ Combination Options
% 2.53/0.99  
% 2.53/0.99  --comb_res_mult                         3
% 2.53/0.99  --comb_sup_mult                         2
% 2.53/0.99  --comb_inst_mult                        10
% 2.53/0.99  
% 2.53/0.99  ------ Debug Options
% 2.53/0.99  
% 2.53/0.99  --dbg_backtrace                         false
% 2.53/0.99  --dbg_dump_prop_clauses                 false
% 2.53/0.99  --dbg_dump_prop_clauses_file            -
% 2.53/0.99  --dbg_out_stat                          false
% 2.53/0.99  
% 2.53/0.99  
% 2.53/0.99  
% 2.53/0.99  
% 2.53/0.99  ------ Proving...
% 2.53/0.99  
% 2.53/0.99  
% 2.53/0.99  % SZS status Theorem for theBenchmark.p
% 2.53/0.99  
% 2.53/0.99   Resolution empty clause
% 2.53/0.99  
% 2.53/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.53/0.99  
% 2.53/0.99  fof(f6,axiom,(
% 2.53/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.53/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f20,plain,(
% 2.53/0.99    ! [X0,X1] : (m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.53/0.99    inference(ennf_transformation,[],[f6])).
% 2.53/0.99  
% 2.53/0.99  fof(f21,plain,(
% 2.53/0.99    ! [X0,X1] : (m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.53/0.99    inference(flattening,[],[f20])).
% 2.53/0.99  
% 2.53/0.99  fof(f56,plain,(
% 2.53/0.99    ( ! [X0,X1] : (m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.53/0.99    inference(cnf_transformation,[],[f21])).
% 2.53/0.99  
% 2.53/0.99  fof(f11,conjecture,(
% 2.53/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 2.53/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f12,negated_conjecture,(
% 2.53/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 2.53/0.99    inference(negated_conjecture,[],[f11])).
% 2.53/0.99  
% 2.53/0.99  fof(f30,plain,(
% 2.53/0.99    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.53/0.99    inference(ennf_transformation,[],[f12])).
% 2.53/0.99  
% 2.53/0.99  fof(f31,plain,(
% 2.53/0.99    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.53/0.99    inference(flattening,[],[f30])).
% 2.53/0.99  
% 2.53/0.99  fof(f39,plain,(
% 2.53/0.99    ? [X0] : (? [X1] : (((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.53/0.99    inference(nnf_transformation,[],[f31])).
% 2.53/0.99  
% 2.53/0.99  fof(f40,plain,(
% 2.53/0.99    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.53/0.99    inference(flattening,[],[f39])).
% 2.53/0.99  
% 2.53/0.99  fof(f42,plain,(
% 2.53/0.99    ( ! [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,sK1) | ~v3_pre_topc(sK1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,sK1) | v3_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.53/0.99    introduced(choice_axiom,[])).
% 2.53/0.99  
% 2.53/0.99  fof(f41,plain,(
% 2.53/0.99    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X1) | ~v3_pre_topc(X1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.53/0.99    introduced(choice_axiom,[])).
% 2.53/0.99  
% 2.53/0.99  fof(f43,plain,(
% 2.53/0.99    ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.53/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).
% 2.53/0.99  
% 2.53/0.99  fof(f64,plain,(
% 2.53/0.99    ~v2_struct_0(sK0)),
% 2.53/0.99    inference(cnf_transformation,[],[f43])).
% 2.53/0.99  
% 2.53/0.99  fof(f65,plain,(
% 2.53/0.99    v2_pre_topc(sK0)),
% 2.53/0.99    inference(cnf_transformation,[],[f43])).
% 2.53/0.99  
% 2.53/0.99  fof(f66,plain,(
% 2.53/0.99    l1_pre_topc(sK0)),
% 2.53/0.99    inference(cnf_transformation,[],[f43])).
% 2.53/0.99  
% 2.53/0.99  fof(f8,axiom,(
% 2.53/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 2.53/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f24,plain,(
% 2.53/0.99    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.53/0.99    inference(ennf_transformation,[],[f8])).
% 2.53/0.99  
% 2.53/0.99  fof(f25,plain,(
% 2.53/0.99    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.53/0.99    inference(flattening,[],[f24])).
% 2.53/0.99  
% 2.53/0.99  fof(f38,plain,(
% 2.53/0.99    ! [X0] : (! [X1] : (((r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1)) & (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.53/0.99    inference(nnf_transformation,[],[f25])).
% 2.53/0.99  
% 2.53/0.99  fof(f59,plain,(
% 2.53/0.99    ( ! [X0,X1] : (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.53/0.99    inference(cnf_transformation,[],[f38])).
% 2.53/0.99  
% 2.53/0.99  fof(f2,axiom,(
% 2.53/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 2.53/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f14,plain,(
% 2.53/0.99    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.53/0.99    inference(ennf_transformation,[],[f2])).
% 2.53/0.99  
% 2.53/0.99  fof(f34,plain,(
% 2.53/0.99    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.53/0.99    inference(nnf_transformation,[],[f14])).
% 2.53/0.99  
% 2.53/0.99  fof(f47,plain,(
% 2.53/0.99    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.53/0.99    inference(cnf_transformation,[],[f34])).
% 2.53/0.99  
% 2.53/0.99  fof(f68,plain,(
% 2.53/0.99    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)),
% 2.53/0.99    inference(cnf_transformation,[],[f43])).
% 2.53/0.99  
% 2.53/0.99  fof(f67,plain,(
% 2.53/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.53/0.99    inference(cnf_transformation,[],[f43])).
% 2.53/0.99  
% 2.53/0.99  fof(f4,axiom,(
% 2.53/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 2.53/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f16,plain,(
% 2.53/0.99    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.53/0.99    inference(ennf_transformation,[],[f4])).
% 2.53/0.99  
% 2.53/0.99  fof(f17,plain,(
% 2.53/0.99    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.53/0.99    inference(flattening,[],[f16])).
% 2.53/0.99  
% 2.53/0.99  fof(f36,plain,(
% 2.53/0.99    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.53/0.99    inference(nnf_transformation,[],[f17])).
% 2.53/0.99  
% 2.53/0.99  fof(f37,plain,(
% 2.53/0.99    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.53/0.99    inference(flattening,[],[f36])).
% 2.53/0.99  
% 2.53/0.99  fof(f51,plain,(
% 2.53/0.99    ( ! [X0,X1] : (v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.53/0.99    inference(cnf_transformation,[],[f37])).
% 2.53/0.99  
% 2.53/0.99  fof(f9,axiom,(
% 2.53/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 2.53/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f26,plain,(
% 2.53/0.99    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.53/0.99    inference(ennf_transformation,[],[f9])).
% 2.53/0.99  
% 2.53/0.99  fof(f27,plain,(
% 2.53/0.99    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.53/0.99    inference(flattening,[],[f26])).
% 2.53/0.99  
% 2.53/0.99  fof(f61,plain,(
% 2.53/0.99    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.53/0.99    inference(cnf_transformation,[],[f27])).
% 2.53/0.99  
% 2.53/0.99  fof(f3,axiom,(
% 2.53/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 2.53/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f15,plain,(
% 2.53/0.99    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.53/0.99    inference(ennf_transformation,[],[f3])).
% 2.53/0.99  
% 2.53/0.99  fof(f35,plain,(
% 2.53/0.99    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(X0))) & (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 2.53/0.99    inference(nnf_transformation,[],[f15])).
% 2.53/0.99  
% 2.53/0.99  fof(f49,plain,(
% 2.53/0.99    ( ! [X0,X1] : (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.53/0.99    inference(cnf_transformation,[],[f35])).
% 2.53/0.99  
% 2.53/0.99  fof(f62,plain,(
% 2.53/0.99    ( ! [X0,X1] : (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.53/0.99    inference(cnf_transformation,[],[f27])).
% 2.53/0.99  
% 2.53/0.99  fof(f7,axiom,(
% 2.53/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 2.53/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f13,plain,(
% 2.53/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))))),
% 2.53/0.99    inference(pure_predicate_removal,[],[f7])).
% 2.53/0.99  
% 2.53/0.99  fof(f22,plain,(
% 2.53/0.99    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.53/0.99    inference(ennf_transformation,[],[f13])).
% 2.53/0.99  
% 2.53/0.99  fof(f23,plain,(
% 2.53/0.99    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.53/0.99    inference(flattening,[],[f22])).
% 2.53/0.99  
% 2.53/0.99  fof(f58,plain,(
% 2.53/0.99    ( ! [X0,X1] : (l1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.53/0.99    inference(cnf_transformation,[],[f23])).
% 2.53/0.99  
% 2.53/0.99  fof(f1,axiom,(
% 2.53/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.53/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f32,plain,(
% 2.53/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.53/0.99    inference(nnf_transformation,[],[f1])).
% 2.53/0.99  
% 2.53/0.99  fof(f33,plain,(
% 2.53/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.53/0.99    inference(flattening,[],[f32])).
% 2.53/0.99  
% 2.53/0.99  fof(f44,plain,(
% 2.53/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.53/0.99    inference(cnf_transformation,[],[f33])).
% 2.53/0.99  
% 2.53/0.99  fof(f71,plain,(
% 2.53/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.53/0.99    inference(equality_resolution,[],[f44])).
% 2.53/0.99  
% 2.53/0.99  fof(f50,plain,(
% 2.53/0.99    ( ! [X0,X1] : (v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.53/0.99    inference(cnf_transformation,[],[f35])).
% 2.53/0.99  
% 2.53/0.99  fof(f53,plain,(
% 2.53/0.99    ( ! [X0,X1] : (v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.53/0.99    inference(cnf_transformation,[],[f37])).
% 2.53/0.99  
% 2.53/0.99  fof(f46,plain,(
% 2.53/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.53/0.99    inference(cnf_transformation,[],[f33])).
% 2.53/0.99  
% 2.53/0.99  fof(f10,axiom,(
% 2.53/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1))))),
% 2.53/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f28,plain,(
% 2.53/0.99    ! [X0] : (! [X1] : (r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.53/0.99    inference(ennf_transformation,[],[f10])).
% 2.53/0.99  
% 2.53/0.99  fof(f29,plain,(
% 2.53/0.99    ! [X0] : (! [X1] : (r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.53/0.99    inference(flattening,[],[f28])).
% 2.53/0.99  
% 2.53/0.99  fof(f63,plain,(
% 2.53/0.99    ( ! [X0,X1] : (r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.53/0.99    inference(cnf_transformation,[],[f29])).
% 2.53/0.99  
% 2.53/0.99  fof(f5,axiom,(
% 2.53/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)))),
% 2.53/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/0.99  
% 2.53/0.99  fof(f18,plain,(
% 2.53/0.99    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.53/0.99    inference(ennf_transformation,[],[f5])).
% 2.53/0.99  
% 2.53/0.99  fof(f19,plain,(
% 2.53/0.99    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.53/0.99    inference(flattening,[],[f18])).
% 2.53/0.99  
% 2.53/0.99  fof(f55,plain,(
% 2.53/0.99    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.53/0.99    inference(cnf_transformation,[],[f19])).
% 2.53/0.99  
% 2.53/0.99  fof(f60,plain,(
% 2.53/0.99    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.53/0.99    inference(cnf_transformation,[],[f38])).
% 2.53/0.99  
% 2.53/0.99  fof(f48,plain,(
% 2.53/0.99    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.53/0.99    inference(cnf_transformation,[],[f34])).
% 2.53/0.99  
% 2.53/0.99  fof(f69,plain,(
% 2.53/0.99    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 2.53/0.99    inference(cnf_transformation,[],[f43])).
% 2.53/0.99  
% 2.53/0.99  cnf(c_12,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/0.99      | m1_subset_1(k5_tmap_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.53/0.99      | v2_struct_0(X1)
% 2.53/0.99      | ~ v2_pre_topc(X1)
% 2.53/0.99      | ~ l1_pre_topc(X1) ),
% 2.53/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_25,negated_conjecture,
% 2.53/0.99      ( ~ v2_struct_0(sK0) ),
% 2.53/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_557,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/0.99      | m1_subset_1(k5_tmap_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.53/0.99      | ~ v2_pre_topc(X1)
% 2.53/0.99      | ~ l1_pre_topc(X1)
% 2.53/0.99      | sK0 != X1 ),
% 2.53/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_25]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_558,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/0.99      | m1_subset_1(k5_tmap_1(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 2.53/0.99      | ~ v2_pre_topc(sK0)
% 2.53/0.99      | ~ l1_pre_topc(sK0) ),
% 2.53/0.99      inference(unflattening,[status(thm)],[c_557]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_24,negated_conjecture,
% 2.53/0.99      ( v2_pre_topc(sK0) ),
% 2.53/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_23,negated_conjecture,
% 2.53/0.99      ( l1_pre_topc(sK0) ),
% 2.53/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_562,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/0.99      | m1_subset_1(k5_tmap_1(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 2.53/0.99      inference(global_propositional_subsumption,
% 2.53/0.99                [status(thm)],
% 2.53/0.99                [c_558,c_24,c_23]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1459,plain,
% 2.53/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.53/0.99      | m1_subset_1(k5_tmap_1(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_562]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_16,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/0.99      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 2.53/0.99      | v2_struct_0(X1)
% 2.53/0.99      | ~ v2_pre_topc(X1)
% 2.53/0.99      | ~ l1_pre_topc(X1)
% 2.53/0.99      | k5_tmap_1(X1,X0) = u1_pre_topc(X1) ),
% 2.53/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_4,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/0.99      | r2_hidden(X0,u1_pre_topc(X1))
% 2.53/0.99      | ~ v3_pre_topc(X0,X1)
% 2.53/0.99      | ~ l1_pre_topc(X1) ),
% 2.53/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_21,negated_conjecture,
% 2.53/0.99      ( v3_pre_topc(sK1,sK0)
% 2.53/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 2.53/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_197,plain,
% 2.53/0.99      ( v3_pre_topc(sK1,sK0)
% 2.53/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 2.53/0.99      inference(prop_impl,[status(thm)],[c_21]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_347,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/0.99      | r2_hidden(X0,u1_pre_topc(X1))
% 2.53/0.99      | ~ l1_pre_topc(X1)
% 2.53/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
% 2.53/0.99      | sK1 != X0
% 2.53/0.99      | sK0 != X1 ),
% 2.53/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_197]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_348,plain,
% 2.53/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/0.99      | r2_hidden(sK1,u1_pre_topc(sK0))
% 2.53/0.99      | ~ l1_pre_topc(sK0)
% 2.53/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 2.53/0.99      inference(unflattening,[status(thm)],[c_347]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_22,negated_conjecture,
% 2.53/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.53/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_350,plain,
% 2.53/0.99      ( r2_hidden(sK1,u1_pre_topc(sK0))
% 2.53/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 2.53/0.99      inference(global_propositional_subsumption,
% 2.53/0.99                [status(thm)],
% 2.53/0.99                [c_348,c_23,c_22]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_396,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/0.99      | v2_struct_0(X1)
% 2.53/0.99      | ~ v2_pre_topc(X1)
% 2.53/0.99      | ~ l1_pre_topc(X1)
% 2.53/0.99      | k5_tmap_1(X1,X0) = u1_pre_topc(X1)
% 2.53/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
% 2.53/0.99      | u1_pre_topc(X1) != u1_pre_topc(sK0)
% 2.53/0.99      | sK1 != X0 ),
% 2.53/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_350]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_397,plain,
% 2.53/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.53/0.99      | v2_struct_0(X0)
% 2.53/0.99      | ~ v2_pre_topc(X0)
% 2.53/0.99      | ~ l1_pre_topc(X0)
% 2.53/0.99      | k5_tmap_1(X0,sK1) = u1_pre_topc(X0)
% 2.53/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
% 2.53/0.99      | u1_pre_topc(X0) != u1_pre_topc(sK0) ),
% 2.53/0.99      inference(unflattening,[status(thm)],[c_396]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_439,plain,
% 2.53/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.53/0.99      | ~ v2_pre_topc(X0)
% 2.53/0.99      | ~ l1_pre_topc(X0)
% 2.53/0.99      | k5_tmap_1(X0,sK1) = u1_pre_topc(X0)
% 2.53/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
% 2.53/0.99      | u1_pre_topc(X0) != u1_pre_topc(sK0)
% 2.53/0.99      | sK0 != X0 ),
% 2.53/0.99      inference(resolution_lifted,[status(thm)],[c_397,c_25]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_440,plain,
% 2.53/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/0.99      | ~ v2_pre_topc(sK0)
% 2.53/0.99      | ~ l1_pre_topc(sK0)
% 2.53/0.99      | k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 2.53/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
% 2.53/0.99      | u1_pre_topc(sK0) != u1_pre_topc(sK0) ),
% 2.53/0.99      inference(unflattening,[status(thm)],[c_439]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_442,plain,
% 2.53/0.99      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 2.53/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
% 2.53/0.99      | u1_pre_topc(sK0) != u1_pre_topc(sK0) ),
% 2.53/0.99      inference(global_propositional_subsumption,
% 2.53/0.99                [status(thm)],
% 2.53/0.99                [c_440,c_25,c_24,c_23,c_22,c_399]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_827,plain,
% 2.53/0.99      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 2.53/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 2.53/0.99      inference(equality_resolution_simp,[status(thm)],[c_442]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_858,plain,
% 2.53/0.99      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 2.53/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 2.53/0.99      inference(prop_impl,[status(thm)],[c_827]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_10,plain,
% 2.53/0.99      ( ~ v1_tops_2(X0,X1)
% 2.53/0.99      | v1_tops_2(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.53/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.53/0.99      | v2_struct_0(X1)
% 2.53/0.99      | ~ v2_pre_topc(X1)
% 2.53/0.99      | ~ l1_pre_topc(X1) ),
% 2.53/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_593,plain,
% 2.53/0.99      ( ~ v1_tops_2(X0,X1)
% 2.53/0.99      | v1_tops_2(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.53/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.53/0.99      | ~ v2_pre_topc(X1)
% 2.53/0.99      | ~ l1_pre_topc(X1)
% 2.53/0.99      | sK0 != X1 ),
% 2.53/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_25]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_594,plain,
% 2.53/0.99      ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 2.53/0.99      | ~ v1_tops_2(X0,sK0)
% 2.53/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 2.53/0.99      | ~ v2_pre_topc(sK0)
% 2.53/0.99      | ~ l1_pre_topc(sK0) ),
% 2.53/0.99      inference(unflattening,[status(thm)],[c_593]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_598,plain,
% 2.53/0.99      ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 2.53/0.99      | ~ v1_tops_2(X0,sK0)
% 2.53/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 2.53/0.99      inference(global_propositional_subsumption,
% 2.53/0.99                [status(thm)],
% 2.53/0.99                [c_594,c_24,c_23]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1457,plain,
% 2.53/0.99      ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = iProver_top
% 2.53/0.99      | v1_tops_2(X0,sK0) != iProver_top
% 2.53/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_598]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_2078,plain,
% 2.53/0.99      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 2.53/0.99      | v1_tops_2(X0,k6_tmap_1(sK0,sK1)) = iProver_top
% 2.53/0.99      | v1_tops_2(X0,sK0) != iProver_top
% 2.53/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_858,c_1457]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_2397,plain,
% 2.53/0.99      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 2.53/0.99      | v1_tops_2(k5_tmap_1(sK0,X0),k6_tmap_1(sK0,sK1)) = iProver_top
% 2.53/0.99      | v1_tops_2(k5_tmap_1(sK0,X0),sK0) != iProver_top
% 2.53/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_1459,c_2078]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1465,plain,
% 2.53/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_18,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/0.99      | v2_struct_0(X1)
% 2.53/0.99      | ~ v2_pre_topc(X1)
% 2.53/0.99      | ~ l1_pre_topc(X1)
% 2.53/0.99      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 2.53/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_485,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/0.99      | ~ v2_pre_topc(X1)
% 2.53/0.99      | ~ l1_pre_topc(X1)
% 2.53/0.99      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
% 2.53/0.99      | sK0 != X1 ),
% 2.53/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_25]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_486,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/0.99      | ~ v2_pre_topc(sK0)
% 2.53/0.99      | ~ l1_pre_topc(sK0)
% 2.53/0.99      | u1_struct_0(k6_tmap_1(sK0,X0)) = u1_struct_0(sK0) ),
% 2.53/0.99      inference(unflattening,[status(thm)],[c_485]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_490,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/0.99      | u1_struct_0(k6_tmap_1(sK0,X0)) = u1_struct_0(sK0) ),
% 2.53/0.99      inference(global_propositional_subsumption,
% 2.53/0.99                [status(thm)],
% 2.53/0.99                [c_486,c_24,c_23]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1462,plain,
% 2.53/0.99      ( u1_struct_0(k6_tmap_1(sK0,X0)) = u1_struct_0(sK0)
% 2.53/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_490]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1647,plain,
% 2.53/0.99      ( u1_struct_0(k6_tmap_1(sK0,sK1)) = u1_struct_0(sK0) ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_1465,c_1462]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_6,plain,
% 2.53/0.99      ( ~ v1_tops_2(X0,X1)
% 2.53/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.53/0.99      | r1_tarski(X0,u1_pre_topc(X1))
% 2.53/0.99      | ~ l1_pre_topc(X1) ),
% 2.53/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1466,plain,
% 2.53/0.99      ( v1_tops_2(X0,X1) != iProver_top
% 2.53/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
% 2.53/0.99      | r1_tarski(X0,u1_pre_topc(X1)) = iProver_top
% 2.53/0.99      | l1_pre_topc(X1) != iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_2264,plain,
% 2.53/0.99      ( v1_tops_2(X0,k6_tmap_1(sK0,sK1)) != iProver_top
% 2.53/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 2.53/0.99      | r1_tarski(X0,u1_pre_topc(k6_tmap_1(sK0,sK1))) = iProver_top
% 2.53/0.99      | l1_pre_topc(k6_tmap_1(sK0,sK1)) != iProver_top ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_1647,c_1466]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_17,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/0.99      | v2_struct_0(X1)
% 2.53/0.99      | ~ v2_pre_topc(X1)
% 2.53/0.99      | ~ l1_pre_topc(X1)
% 2.53/0.99      | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
% 2.53/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_503,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/0.99      | ~ v2_pre_topc(X1)
% 2.53/0.99      | ~ l1_pre_topc(X1)
% 2.53/0.99      | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0)
% 2.53/0.99      | sK0 != X1 ),
% 2.53/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_504,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/0.99      | ~ v2_pre_topc(sK0)
% 2.53/0.99      | ~ l1_pre_topc(sK0)
% 2.53/0.99      | u1_pre_topc(k6_tmap_1(sK0,X0)) = k5_tmap_1(sK0,X0) ),
% 2.53/0.99      inference(unflattening,[status(thm)],[c_503]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_508,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/0.99      | u1_pre_topc(k6_tmap_1(sK0,X0)) = k5_tmap_1(sK0,X0) ),
% 2.53/0.99      inference(global_propositional_subsumption,
% 2.53/0.99                [status(thm)],
% 2.53/0.99                [c_504,c_24,c_23]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1461,plain,
% 2.53/0.99      ( u1_pre_topc(k6_tmap_1(sK0,X0)) = k5_tmap_1(sK0,X0)
% 2.53/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_508]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1680,plain,
% 2.53/0.99      ( u1_pre_topc(k6_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,sK1) ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_1465,c_1461]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_2269,plain,
% 2.53/0.99      ( v1_tops_2(X0,k6_tmap_1(sK0,sK1)) != iProver_top
% 2.53/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 2.53/0.99      | r1_tarski(X0,k5_tmap_1(sK0,sK1)) = iProver_top
% 2.53/0.99      | l1_pre_topc(k6_tmap_1(sK0,sK1)) != iProver_top ),
% 2.53/0.99      inference(light_normalisation,[status(thm)],[c_2264,c_1680]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_29,plain,
% 2.53/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_13,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/0.99      | v2_struct_0(X1)
% 2.53/0.99      | ~ v2_pre_topc(X1)
% 2.53/0.99      | ~ l1_pre_topc(X1)
% 2.53/0.99      | l1_pre_topc(k6_tmap_1(X1,X0)) ),
% 2.53/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_539,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/0.99      | ~ v2_pre_topc(X1)
% 2.53/0.99      | ~ l1_pre_topc(X1)
% 2.53/0.99      | l1_pre_topc(k6_tmap_1(X1,X0))
% 2.53/0.99      | sK0 != X1 ),
% 2.53/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_25]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_540,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/0.99      | ~ v2_pre_topc(sK0)
% 2.53/0.99      | l1_pre_topc(k6_tmap_1(sK0,X0))
% 2.53/0.99      | ~ l1_pre_topc(sK0) ),
% 2.53/0.99      inference(unflattening,[status(thm)],[c_539]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_544,plain,
% 2.53/0.99      ( l1_pre_topc(k6_tmap_1(sK0,X0))
% 2.53/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.53/0.99      inference(global_propositional_subsumption,
% 2.53/0.99                [status(thm)],
% 2.53/0.99                [c_540,c_24,c_23]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_545,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/0.99      | l1_pre_topc(k6_tmap_1(sK0,X0)) ),
% 2.53/0.99      inference(renaming,[status(thm)],[c_544]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1596,plain,
% 2.53/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/0.99      | l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
% 2.53/0.99      inference(instantiation,[status(thm)],[c_545]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1597,plain,
% 2.53/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.53/0.99      | l1_pre_topc(k6_tmap_1(sK0,sK1)) = iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_1596]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_2588,plain,
% 2.53/0.99      ( r1_tarski(X0,k5_tmap_1(sK0,sK1)) = iProver_top
% 2.53/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 2.53/0.99      | v1_tops_2(X0,k6_tmap_1(sK0,sK1)) != iProver_top ),
% 2.53/0.99      inference(global_propositional_subsumption,
% 2.53/0.99                [status(thm)],
% 2.53/0.99                [c_2269,c_29,c_1597]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_2589,plain,
% 2.53/0.99      ( v1_tops_2(X0,k6_tmap_1(sK0,sK1)) != iProver_top
% 2.53/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 2.53/0.99      | r1_tarski(X0,k5_tmap_1(sK0,sK1)) = iProver_top ),
% 2.53/0.99      inference(renaming,[status(thm)],[c_2588]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_2597,plain,
% 2.53/0.99      ( v1_tops_2(k5_tmap_1(sK0,X0),k6_tmap_1(sK0,sK1)) != iProver_top
% 2.53/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.53/0.99      | r1_tarski(k5_tmap_1(sK0,X0),k5_tmap_1(sK0,sK1)) = iProver_top ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_1459,c_2589]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_2986,plain,
% 2.53/0.99      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 2.53/0.99      | v1_tops_2(k5_tmap_1(sK0,X0),sK0) != iProver_top
% 2.53/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.53/0.99      | r1_tarski(k5_tmap_1(sK0,X0),k5_tmap_1(sK0,sK1)) = iProver_top ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_2397,c_2597]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f71]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1468,plain,
% 2.53/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_5,plain,
% 2.53/0.99      ( v1_tops_2(X0,X1)
% 2.53/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.53/0.99      | ~ r1_tarski(X0,u1_pre_topc(X1))
% 2.53/0.99      | ~ l1_pre_topc(X1) ),
% 2.53/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1467,plain,
% 2.53/0.99      ( v1_tops_2(X0,X1) = iProver_top
% 2.53/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
% 2.53/0.99      | r1_tarski(X0,u1_pre_topc(X1)) != iProver_top
% 2.53/0.99      | l1_pre_topc(X1) != iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_2308,plain,
% 2.53/0.99      ( v1_tops_2(X0,k6_tmap_1(sK0,sK1)) = iProver_top
% 2.53/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 2.53/0.99      | r1_tarski(X0,u1_pre_topc(k6_tmap_1(sK0,sK1))) != iProver_top
% 2.53/0.99      | l1_pre_topc(k6_tmap_1(sK0,sK1)) != iProver_top ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_1647,c_1467]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_2313,plain,
% 2.53/0.99      ( v1_tops_2(X0,k6_tmap_1(sK0,sK1)) = iProver_top
% 2.53/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 2.53/0.99      | r1_tarski(X0,k5_tmap_1(sK0,sK1)) != iProver_top
% 2.53/0.99      | l1_pre_topc(k6_tmap_1(sK0,sK1)) != iProver_top ),
% 2.53/0.99      inference(light_normalisation,[status(thm)],[c_2308,c_1680]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_2711,plain,
% 2.53/0.99      ( r1_tarski(X0,k5_tmap_1(sK0,sK1)) != iProver_top
% 2.53/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 2.53/0.99      | v1_tops_2(X0,k6_tmap_1(sK0,sK1)) = iProver_top ),
% 2.53/0.99      inference(global_propositional_subsumption,
% 2.53/0.99                [status(thm)],
% 2.53/0.99                [c_2313,c_29,c_1597]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_2712,plain,
% 2.53/0.99      ( v1_tops_2(X0,k6_tmap_1(sK0,sK1)) = iProver_top
% 2.53/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 2.53/0.99      | r1_tarski(X0,k5_tmap_1(sK0,sK1)) != iProver_top ),
% 2.53/0.99      inference(renaming,[status(thm)],[c_2711]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_2720,plain,
% 2.53/0.99      ( v1_tops_2(k5_tmap_1(sK0,X0),k6_tmap_1(sK0,sK1)) = iProver_top
% 2.53/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.53/0.99      | r1_tarski(k5_tmap_1(sK0,X0),k5_tmap_1(sK0,sK1)) != iProver_top ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_1459,c_2712]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_2728,plain,
% 2.53/0.99      ( v1_tops_2(k5_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) = iProver_top
% 2.53/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_1468,c_2720]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_3148,plain,
% 2.53/0.99      ( v1_tops_2(k5_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) = iProver_top ),
% 2.53/0.99      inference(global_propositional_subsumption,[status(thm)],[c_2728,c_29]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_8,plain,
% 2.53/0.99      ( v1_tops_2(X0,X1)
% 2.53/0.99      | ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.53/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
% 2.53/0.99      | v2_struct_0(X1)
% 2.53/0.99      | ~ v2_pre_topc(X1)
% 2.53/0.99      | ~ l1_pre_topc(X1) ),
% 2.53/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_635,plain,
% 2.53/0.99      ( v1_tops_2(X0,X1)
% 2.53/0.99      | ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 2.53/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
% 2.53/0.99      | ~ v2_pre_topc(X1)
% 2.53/0.99      | ~ l1_pre_topc(X1)
% 2.53/0.99      | sK0 != X1 ),
% 2.53/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_25]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_636,plain,
% 2.53/0.99      ( ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 2.53/0.99      | v1_tops_2(X0,sK0)
% 2.53/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
% 2.53/0.99      | ~ v2_pre_topc(sK0)
% 2.53/0.99      | ~ l1_pre_topc(sK0) ),
% 2.53/0.99      inference(unflattening,[status(thm)],[c_635]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_640,plain,
% 2.53/0.99      ( ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
% 2.53/0.99      | v1_tops_2(X0,sK0)
% 2.53/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
% 2.53/0.99      inference(global_propositional_subsumption,
% 2.53/0.99                [status(thm)],
% 2.53/0.99                [c_636,c_24,c_23]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1455,plain,
% 2.53/0.99      ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 2.53/0.99      | v1_tops_2(X0,sK0) = iProver_top
% 2.53/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) != iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_640]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_2176,plain,
% 2.53/0.99      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 2.53/0.99      | v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 2.53/0.99      | v1_tops_2(X0,sK0) = iProver_top
% 2.53/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))) != iProver_top ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_858,c_1455]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_2181,plain,
% 2.53/0.99      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 2.53/0.99      | v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != iProver_top
% 2.53/0.99      | v1_tops_2(X0,sK0) = iProver_top
% 2.53/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 2.53/0.99      inference(light_normalisation,[status(thm)],[c_2176,c_1647]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_2885,plain,
% 2.53/0.99      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 2.53/0.99      | v1_tops_2(X0,k6_tmap_1(sK0,sK1)) != iProver_top
% 2.53/0.99      | v1_tops_2(X0,sK0) = iProver_top
% 2.53/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_858,c_2181]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_2995,plain,
% 2.53/0.99      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 2.53/0.99      | v1_tops_2(k5_tmap_1(sK0,X0),k6_tmap_1(sK0,sK1)) != iProver_top
% 2.53/0.99      | v1_tops_2(k5_tmap_1(sK0,X0),sK0) = iProver_top
% 2.53/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_1459,c_2885]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_3159,plain,
% 2.53/0.99      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 2.53/0.99      | v1_tops_2(k5_tmap_1(sK0,sK1),sK0) = iProver_top
% 2.53/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_3148,c_2995]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_28,plain,
% 2.53/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_84,plain,
% 2.53/0.99      ( r1_tarski(sK0,sK0) ),
% 2.53/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_0,plain,
% 2.53/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.53/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_88,plain,
% 2.53/0.99      ( ~ r1_tarski(sK0,sK0) | sK0 = sK0 ),
% 2.53/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1030,plain,
% 2.53/0.99      ( X0 != X1 | u1_pre_topc(X0) = u1_pre_topc(X1) ),
% 2.53/0.99      theory(equality) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1040,plain,
% 2.53/0.99      ( u1_pre_topc(sK0) = u1_pre_topc(sK0) | sK0 != sK0 ),
% 2.53/0.99      inference(instantiation,[status(thm)],[c_1030]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1599,plain,
% 2.53/0.99      ( m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 2.53/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.53/0.99      inference(instantiation,[status(thm)],[c_562]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1600,plain,
% 2.53/0.99      ( m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 2.53/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_1599]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1629,plain,
% 2.53/0.99      ( r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0)) ),
% 2.53/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1631,plain,
% 2.53/0.99      ( r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0)) = iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_1629]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1633,plain,
% 2.53/0.99      ( r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK0)) = iProver_top ),
% 2.53/0.99      inference(instantiation,[status(thm)],[c_1631]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1029,plain,
% 2.53/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.53/0.99      theory(equality) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1624,plain,
% 2.53/0.99      ( ~ r1_tarski(X0,X1)
% 2.53/0.99      | r1_tarski(X2,u1_pre_topc(X3))
% 2.53/0.99      | X2 != X0
% 2.53/0.99      | u1_pre_topc(X3) != X1 ),
% 2.53/0.99      inference(instantiation,[status(thm)],[c_1029]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1685,plain,
% 2.53/0.99      ( ~ r1_tarski(X0,u1_pre_topc(X1))
% 2.53/0.99      | r1_tarski(X2,u1_pre_topc(X1))
% 2.53/0.99      | X2 != X0
% 2.53/0.99      | u1_pre_topc(X1) != u1_pre_topc(X1) ),
% 2.53/0.99      inference(instantiation,[status(thm)],[c_1624]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1898,plain,
% 2.53/0.99      ( r1_tarski(X0,u1_pre_topc(X1))
% 2.53/0.99      | ~ r1_tarski(u1_pre_topc(X1),u1_pre_topc(X1))
% 2.53/0.99      | X0 != u1_pre_topc(X1)
% 2.53/0.99      | u1_pre_topc(X1) != u1_pre_topc(X1) ),
% 2.53/0.99      inference(instantiation,[status(thm)],[c_1685]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_3219,plain,
% 2.53/0.99      ( r1_tarski(k5_tmap_1(sK0,sK1),u1_pre_topc(sK0))
% 2.53/0.99      | ~ r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK0))
% 2.53/0.99      | k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0)
% 2.53/0.99      | u1_pre_topc(sK0) != u1_pre_topc(sK0) ),
% 2.53/0.99      inference(instantiation,[status(thm)],[c_1898]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_3222,plain,
% 2.53/0.99      ( k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0)
% 2.53/0.99      | u1_pre_topc(sK0) != u1_pre_topc(sK0)
% 2.53/0.99      | r1_tarski(k5_tmap_1(sK0,sK1),u1_pre_topc(sK0)) = iProver_top
% 2.53/0.99      | r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK0)) != iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_3219]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_3390,plain,
% 2.53/0.99      ( v1_tops_2(k5_tmap_1(sK0,sK1),X0)
% 2.53/0.99      | ~ m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.53/0.99      | ~ r1_tarski(k5_tmap_1(sK0,sK1),u1_pre_topc(X0))
% 2.53/0.99      | ~ l1_pre_topc(X0) ),
% 2.53/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_3391,plain,
% 2.53/0.99      ( v1_tops_2(k5_tmap_1(sK0,sK1),X0) = iProver_top
% 2.53/0.99      | m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
% 2.53/0.99      | r1_tarski(k5_tmap_1(sK0,sK1),u1_pre_topc(X0)) != iProver_top
% 2.53/0.99      | l1_pre_topc(X0) != iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_3390]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_3393,plain,
% 2.53/0.99      ( v1_tops_2(k5_tmap_1(sK0,sK1),sK0) = iProver_top
% 2.53/0.99      | m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 2.53/0.99      | r1_tarski(k5_tmap_1(sK0,sK1),u1_pre_topc(sK0)) != iProver_top
% 2.53/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 2.53/0.99      inference(instantiation,[status(thm)],[c_3391]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_3622,plain,
% 2.53/0.99      ( v1_tops_2(k5_tmap_1(sK0,sK1),sK0) = iProver_top ),
% 2.53/0.99      inference(global_propositional_subsumption,
% 2.53/0.99                [status(thm)],
% 2.53/0.99                [c_3159,c_28,c_29,c_84,c_88,c_1040,c_1600,c_1633,c_3222,c_3393]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_2262,plain,
% 2.53/0.99      ( v1_tops_2(k5_tmap_1(sK0,X0),sK0) != iProver_top
% 2.53/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.53/0.99      | r1_tarski(k5_tmap_1(sK0,X0),u1_pre_topc(sK0)) = iProver_top
% 2.53/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_1459,c_1466]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_2470,plain,
% 2.53/0.99      ( r1_tarski(k5_tmap_1(sK0,X0),u1_pre_topc(sK0)) = iProver_top
% 2.53/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.53/0.99      | v1_tops_2(k5_tmap_1(sK0,X0),sK0) != iProver_top ),
% 2.53/0.99      inference(global_propositional_subsumption,[status(thm)],[c_2262,c_28]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_2471,plain,
% 2.53/0.99      ( v1_tops_2(k5_tmap_1(sK0,X0),sK0) != iProver_top
% 2.53/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.53/0.99      | r1_tarski(k5_tmap_1(sK0,X0),u1_pre_topc(sK0)) = iProver_top ),
% 2.53/0.99      inference(renaming,[status(thm)],[c_2470]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_19,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/0.99      | r1_tarski(u1_pre_topc(X1),k5_tmap_1(X1,X0))
% 2.53/0.99      | v2_struct_0(X1)
% 2.53/0.99      | ~ v2_pre_topc(X1)
% 2.53/0.99      | ~ l1_pre_topc(X1) ),
% 2.53/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_467,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/0.99      | r1_tarski(u1_pre_topc(X1),k5_tmap_1(X1,X0))
% 2.53/0.99      | ~ v2_pre_topc(X1)
% 2.53/0.99      | ~ l1_pre_topc(X1)
% 2.53/0.99      | sK0 != X1 ),
% 2.53/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_25]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_468,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/0.99      | r1_tarski(u1_pre_topc(sK0),k5_tmap_1(sK0,X0))
% 2.53/0.99      | ~ v2_pre_topc(sK0)
% 2.53/0.99      | ~ l1_pre_topc(sK0) ),
% 2.53/0.99      inference(unflattening,[status(thm)],[c_467]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_472,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/0.99      | r1_tarski(u1_pre_topc(sK0),k5_tmap_1(sK0,X0)) ),
% 2.53/0.99      inference(global_propositional_subsumption,
% 2.53/0.99                [status(thm)],
% 2.53/0.99                [c_468,c_24,c_23]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1463,plain,
% 2.53/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.53/0.99      | r1_tarski(u1_pre_topc(sK0),k5_tmap_1(sK0,X0)) = iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_472]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1469,plain,
% 2.53/0.99      ( X0 = X1
% 2.53/0.99      | r1_tarski(X0,X1) != iProver_top
% 2.53/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1912,plain,
% 2.53/0.99      ( k5_tmap_1(sK0,X0) = u1_pre_topc(sK0)
% 2.53/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.53/0.99      | r1_tarski(k5_tmap_1(sK0,X0),u1_pre_topc(sK0)) != iProver_top ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_1463,c_1469]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_2480,plain,
% 2.53/0.99      ( k5_tmap_1(sK0,X0) = u1_pre_topc(sK0)
% 2.53/0.99      | v1_tops_2(k5_tmap_1(sK0,X0),sK0) != iProver_top
% 2.53/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_2471,c_1912]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_3627,plain,
% 2.53/0.99      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 2.53/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_3622,c_2480]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_3718,plain,
% 2.53/0.99      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0) ),
% 2.53/0.99      inference(global_propositional_subsumption,
% 2.53/0.99                [status(thm)],
% 2.53/0.99                [c_2986,c_29,c_3627]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_11,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/0.99      | v2_struct_0(X1)
% 2.53/0.99      | ~ v2_pre_topc(X1)
% 2.53/0.99      | ~ l1_pre_topc(X1)
% 2.53/0.99      | g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X0)) = k6_tmap_1(X1,X0) ),
% 2.53/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_575,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/0.99      | ~ v2_pre_topc(X1)
% 2.53/0.99      | ~ l1_pre_topc(X1)
% 2.53/0.99      | g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X0)) = k6_tmap_1(X1,X0)
% 2.53/0.99      | sK0 != X1 ),
% 2.53/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_25]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_576,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/0.99      | ~ v2_pre_topc(sK0)
% 2.53/0.99      | ~ l1_pre_topc(sK0)
% 2.53/0.99      | g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) = k6_tmap_1(sK0,X0) ),
% 2.53/0.99      inference(unflattening,[status(thm)],[c_575]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_580,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/0.99      | g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) = k6_tmap_1(sK0,X0) ),
% 2.53/0.99      inference(global_propositional_subsumption,
% 2.53/0.99                [status(thm)],
% 2.53/0.99                [c_576,c_24,c_23]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1458,plain,
% 2.53/0.99      ( g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) = k6_tmap_1(sK0,X0)
% 2.53/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.53/0.99      inference(predicate_to_equality,[status(thm)],[c_580]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_1919,plain,
% 2.53/0.99      ( g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) = k6_tmap_1(sK0,sK1) ),
% 2.53/0.99      inference(superposition,[status(thm)],[c_1465,c_1458]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_3727,plain,
% 2.53/0.99      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 2.53/0.99      inference(demodulation,[status(thm)],[c_3718,c_1919]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_15,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/0.99      | r2_hidden(X0,u1_pre_topc(X1))
% 2.53/0.99      | v2_struct_0(X1)
% 2.53/0.99      | ~ v2_pre_topc(X1)
% 2.53/0.99      | ~ l1_pre_topc(X1)
% 2.53/0.99      | k5_tmap_1(X1,X0) != u1_pre_topc(X1) ),
% 2.53/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_3,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/0.99      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 2.53/0.99      | v3_pre_topc(X0,X1)
% 2.53/0.99      | ~ l1_pre_topc(X1) ),
% 2.53/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_20,negated_conjecture,
% 2.53/0.99      ( ~ v3_pre_topc(sK1,sK0)
% 2.53/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 2.53/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_195,plain,
% 2.53/0.99      ( ~ v3_pre_topc(sK1,sK0)
% 2.53/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 2.53/0.99      inference(prop_impl,[status(thm)],[c_20]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_333,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/0.99      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 2.53/0.99      | ~ l1_pre_topc(X1)
% 2.53/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
% 2.53/0.99      | sK1 != X0
% 2.53/0.99      | sK0 != X1 ),
% 2.53/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_195]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_334,plain,
% 2.53/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/0.99      | ~ r2_hidden(sK1,u1_pre_topc(sK0))
% 2.53/0.99      | ~ l1_pre_topc(sK0)
% 2.53/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 2.53/0.99      inference(unflattening,[status(thm)],[c_333]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_336,plain,
% 2.53/0.99      ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
% 2.53/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 2.53/0.99      inference(global_propositional_subsumption,
% 2.53/0.99                [status(thm)],
% 2.53/0.99                [c_334,c_23,c_22]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_369,plain,
% 2.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/0.99      | v2_struct_0(X1)
% 2.53/0.99      | ~ v2_pre_topc(X1)
% 2.53/0.99      | ~ l1_pre_topc(X1)
% 2.53/0.99      | k5_tmap_1(X1,X0) != u1_pre_topc(X1)
% 2.53/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
% 2.53/0.99      | u1_pre_topc(X1) != u1_pre_topc(sK0)
% 2.53/0.99      | sK1 != X0 ),
% 2.53/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_336]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_370,plain,
% 2.53/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.53/0.99      | v2_struct_0(X0)
% 2.53/0.99      | ~ v2_pre_topc(X0)
% 2.53/0.99      | ~ l1_pre_topc(X0)
% 2.53/0.99      | k5_tmap_1(X0,sK1) != u1_pre_topc(X0)
% 2.53/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
% 2.53/0.99      | u1_pre_topc(X0) != u1_pre_topc(sK0) ),
% 2.53/0.99      inference(unflattening,[status(thm)],[c_369]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_453,plain,
% 2.53/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.53/0.99      | ~ v2_pre_topc(X0)
% 2.53/0.99      | ~ l1_pre_topc(X0)
% 2.53/0.99      | k5_tmap_1(X0,sK1) != u1_pre_topc(X0)
% 2.53/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
% 2.53/0.99      | u1_pre_topc(X0) != u1_pre_topc(sK0)
% 2.53/0.99      | sK0 != X0 ),
% 2.53/0.99      inference(resolution_lifted,[status(thm)],[c_370,c_25]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_454,plain,
% 2.53/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.53/0.99      | ~ v2_pre_topc(sK0)
% 2.53/0.99      | ~ l1_pre_topc(sK0)
% 2.53/0.99      | k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0)
% 2.53/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
% 2.53/0.99      | u1_pre_topc(sK0) != u1_pre_topc(sK0) ),
% 2.53/0.99      inference(unflattening,[status(thm)],[c_453]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_456,plain,
% 2.53/0.99      ( k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0)
% 2.53/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
% 2.53/0.99      | u1_pre_topc(sK0) != u1_pre_topc(sK0) ),
% 2.53/0.99      inference(global_propositional_subsumption,
% 2.53/0.99                [status(thm)],
% 2.53/0.99                [c_454,c_25,c_24,c_23,c_22,c_372]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_826,plain,
% 2.53/0.99      ( k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0)
% 2.53/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 2.53/0.99      inference(equality_resolution_simp,[status(thm)],[c_456]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_856,plain,
% 2.53/0.99      ( k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0)
% 2.53/0.99      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 2.53/0.99      inference(prop_impl,[status(thm)],[c_826]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_3728,plain,
% 2.53/0.99      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
% 2.53/0.99      | u1_pre_topc(sK0) != u1_pre_topc(sK0) ),
% 2.53/0.99      inference(demodulation,[status(thm)],[c_3718,c_856]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_3732,plain,
% 2.53/0.99      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 2.53/0.99      inference(equality_resolution_simp,[status(thm)],[c_3728]) ).
% 2.53/0.99  
% 2.53/0.99  cnf(c_3736,plain,
% 2.53/0.99      ( $false ),
% 2.53/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_3727,c_3732]) ).
% 2.53/0.99  
% 2.53/0.99  
% 2.53/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.53/0.99  
% 2.53/0.99  ------                               Statistics
% 2.53/0.99  
% 2.53/0.99  ------ General
% 2.53/0.99  
% 2.53/0.99  abstr_ref_over_cycles:                  0
% 2.53/0.99  abstr_ref_under_cycles:                 0
% 2.53/0.99  gc_basic_clause_elim:                   0
% 2.53/0.99  forced_gc_time:                         0
% 2.53/0.99  parsing_time:                           0.01
% 2.53/0.99  unif_index_cands_time:                  0.
% 2.53/0.99  unif_index_add_time:                    0.
% 2.53/0.99  orderings_time:                         0.
% 2.53/0.99  out_proof_time:                         0.01
% 2.53/0.99  total_time:                             0.144
% 2.53/0.99  num_of_symbols:                         47
% 2.53/0.99  num_of_terms:                           1665
% 2.53/0.99  
% 2.53/0.99  ------ Preprocessing
% 2.53/0.99  
% 2.53/0.99  num_of_splits:                          0
% 2.53/0.99  num_of_split_atoms:                     0
% 2.53/0.99  num_of_reused_defs:                     0
% 2.53/0.99  num_eq_ax_congr_red:                    6
% 2.53/0.99  num_of_sem_filtered_clauses:            1
% 2.53/0.99  num_of_subtypes:                        0
% 2.53/0.99  monotx_restored_types:                  0
% 2.53/0.99  sat_num_of_epr_types:                   0
% 2.53/0.99  sat_num_of_non_cyclic_types:            0
% 2.53/0.99  sat_guarded_non_collapsed_types:        0
% 2.53/0.99  num_pure_diseq_elim:                    0
% 2.53/0.99  simp_replaced_by:                       0
% 2.53/0.99  res_preprocessed:                       104
% 2.53/0.99  prep_upred:                             0
% 2.53/0.99  prep_unflattend:                        27
% 2.53/0.99  smt_new_axioms:                         0
% 2.53/0.99  pred_elim_cands:                        4
% 2.53/0.99  pred_elim:                              4
% 2.53/0.99  pred_elim_cl:                           7
% 2.53/0.99  pred_elim_cycles:                       6
% 2.53/0.99  merged_defs:                            8
% 2.53/0.99  merged_defs_ncl:                        0
% 2.53/0.99  bin_hyper_res:                          8
% 2.53/0.99  prep_cycles:                            4
% 2.53/0.99  pred_elim_time:                         0.012
% 2.53/0.99  splitting_time:                         0.
% 2.53/0.99  sem_filter_time:                        0.
% 2.53/0.99  monotx_time:                            0.
% 2.53/0.99  subtype_inf_time:                       0.
% 2.53/0.99  
% 2.53/0.99  ------ Problem properties
% 2.53/0.99  
% 2.53/0.99  clauses:                                18
% 2.53/0.99  conjectures:                            2
% 2.53/0.99  epr:                                    3
% 2.53/0.99  horn:                                   17
% 2.53/0.99  ground:                                 4
% 2.53/0.99  unary:                                  3
% 2.53/0.99  binary:                                 8
% 2.53/0.99  lits:                                   42
% 2.53/0.99  lits_eq:                                8
% 2.53/0.99  fd_pure:                                0
% 2.53/0.99  fd_pseudo:                              0
% 2.53/0.99  fd_cond:                                0
% 2.53/0.99  fd_pseudo_cond:                         1
% 2.53/0.99  ac_symbols:                             0
% 2.53/0.99  
% 2.53/0.99  ------ Propositional Solver
% 2.53/0.99  
% 2.53/0.99  prop_solver_calls:                      29
% 2.53/0.99  prop_fast_solver_calls:                 884
% 2.53/0.99  smt_solver_calls:                       0
% 2.53/0.99  smt_fast_solver_calls:                  0
% 2.53/0.99  prop_num_of_clauses:                    1020
% 2.53/0.99  prop_preprocess_simplified:             4232
% 2.53/0.99  prop_fo_subsumed:                       44
% 2.53/0.99  prop_solver_time:                       0.
% 2.53/0.99  smt_solver_time:                        0.
% 2.53/0.99  smt_fast_solver_time:                   0.
% 2.53/0.99  prop_fast_solver_time:                  0.
% 2.53/0.99  prop_unsat_core_time:                   0.
% 2.53/0.99  
% 2.53/0.99  ------ QBF
% 2.53/0.99  
% 2.53/0.99  qbf_q_res:                              0
% 2.53/0.99  qbf_num_tautologies:                    0
% 2.53/0.99  qbf_prep_cycles:                        0
% 2.53/0.99  
% 2.53/0.99  ------ BMC1
% 2.53/0.99  
% 2.53/0.99  bmc1_current_bound:                     -1
% 2.53/0.99  bmc1_last_solved_bound:                 -1
% 2.53/0.99  bmc1_unsat_core_size:                   -1
% 2.53/0.99  bmc1_unsat_core_parents_size:           -1
% 2.53/0.99  bmc1_merge_next_fun:                    0
% 2.53/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.53/0.99  
% 2.53/0.99  ------ Instantiation
% 2.53/0.99  
% 2.53/0.99  inst_num_of_clauses:                    327
% 2.53/0.99  inst_num_in_passive:                    68
% 2.53/0.99  inst_num_in_active:                     201
% 2.53/0.99  inst_num_in_unprocessed:                58
% 2.53/0.99  inst_num_of_loops:                      220
% 2.53/0.99  inst_num_of_learning_restarts:          0
% 2.53/0.99  inst_num_moves_active_passive:          13
% 2.53/0.99  inst_lit_activity:                      0
% 2.53/0.99  inst_lit_activity_moves:                0
% 2.53/0.99  inst_num_tautologies:                   0
% 2.53/0.99  inst_num_prop_implied:                  0
% 2.53/0.99  inst_num_existing_simplified:           0
% 2.53/0.99  inst_num_eq_res_simplified:             0
% 2.53/0.99  inst_num_child_elim:                    0
% 2.53/0.99  inst_num_of_dismatching_blockings:      159
% 2.53/0.99  inst_num_of_non_proper_insts:           449
% 2.53/0.99  inst_num_of_duplicates:                 0
% 2.53/0.99  inst_inst_num_from_inst_to_res:         0
% 2.53/0.99  inst_dismatching_checking_time:         0.
% 2.53/0.99  
% 2.53/0.99  ------ Resolution
% 2.53/0.99  
% 2.53/0.99  res_num_of_clauses:                     0
% 2.53/0.99  res_num_in_passive:                     0
% 2.53/0.99  res_num_in_active:                      0
% 2.53/0.99  res_num_of_loops:                       108
% 2.53/0.99  res_forward_subset_subsumed:            70
% 2.53/0.99  res_backward_subset_subsumed:           2
% 2.53/0.99  res_forward_subsumed:                   0
% 2.53/0.99  res_backward_subsumed:                  0
% 2.53/0.99  res_forward_subsumption_resolution:     0
% 2.53/0.99  res_backward_subsumption_resolution:    0
% 2.53/0.99  res_clause_to_clause_subsumption:       149
% 2.53/0.99  res_orphan_elimination:                 0
% 2.53/0.99  res_tautology_del:                      112
% 2.53/0.99  res_num_eq_res_simplified:              2
% 2.53/0.99  res_num_sel_changes:                    0
% 2.53/0.99  res_moves_from_active_to_pass:          0
% 2.53/0.99  
% 2.53/0.99  ------ Superposition
% 2.53/0.99  
% 2.53/0.99  sup_time_total:                         0.
% 2.53/0.99  sup_time_generating:                    0.
% 2.53/0.99  sup_time_sim_full:                      0.
% 2.53/0.99  sup_time_sim_immed:                     0.
% 2.53/0.99  
% 2.53/0.99  sup_num_of_clauses:                     28
% 2.53/0.99  sup_num_in_active:                      24
% 2.53/0.99  sup_num_in_passive:                     4
% 2.53/0.99  sup_num_of_loops:                       42
% 2.53/0.99  sup_fw_superposition:                   34
% 2.53/0.99  sup_bw_superposition:                   8
% 2.53/0.99  sup_immediate_simplified:               11
% 2.53/0.99  sup_given_eliminated:                   0
% 2.53/0.99  comparisons_done:                       0
% 2.53/0.99  comparisons_avoided:                    9
% 2.53/0.99  
% 2.53/0.99  ------ Simplifications
% 2.53/0.99  
% 2.53/0.99  
% 2.53/0.99  sim_fw_subset_subsumed:                 2
% 2.53/0.99  sim_bw_subset_subsumed:                 10
% 2.53/0.99  sim_fw_subsumed:                        2
% 2.53/0.99  sim_bw_subsumed:                        0
% 2.53/0.99  sim_fw_subsumption_res:                 1
% 2.53/0.99  sim_bw_subsumption_res:                 0
% 2.53/0.99  sim_tautology_del:                      8
% 2.53/0.99  sim_eq_tautology_del:                   2
% 2.53/0.99  sim_eq_res_simp:                        1
% 2.53/0.99  sim_fw_demodulated:                     0
% 2.53/0.99  sim_bw_demodulated:                     9
% 2.53/0.99  sim_light_normalised:                   7
% 2.53/0.99  sim_joinable_taut:                      0
% 2.53/0.99  sim_joinable_simp:                      0
% 2.53/0.99  sim_ac_normalised:                      0
% 2.53/0.99  sim_smt_subsumption:                    0
% 2.53/0.99  
%------------------------------------------------------------------------------
