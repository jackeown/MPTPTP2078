%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:48 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_42)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v2_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f58,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f59,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
     => ( ( ~ v1_zfmisc_1(sK3)
          | ~ v2_tex_2(sK3,X0) )
        & ( v1_zfmisc_1(sK3)
          | v2_tex_2(sK3,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_zfmisc_1(X1)
              | ~ v2_tex_2(X1,X0) )
            & ( v1_zfmisc_1(X1)
              | v2_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,sK2) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK2)
      & v2_tdlat_3(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ( ~ v1_zfmisc_1(sK3)
      | ~ v2_tex_2(sK3,sK2) )
    & ( v1_zfmisc_1(sK3)
      | v2_tex_2(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & ~ v1_xboole_0(sK3)
    & l1_pre_topc(sK2)
    & v2_tdlat_3(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f59,f61,f60])).

fof(f98,plain,
    ( v1_zfmisc_1(sK3)
    | v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f97,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f62])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_tdlat_3(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK1(X0,X1)) = X1
        & m1_pre_topc(sK1(X0,X1),X0)
        & v1_tdlat_3(sK1(X0,X1))
        & ~ v2_struct_0(sK1(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK1(X0,X1)) = X1
            & m1_pre_topc(sK1(X0,X1),X0)
            & v1_tdlat_3(sK1(X0,X1))
            & ~ v2_struct_0(sK1(X0,X1)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f44,f56])).

fof(f90,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK1(X0,X1)) = X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f92,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f93,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f95,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f96,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f50,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f49])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f50,f51])).

fof(f64,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f16,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f86,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( v2_tdlat_3(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_pre_topc(X0)
          & v7_struct_0(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f83,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f81,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f76,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ( v2_struct_0(X0)
       => v7_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f75,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f78,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(sK1(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK1(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f77,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_tdlat_3(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v2_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f94,plain,(
    v2_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f63,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f99,plain,
    ( ~ v1_zfmisc_1(sK3)
    | ~ v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_5068,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_zfmisc_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_9054,plain,
    ( v1_zfmisc_1(X0)
    | ~ v1_zfmisc_1(u1_struct_0(sK1(X1,sK3)))
    | X0 != u1_struct_0(sK1(X1,sK3)) ),
    inference(instantiation,[status(thm)],[c_5068])).

cnf(c_11492,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK1(X0,sK3)))
    | v1_zfmisc_1(sK3)
    | sK3 != u1_struct_0(sK1(X0,sK3)) ),
    inference(instantiation,[status(thm)],[c_9054])).

cnf(c_11494,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK1(sK2,sK3)))
    | v1_zfmisc_1(sK3)
    | sK3 != u1_struct_0(sK1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_11492])).

cnf(c_30,negated_conjecture,
    ( v2_tex_2(sK3,sK2)
    | v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_5883,plain,
    ( v2_tex_2(sK3,sK2) = iProver_top
    | v1_zfmisc_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_5882,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_24,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_5889,plain,
    ( u1_struct_0(sK1(X0,X1)) = X1
    | v2_tex_2(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_7612,plain,
    ( u1_struct_0(sK1(sK2,sK3)) = sK3
    | v2_tex_2(sK3,sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5882,c_5889])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_37,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_38,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_40,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_41,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_7756,plain,
    ( u1_struct_0(sK1(sK2,sK3)) = sK3
    | v2_tex_2(sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7612,c_37,c_38,c_40,c_41])).

cnf(c_7762,plain,
    ( u1_struct_0(sK1(sK2,sK3)) = sK3
    | v1_zfmisc_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5883,c_7756])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_4,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_282,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_tarski(X0),X1) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_283,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_282])).

cnf(c_755,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | v1_xboole_0(X2)
    | X1 != X2
    | sK0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_283])).

cnf(c_756,plain,
    ( r1_tarski(k1_tarski(sK0(X0)),X0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_755])).

cnf(c_5870,plain,
    ( r1_tarski(k1_tarski(sK0(X0)),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_756])).

cnf(c_23,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_5890,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_7383,plain,
    ( k1_tarski(sK0(X0)) = X0
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_tarski(sK0(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5870,c_5890])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_5899,plain,
    ( v1_xboole_0(k1_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_10039,plain,
    ( k1_tarski(sK0(X0)) = X0
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7383,c_5899])).

cnf(c_10045,plain,
    ( u1_struct_0(sK1(sK2,sK3)) = sK3
    | k1_tarski(sK0(sK3)) = sK3
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_7762,c_10039])).

cnf(c_10074,plain,
    ( v1_xboole_0(sK3)
    | u1_struct_0(sK1(sK2,sK3)) = sK3
    | k1_tarski(sK0(sK3)) = sK3 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10045])).

cnf(c_10191,plain,
    ( k1_tarski(sK0(sK3)) = sK3
    | u1_struct_0(sK1(sK2,sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10045,c_32,c_10074])).

cnf(c_10192,plain,
    ( u1_struct_0(sK1(sK2,sK3)) = sK3
    | k1_tarski(sK0(sK3)) = sK3 ),
    inference(renaming,[status(thm)],[c_10191])).

cnf(c_28,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_5885,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_10197,plain,
    ( k1_tarski(sK0(sK3)) = sK3
    | v2_tex_2(k6_domain_1(sK3,X0),sK1(sK2,sK3)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1(sK2,sK3))) != iProver_top
    | v2_pre_topc(sK1(sK2,sK3)) != iProver_top
    | l1_pre_topc(sK1(sK2,sK3)) != iProver_top
    | v2_struct_0(sK1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10192,c_5885])).

cnf(c_20,plain,
    ( ~ v2_tdlat_3(X0)
    | ~ v1_tdlat_3(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v7_struct_0(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_18,plain,
    ( ~ v2_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_13,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_12,plain,
    ( ~ l1_struct_0(X0)
    | ~ v2_struct_0(X0)
    | v7_struct_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_204,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_tdlat_3(X0)
    | ~ v1_tdlat_3(X0)
    | v7_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_18,c_13,c_12])).

cnf(c_205,plain,
    ( ~ v2_tdlat_3(X0)
    | ~ v1_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | v7_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_204])).

cnf(c_15,plain,
    ( v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | ~ v7_struct_0(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_479,plain,
    ( v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | ~ v7_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_13,c_15])).

cnf(c_525,plain,
    ( ~ v2_tdlat_3(X0)
    | ~ v1_tdlat_3(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_205,c_479])).

cnf(c_5875,plain,
    ( v2_tdlat_3(X0) != iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_525])).

cnf(c_10195,plain,
    ( k1_tarski(sK0(sK3)) = sK3
    | v2_tdlat_3(sK1(sK2,sK3)) != iProver_top
    | v1_tdlat_3(sK1(sK2,sK3)) != iProver_top
    | v1_zfmisc_1(sK3) = iProver_top
    | l1_pre_topc(sK1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10192,c_5875])).

cnf(c_43,plain,
    ( v2_tex_2(sK3,sK2) = iProver_top
    | v1_zfmisc_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_26,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tdlat_3(sK1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_290,plain,
    ( v1_zfmisc_1(sK3)
    | v2_tex_2(sK3,sK2) ),
    inference(prop_impl,[status(thm)],[c_30])).

cnf(c_291,plain,
    ( v2_tex_2(sK3,sK2)
    | v1_zfmisc_1(sK3) ),
    inference(renaming,[status(thm)],[c_290])).

cnf(c_1043,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tdlat_3(sK1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(sK3)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | sK2 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_291])).

cnf(c_1044,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_tdlat_3(sK1(sK2,sK3))
    | ~ v2_pre_topc(sK2)
    | v1_zfmisc_1(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1043])).

cnf(c_1046,plain,
    ( v1_zfmisc_1(sK3)
    | v1_tdlat_3(sK1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1044,c_36,c_35,c_33,c_32,c_31])).

cnf(c_1047,plain,
    ( v1_tdlat_3(sK1(sK2,sK3))
    | v1_zfmisc_1(sK3) ),
    inference(renaming,[status(thm)],[c_1046])).

cnf(c_1048,plain,
    ( v1_tdlat_3(sK1(sK2,sK3)) = iProver_top
    | v1_zfmisc_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1047])).

cnf(c_25,plain,
    ( ~ v2_tex_2(X0,X1)
    | m1_pre_topc(sK1(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_5888,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | m1_pre_topc(sK1(X1,X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_8406,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | m1_pre_topc(sK1(sK2,sK3),sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5882,c_5888])).

cnf(c_2663,plain,
    ( ~ v2_tex_2(X0,X1)
    | m1_pre_topc(sK1(X1,X0),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(sK2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_31])).

cnf(c_2664,plain,
    ( ~ v2_tex_2(sK3,X0)
    | m1_pre_topc(sK1(X0,sK3),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v1_xboole_0(sK3)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_2663])).

cnf(c_2668,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | m1_pre_topc(sK1(X0,sK3),X0)
    | ~ v2_tex_2(sK3,X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2664,c_32])).

cnf(c_2669,plain,
    ( ~ v2_tex_2(sK3,X0)
    | m1_pre_topc(sK1(X0,sK3),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_2668])).

cnf(c_2670,plain,
    ( k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK2))
    | v2_tex_2(sK3,X0) != iProver_top
    | m1_pre_topc(sK1(X0,sK3),X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2669])).

cnf(c_2672,plain,
    ( k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
    | v2_tex_2(sK3,sK2) != iProver_top
    | m1_pre_topc(sK1(sK2,sK3),sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2670])).

cnf(c_5057,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_7799,plain,
    ( k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_5057])).

cnf(c_8841,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | m1_pre_topc(sK1(sK2,sK3),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8406,c_37,c_38,c_40,c_41,c_42,c_6309])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_5894,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_8847,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | l1_pre_topc(sK1(sK2,sK3)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8841,c_5894])).

cnf(c_22,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_tdlat_3(X1)
    | v2_tdlat_3(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1293,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_tdlat_3(X2)
    | ~ v2_tdlat_3(X1)
    | v2_tdlat_3(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_22])).

cnf(c_1294,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_tdlat_3(X1)
    | v2_tdlat_3(X0)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_1293])).

cnf(c_5869,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | v2_tdlat_3(X1) != iProver_top
    | v2_tdlat_3(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1294])).

cnf(c_8848,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | v2_tdlat_3(sK1(sK2,sK3)) = iProver_top
    | v2_tdlat_3(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_8841,c_5869])).

cnf(c_34,negated_conjecture,
    ( v2_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_39,plain,
    ( v2_tdlat_3(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_9047,plain,
    ( v2_tdlat_3(sK1(sK2,sK3)) = iProver_top
    | v2_tex_2(sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8848,c_37,c_39,c_40])).

cnf(c_9048,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | v2_tdlat_3(sK1(sK2,sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_9047])).

cnf(c_10514,plain,
    ( v1_zfmisc_1(sK3) = iProver_top
    | k1_tarski(sK0(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10195,c_37,c_39,c_40,c_43,c_1048,c_8847,c_8848])).

cnf(c_10515,plain,
    ( k1_tarski(sK0(sK3)) = sK3
    | v1_zfmisc_1(sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_10514])).

cnf(c_10520,plain,
    ( k1_tarski(sK0(sK3)) = sK3
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_10515,c_10039])).

cnf(c_10523,plain,
    ( k1_tarski(sK0(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10197,c_41,c_10520])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_5895,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6384,plain,
    ( r1_tarski(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5882,c_5895])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_5900,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6863,plain,
    ( r1_tarski(X0,u1_struct_0(sK2)) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6384,c_5900])).

cnf(c_5,plain,
    ( ~ r1_tarski(k1_tarski(X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_280,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k1_tarski(X0),X1) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_281,plain,
    ( ~ r1_tarski(k1_tarski(X0),X1)
    | r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_280])).

cnf(c_8,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_221,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_1])).

cnf(c_222,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_221])).

cnf(c_720,plain,
    ( m1_subset_1(X0,X1)
    | ~ r1_tarski(k1_tarski(X0),X1) ),
    inference(resolution,[status(thm)],[c_281,c_222])).

cnf(c_5873,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r1_tarski(k1_tarski(X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_720])).

cnf(c_7046,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
    | r1_tarski(k1_tarski(X0),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6863,c_5873])).

cnf(c_7072,plain,
    ( m1_subset_1(sK0(sK3),u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5870,c_7046])).

cnf(c_7285,plain,
    ( m1_subset_1(sK0(sK3),u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7072,c_41])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_5893,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_7291,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK0(sK3)) = k1_tarski(sK0(sK3))
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7285,c_5893])).

cnf(c_732,plain,
    ( ~ r1_tarski(k1_tarski(X0),X1)
    | ~ v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_281,c_1])).

cnf(c_5872,plain,
    ( r1_tarski(k1_tarski(X0),X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_732])).

cnf(c_7047,plain,
    ( r1_tarski(k1_tarski(X0),sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6863,c_5872])).

cnf(c_7162,plain,
    ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5870,c_7047])).

cnf(c_8169,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK0(sK3)) = k1_tarski(sK0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7291,c_41,c_7162])).

cnf(c_10527,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK0(sK3)) = sK3 ),
    inference(demodulation,[status(thm)],[c_10523,c_8169])).

cnf(c_11224,plain,
    ( v2_tex_2(sK3,sK2) = iProver_top
    | m1_subset_1(sK0(sK3),u1_struct_0(sK2)) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_10527,c_5885])).

cnf(c_11225,plain,
    ( v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK0(sK3),u1_struct_0(sK2))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11224])).

cnf(c_9049,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | v2_tdlat_3(sK1(sK2,sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9048])).

cnf(c_8865,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | l1_pre_topc(sK1(sK2,sK3))
    | ~ l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8847])).

cnf(c_5887,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v1_tdlat_3(sK1(X1,X0)) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_7469,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | v1_tdlat_3(sK1(sK2,sK3)) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5882,c_5887])).

cnf(c_7660,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | v1_tdlat_3(sK1(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7469,c_37,c_38,c_40,c_41])).

cnf(c_7662,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | v1_tdlat_3(sK1(sK2,sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7660])).

cnf(c_7073,plain,
    ( m1_subset_1(sK0(sK3),u1_struct_0(sK2))
    | v1_xboole_0(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7072])).

cnf(c_5058,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_6350,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_5058])).

cnf(c_6543,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_6350])).

cnf(c_6890,plain,
    ( u1_struct_0(sK1(X0,sK3)) != sK3
    | sK3 = u1_struct_0(sK1(X0,sK3))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_6543])).

cnf(c_6891,plain,
    ( u1_struct_0(sK1(sK2,sK3)) != sK3
    | sK3 = u1_struct_0(sK1(sK2,sK3))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_6890])).

cnf(c_6779,plain,
    ( ~ v2_tdlat_3(sK1(X0,sK3))
    | ~ v1_tdlat_3(sK1(X0,sK3))
    | v1_zfmisc_1(u1_struct_0(sK1(X0,sK3)))
    | ~ l1_pre_topc(sK1(X0,sK3)) ),
    inference(instantiation,[status(thm)],[c_525])).

cnf(c_6781,plain,
    ( ~ v2_tdlat_3(sK1(sK2,sK3))
    | ~ v1_tdlat_3(sK1(sK2,sK3))
    | v1_zfmisc_1(u1_struct_0(sK1(sK2,sK3)))
    | ~ l1_pre_topc(sK1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_6779])).

cnf(c_6544,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_5057])).

cnf(c_29,negated_conjecture,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f99])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11494,c_11225,c_11224,c_9049,c_8865,c_7756,c_7662,c_7073,c_7072,c_6891,c_6781,c_6544,c_29,c_41,c_32,c_40,c_33,c_38,c_35,c_37,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:05:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.10/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.00  
% 3.10/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.10/1.00  
% 3.10/1.00  ------  iProver source info
% 3.10/1.00  
% 3.10/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.10/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.10/1.00  git: non_committed_changes: false
% 3.10/1.00  git: last_make_outside_of_git: false
% 3.10/1.00  
% 3.10/1.00  ------ 
% 3.10/1.00  
% 3.10/1.00  ------ Input Options
% 3.10/1.00  
% 3.10/1.00  --out_options                           all
% 3.10/1.00  --tptp_safe_out                         true
% 3.10/1.00  --problem_path                          ""
% 3.10/1.00  --include_path                          ""
% 3.10/1.00  --clausifier                            res/vclausify_rel
% 3.10/1.00  --clausifier_options                    --mode clausify
% 3.10/1.00  --stdin                                 false
% 3.10/1.00  --stats_out                             all
% 3.10/1.00  
% 3.10/1.00  ------ General Options
% 3.10/1.00  
% 3.10/1.00  --fof                                   false
% 3.10/1.00  --time_out_real                         305.
% 3.10/1.00  --time_out_virtual                      -1.
% 3.10/1.00  --symbol_type_check                     false
% 3.10/1.00  --clausify_out                          false
% 3.10/1.00  --sig_cnt_out                           false
% 3.10/1.00  --trig_cnt_out                          false
% 3.10/1.00  --trig_cnt_out_tolerance                1.
% 3.10/1.00  --trig_cnt_out_sk_spl                   false
% 3.10/1.00  --abstr_cl_out                          false
% 3.10/1.00  
% 3.10/1.00  ------ Global Options
% 3.10/1.00  
% 3.10/1.00  --schedule                              default
% 3.10/1.00  --add_important_lit                     false
% 3.10/1.00  --prop_solver_per_cl                    1000
% 3.10/1.00  --min_unsat_core                        false
% 3.10/1.00  --soft_assumptions                      false
% 3.10/1.00  --soft_lemma_size                       3
% 3.10/1.00  --prop_impl_unit_size                   0
% 3.10/1.00  --prop_impl_unit                        []
% 3.10/1.00  --share_sel_clauses                     true
% 3.10/1.00  --reset_solvers                         false
% 3.10/1.00  --bc_imp_inh                            [conj_cone]
% 3.10/1.00  --conj_cone_tolerance                   3.
% 3.10/1.00  --extra_neg_conj                        none
% 3.10/1.00  --large_theory_mode                     true
% 3.10/1.00  --prolific_symb_bound                   200
% 3.10/1.00  --lt_threshold                          2000
% 3.10/1.00  --clause_weak_htbl                      true
% 3.10/1.00  --gc_record_bc_elim                     false
% 3.10/1.00  
% 3.10/1.00  ------ Preprocessing Options
% 3.10/1.00  
% 3.10/1.00  --preprocessing_flag                    true
% 3.10/1.00  --time_out_prep_mult                    0.1
% 3.10/1.00  --splitting_mode                        input
% 3.10/1.00  --splitting_grd                         true
% 3.10/1.00  --splitting_cvd                         false
% 3.10/1.00  --splitting_cvd_svl                     false
% 3.10/1.00  --splitting_nvd                         32
% 3.10/1.00  --sub_typing                            true
% 3.10/1.00  --prep_gs_sim                           true
% 3.10/1.00  --prep_unflatten                        true
% 3.10/1.00  --prep_res_sim                          true
% 3.10/1.00  --prep_upred                            true
% 3.10/1.00  --prep_sem_filter                       exhaustive
% 3.10/1.00  --prep_sem_filter_out                   false
% 3.10/1.00  --pred_elim                             true
% 3.10/1.00  --res_sim_input                         true
% 3.10/1.00  --eq_ax_congr_red                       true
% 3.10/1.00  --pure_diseq_elim                       true
% 3.10/1.00  --brand_transform                       false
% 3.10/1.00  --non_eq_to_eq                          false
% 3.10/1.00  --prep_def_merge                        true
% 3.10/1.00  --prep_def_merge_prop_impl              false
% 3.10/1.00  --prep_def_merge_mbd                    true
% 3.10/1.00  --prep_def_merge_tr_red                 false
% 3.10/1.00  --prep_def_merge_tr_cl                  false
% 3.10/1.00  --smt_preprocessing                     true
% 3.10/1.00  --smt_ac_axioms                         fast
% 3.10/1.00  --preprocessed_out                      false
% 3.10/1.00  --preprocessed_stats                    false
% 3.10/1.00  
% 3.10/1.00  ------ Abstraction refinement Options
% 3.10/1.00  
% 3.10/1.00  --abstr_ref                             []
% 3.10/1.00  --abstr_ref_prep                        false
% 3.10/1.00  --abstr_ref_until_sat                   false
% 3.10/1.00  --abstr_ref_sig_restrict                funpre
% 3.10/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.10/1.00  --abstr_ref_under                       []
% 3.10/1.00  
% 3.10/1.00  ------ SAT Options
% 3.10/1.00  
% 3.10/1.00  --sat_mode                              false
% 3.10/1.00  --sat_fm_restart_options                ""
% 3.10/1.00  --sat_gr_def                            false
% 3.10/1.00  --sat_epr_types                         true
% 3.10/1.00  --sat_non_cyclic_types                  false
% 3.10/1.00  --sat_finite_models                     false
% 3.10/1.00  --sat_fm_lemmas                         false
% 3.10/1.00  --sat_fm_prep                           false
% 3.10/1.00  --sat_fm_uc_incr                        true
% 3.10/1.00  --sat_out_model                         small
% 3.10/1.00  --sat_out_clauses                       false
% 3.10/1.00  
% 3.10/1.00  ------ QBF Options
% 3.10/1.00  
% 3.10/1.00  --qbf_mode                              false
% 3.10/1.00  --qbf_elim_univ                         false
% 3.10/1.00  --qbf_dom_inst                          none
% 3.10/1.00  --qbf_dom_pre_inst                      false
% 3.10/1.00  --qbf_sk_in                             false
% 3.10/1.00  --qbf_pred_elim                         true
% 3.10/1.00  --qbf_split                             512
% 3.10/1.00  
% 3.10/1.00  ------ BMC1 Options
% 3.10/1.00  
% 3.10/1.00  --bmc1_incremental                      false
% 3.10/1.00  --bmc1_axioms                           reachable_all
% 3.10/1.00  --bmc1_min_bound                        0
% 3.10/1.00  --bmc1_max_bound                        -1
% 3.10/1.00  --bmc1_max_bound_default                -1
% 3.10/1.00  --bmc1_symbol_reachability              true
% 3.10/1.00  --bmc1_property_lemmas                  false
% 3.10/1.00  --bmc1_k_induction                      false
% 3.10/1.00  --bmc1_non_equiv_states                 false
% 3.10/1.00  --bmc1_deadlock                         false
% 3.10/1.00  --bmc1_ucm                              false
% 3.10/1.00  --bmc1_add_unsat_core                   none
% 3.10/1.00  --bmc1_unsat_core_children              false
% 3.10/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.10/1.00  --bmc1_out_stat                         full
% 3.10/1.00  --bmc1_ground_init                      false
% 3.10/1.00  --bmc1_pre_inst_next_state              false
% 3.10/1.00  --bmc1_pre_inst_state                   false
% 3.10/1.00  --bmc1_pre_inst_reach_state             false
% 3.10/1.00  --bmc1_out_unsat_core                   false
% 3.10/1.00  --bmc1_aig_witness_out                  false
% 3.10/1.00  --bmc1_verbose                          false
% 3.10/1.00  --bmc1_dump_clauses_tptp                false
% 3.10/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.10/1.00  --bmc1_dump_file                        -
% 3.10/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.10/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.10/1.00  --bmc1_ucm_extend_mode                  1
% 3.10/1.00  --bmc1_ucm_init_mode                    2
% 3.10/1.00  --bmc1_ucm_cone_mode                    none
% 3.10/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.10/1.00  --bmc1_ucm_relax_model                  4
% 3.10/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.10/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.10/1.00  --bmc1_ucm_layered_model                none
% 3.10/1.00  --bmc1_ucm_max_lemma_size               10
% 3.10/1.00  
% 3.10/1.00  ------ AIG Options
% 3.10/1.00  
% 3.10/1.00  --aig_mode                              false
% 3.10/1.00  
% 3.10/1.00  ------ Instantiation Options
% 3.10/1.00  
% 3.10/1.00  --instantiation_flag                    true
% 3.10/1.00  --inst_sos_flag                         false
% 3.10/1.00  --inst_sos_phase                        true
% 3.10/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.10/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.10/1.00  --inst_lit_sel_side                     num_symb
% 3.10/1.00  --inst_solver_per_active                1400
% 3.10/1.00  --inst_solver_calls_frac                1.
% 3.10/1.00  --inst_passive_queue_type               priority_queues
% 3.10/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.10/1.00  --inst_passive_queues_freq              [25;2]
% 3.10/1.00  --inst_dismatching                      true
% 3.10/1.00  --inst_eager_unprocessed_to_passive     true
% 3.10/1.00  --inst_prop_sim_given                   true
% 3.10/1.00  --inst_prop_sim_new                     false
% 3.10/1.00  --inst_subs_new                         false
% 3.10/1.00  --inst_eq_res_simp                      false
% 3.10/1.00  --inst_subs_given                       false
% 3.10/1.00  --inst_orphan_elimination               true
% 3.10/1.00  --inst_learning_loop_flag               true
% 3.10/1.00  --inst_learning_start                   3000
% 3.10/1.00  --inst_learning_factor                  2
% 3.10/1.00  --inst_start_prop_sim_after_learn       3
% 3.10/1.00  --inst_sel_renew                        solver
% 3.10/1.00  --inst_lit_activity_flag                true
% 3.10/1.00  --inst_restr_to_given                   false
% 3.10/1.00  --inst_activity_threshold               500
% 3.10/1.00  --inst_out_proof                        true
% 3.10/1.00  
% 3.10/1.00  ------ Resolution Options
% 3.10/1.00  
% 3.10/1.00  --resolution_flag                       true
% 3.10/1.00  --res_lit_sel                           adaptive
% 3.10/1.00  --res_lit_sel_side                      none
% 3.10/1.00  --res_ordering                          kbo
% 3.10/1.00  --res_to_prop_solver                    active
% 3.10/1.00  --res_prop_simpl_new                    false
% 3.10/1.00  --res_prop_simpl_given                  true
% 3.10/1.00  --res_passive_queue_type                priority_queues
% 3.10/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.10/1.00  --res_passive_queues_freq               [15;5]
% 3.10/1.00  --res_forward_subs                      full
% 3.10/1.00  --res_backward_subs                     full
% 3.10/1.00  --res_forward_subs_resolution           true
% 3.10/1.00  --res_backward_subs_resolution          true
% 3.10/1.00  --res_orphan_elimination                true
% 3.10/1.00  --res_time_limit                        2.
% 3.10/1.00  --res_out_proof                         true
% 3.10/1.00  
% 3.10/1.00  ------ Superposition Options
% 3.10/1.00  
% 3.10/1.00  --superposition_flag                    true
% 3.10/1.00  --sup_passive_queue_type                priority_queues
% 3.10/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.10/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.10/1.00  --demod_completeness_check              fast
% 3.10/1.00  --demod_use_ground                      true
% 3.10/1.00  --sup_to_prop_solver                    passive
% 3.10/1.00  --sup_prop_simpl_new                    true
% 3.10/1.00  --sup_prop_simpl_given                  true
% 3.10/1.00  --sup_fun_splitting                     false
% 3.10/1.00  --sup_smt_interval                      50000
% 3.10/1.00  
% 3.10/1.00  ------ Superposition Simplification Setup
% 3.10/1.00  
% 3.10/1.00  --sup_indices_passive                   []
% 3.10/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.10/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/1.00  --sup_full_bw                           [BwDemod]
% 3.10/1.00  --sup_immed_triv                        [TrivRules]
% 3.10/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.10/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/1.00  --sup_immed_bw_main                     []
% 3.10/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.10/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/1.00  
% 3.10/1.00  ------ Combination Options
% 3.10/1.00  
% 3.10/1.00  --comb_res_mult                         3
% 3.10/1.00  --comb_sup_mult                         2
% 3.10/1.00  --comb_inst_mult                        10
% 3.10/1.00  
% 3.10/1.00  ------ Debug Options
% 3.10/1.00  
% 3.10/1.00  --dbg_backtrace                         false
% 3.10/1.00  --dbg_dump_prop_clauses                 false
% 3.10/1.00  --dbg_dump_prop_clauses_file            -
% 3.10/1.00  --dbg_out_stat                          false
% 3.10/1.00  ------ Parsing...
% 3.10/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.10/1.00  
% 3.10/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.10/1.00  
% 3.10/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.10/1.00  
% 3.10/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.10/1.00  ------ Proving...
% 3.10/1.00  ------ Problem Properties 
% 3.10/1.00  
% 3.10/1.00  
% 3.10/1.00  clauses                                 32
% 3.10/1.00  conjectures                             8
% 3.10/1.00  EPR                                     15
% 3.10/1.00  Horn                                    20
% 3.10/1.00  unary                                   7
% 3.10/1.00  binary                                  8
% 3.10/1.00  lits                                    97
% 3.10/1.00  lits eq                                 3
% 3.10/1.00  fd_pure                                 0
% 3.10/1.00  fd_pseudo                               0
% 3.10/1.00  fd_cond                                 0
% 3.10/1.00  fd_pseudo_cond                          1
% 3.10/1.00  AC symbols                              0
% 3.10/1.00  
% 3.10/1.00  ------ Schedule dynamic 5 is on 
% 3.10/1.00  
% 3.10/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.10/1.00  
% 3.10/1.00  
% 3.10/1.00  ------ 
% 3.10/1.00  Current options:
% 3.10/1.00  ------ 
% 3.10/1.00  
% 3.10/1.00  ------ Input Options
% 3.10/1.00  
% 3.10/1.00  --out_options                           all
% 3.10/1.00  --tptp_safe_out                         true
% 3.10/1.00  --problem_path                          ""
% 3.10/1.00  --include_path                          ""
% 3.10/1.00  --clausifier                            res/vclausify_rel
% 3.10/1.00  --clausifier_options                    --mode clausify
% 3.10/1.00  --stdin                                 false
% 3.10/1.00  --stats_out                             all
% 3.10/1.00  
% 3.10/1.00  ------ General Options
% 3.10/1.00  
% 3.10/1.00  --fof                                   false
% 3.10/1.00  --time_out_real                         305.
% 3.10/1.00  --time_out_virtual                      -1.
% 3.10/1.00  --symbol_type_check                     false
% 3.10/1.00  --clausify_out                          false
% 3.10/1.00  --sig_cnt_out                           false
% 3.10/1.00  --trig_cnt_out                          false
% 3.10/1.00  --trig_cnt_out_tolerance                1.
% 3.10/1.00  --trig_cnt_out_sk_spl                   false
% 3.10/1.00  --abstr_cl_out                          false
% 3.10/1.00  
% 3.10/1.00  ------ Global Options
% 3.10/1.00  
% 3.10/1.00  --schedule                              default
% 3.10/1.00  --add_important_lit                     false
% 3.10/1.00  --prop_solver_per_cl                    1000
% 3.10/1.00  --min_unsat_core                        false
% 3.10/1.00  --soft_assumptions                      false
% 3.10/1.00  --soft_lemma_size                       3
% 3.10/1.00  --prop_impl_unit_size                   0
% 3.10/1.00  --prop_impl_unit                        []
% 3.10/1.00  --share_sel_clauses                     true
% 3.10/1.00  --reset_solvers                         false
% 3.10/1.00  --bc_imp_inh                            [conj_cone]
% 3.10/1.00  --conj_cone_tolerance                   3.
% 3.10/1.00  --extra_neg_conj                        none
% 3.10/1.00  --large_theory_mode                     true
% 3.10/1.00  --prolific_symb_bound                   200
% 3.10/1.00  --lt_threshold                          2000
% 3.10/1.00  --clause_weak_htbl                      true
% 3.10/1.00  --gc_record_bc_elim                     false
% 3.10/1.00  
% 3.10/1.00  ------ Preprocessing Options
% 3.10/1.00  
% 3.10/1.00  --preprocessing_flag                    true
% 3.10/1.00  --time_out_prep_mult                    0.1
% 3.10/1.00  --splitting_mode                        input
% 3.10/1.00  --splitting_grd                         true
% 3.10/1.00  --splitting_cvd                         false
% 3.10/1.00  --splitting_cvd_svl                     false
% 3.10/1.00  --splitting_nvd                         32
% 3.10/1.00  --sub_typing                            true
% 3.10/1.00  --prep_gs_sim                           true
% 3.10/1.00  --prep_unflatten                        true
% 3.10/1.00  --prep_res_sim                          true
% 3.10/1.00  --prep_upred                            true
% 3.10/1.00  --prep_sem_filter                       exhaustive
% 3.10/1.00  --prep_sem_filter_out                   false
% 3.10/1.00  --pred_elim                             true
% 3.10/1.00  --res_sim_input                         true
% 3.10/1.00  --eq_ax_congr_red                       true
% 3.10/1.00  --pure_diseq_elim                       true
% 3.10/1.00  --brand_transform                       false
% 3.10/1.00  --non_eq_to_eq                          false
% 3.10/1.00  --prep_def_merge                        true
% 3.10/1.00  --prep_def_merge_prop_impl              false
% 3.10/1.00  --prep_def_merge_mbd                    true
% 3.10/1.00  --prep_def_merge_tr_red                 false
% 3.10/1.00  --prep_def_merge_tr_cl                  false
% 3.10/1.00  --smt_preprocessing                     true
% 3.10/1.00  --smt_ac_axioms                         fast
% 3.10/1.00  --preprocessed_out                      false
% 3.10/1.00  --preprocessed_stats                    false
% 3.10/1.00  
% 3.10/1.00  ------ Abstraction refinement Options
% 3.10/1.00  
% 3.10/1.00  --abstr_ref                             []
% 3.10/1.00  --abstr_ref_prep                        false
% 3.10/1.00  --abstr_ref_until_sat                   false
% 3.10/1.00  --abstr_ref_sig_restrict                funpre
% 3.10/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.10/1.00  --abstr_ref_under                       []
% 3.10/1.00  
% 3.10/1.00  ------ SAT Options
% 3.10/1.00  
% 3.10/1.00  --sat_mode                              false
% 3.10/1.00  --sat_fm_restart_options                ""
% 3.10/1.00  --sat_gr_def                            false
% 3.10/1.00  --sat_epr_types                         true
% 3.10/1.00  --sat_non_cyclic_types                  false
% 3.10/1.00  --sat_finite_models                     false
% 3.10/1.00  --sat_fm_lemmas                         false
% 3.10/1.00  --sat_fm_prep                           false
% 3.10/1.00  --sat_fm_uc_incr                        true
% 3.10/1.00  --sat_out_model                         small
% 3.10/1.00  --sat_out_clauses                       false
% 3.10/1.00  
% 3.10/1.00  ------ QBF Options
% 3.10/1.00  
% 3.10/1.00  --qbf_mode                              false
% 3.10/1.00  --qbf_elim_univ                         false
% 3.10/1.00  --qbf_dom_inst                          none
% 3.10/1.00  --qbf_dom_pre_inst                      false
% 3.10/1.00  --qbf_sk_in                             false
% 3.10/1.00  --qbf_pred_elim                         true
% 3.10/1.00  --qbf_split                             512
% 3.10/1.00  
% 3.10/1.00  ------ BMC1 Options
% 3.10/1.00  
% 3.10/1.00  --bmc1_incremental                      false
% 3.10/1.00  --bmc1_axioms                           reachable_all
% 3.10/1.00  --bmc1_min_bound                        0
% 3.10/1.00  --bmc1_max_bound                        -1
% 3.10/1.00  --bmc1_max_bound_default                -1
% 3.10/1.00  --bmc1_symbol_reachability              true
% 3.10/1.00  --bmc1_property_lemmas                  false
% 3.10/1.00  --bmc1_k_induction                      false
% 3.10/1.00  --bmc1_non_equiv_states                 false
% 3.10/1.00  --bmc1_deadlock                         false
% 3.10/1.00  --bmc1_ucm                              false
% 3.10/1.00  --bmc1_add_unsat_core                   none
% 3.10/1.00  --bmc1_unsat_core_children              false
% 3.10/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.10/1.00  --bmc1_out_stat                         full
% 3.10/1.00  --bmc1_ground_init                      false
% 3.10/1.00  --bmc1_pre_inst_next_state              false
% 3.10/1.00  --bmc1_pre_inst_state                   false
% 3.10/1.00  --bmc1_pre_inst_reach_state             false
% 3.10/1.00  --bmc1_out_unsat_core                   false
% 3.10/1.00  --bmc1_aig_witness_out                  false
% 3.10/1.00  --bmc1_verbose                          false
% 3.10/1.00  --bmc1_dump_clauses_tptp                false
% 3.10/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.10/1.00  --bmc1_dump_file                        -
% 3.10/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.10/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.10/1.00  --bmc1_ucm_extend_mode                  1
% 3.10/1.00  --bmc1_ucm_init_mode                    2
% 3.10/1.00  --bmc1_ucm_cone_mode                    none
% 3.10/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.10/1.00  --bmc1_ucm_relax_model                  4
% 3.10/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.10/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.10/1.00  --bmc1_ucm_layered_model                none
% 3.10/1.00  --bmc1_ucm_max_lemma_size               10
% 3.10/1.00  
% 3.10/1.00  ------ AIG Options
% 3.10/1.00  
% 3.10/1.00  --aig_mode                              false
% 3.10/1.00  
% 3.10/1.00  ------ Instantiation Options
% 3.10/1.00  
% 3.10/1.00  --instantiation_flag                    true
% 3.10/1.00  --inst_sos_flag                         false
% 3.10/1.00  --inst_sos_phase                        true
% 3.10/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.10/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.10/1.00  --inst_lit_sel_side                     none
% 3.10/1.00  --inst_solver_per_active                1400
% 3.10/1.00  --inst_solver_calls_frac                1.
% 3.10/1.00  --inst_passive_queue_type               priority_queues
% 3.10/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.10/1.00  --inst_passive_queues_freq              [25;2]
% 3.10/1.00  --inst_dismatching                      true
% 3.10/1.00  --inst_eager_unprocessed_to_passive     true
% 3.10/1.00  --inst_prop_sim_given                   true
% 3.10/1.00  --inst_prop_sim_new                     false
% 3.10/1.00  --inst_subs_new                         false
% 3.10/1.00  --inst_eq_res_simp                      false
% 3.10/1.00  --inst_subs_given                       false
% 3.10/1.00  --inst_orphan_elimination               true
% 3.10/1.00  --inst_learning_loop_flag               true
% 3.10/1.00  --inst_learning_start                   3000
% 3.10/1.00  --inst_learning_factor                  2
% 3.10/1.00  --inst_start_prop_sim_after_learn       3
% 3.10/1.00  --inst_sel_renew                        solver
% 3.10/1.00  --inst_lit_activity_flag                true
% 3.10/1.00  --inst_restr_to_given                   false
% 3.10/1.00  --inst_activity_threshold               500
% 3.10/1.00  --inst_out_proof                        true
% 3.10/1.00  
% 3.10/1.00  ------ Resolution Options
% 3.10/1.00  
% 3.10/1.00  --resolution_flag                       false
% 3.10/1.00  --res_lit_sel                           adaptive
% 3.10/1.00  --res_lit_sel_side                      none
% 3.10/1.00  --res_ordering                          kbo
% 3.10/1.00  --res_to_prop_solver                    active
% 3.10/1.00  --res_prop_simpl_new                    false
% 3.10/1.00  --res_prop_simpl_given                  true
% 3.10/1.00  --res_passive_queue_type                priority_queues
% 3.10/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.10/1.00  --res_passive_queues_freq               [15;5]
% 3.10/1.00  --res_forward_subs                      full
% 3.10/1.00  --res_backward_subs                     full
% 3.10/1.00  --res_forward_subs_resolution           true
% 3.10/1.00  --res_backward_subs_resolution          true
% 3.10/1.00  --res_orphan_elimination                true
% 3.10/1.00  --res_time_limit                        2.
% 3.10/1.00  --res_out_proof                         true
% 3.10/1.00  
% 3.10/1.00  ------ Superposition Options
% 3.10/1.00  
% 3.10/1.00  --superposition_flag                    true
% 3.10/1.00  --sup_passive_queue_type                priority_queues
% 3.10/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.10/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.10/1.00  --demod_completeness_check              fast
% 3.10/1.00  --demod_use_ground                      true
% 3.10/1.00  --sup_to_prop_solver                    passive
% 3.10/1.00  --sup_prop_simpl_new                    true
% 3.10/1.00  --sup_prop_simpl_given                  true
% 3.10/1.00  --sup_fun_splitting                     false
% 3.10/1.00  --sup_smt_interval                      50000
% 3.10/1.00  
% 3.10/1.00  ------ Superposition Simplification Setup
% 3.10/1.00  
% 3.10/1.00  --sup_indices_passive                   []
% 3.10/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.10/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/1.00  --sup_full_bw                           [BwDemod]
% 3.10/1.00  --sup_immed_triv                        [TrivRules]
% 3.10/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.10/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/1.00  --sup_immed_bw_main                     []
% 3.10/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.10/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/1.00  
% 3.10/1.00  ------ Combination Options
% 3.10/1.00  
% 3.10/1.00  --comb_res_mult                         3
% 3.10/1.00  --comb_sup_mult                         2
% 3.10/1.00  --comb_inst_mult                        10
% 3.10/1.00  
% 3.10/1.00  ------ Debug Options
% 3.10/1.00  
% 3.10/1.00  --dbg_backtrace                         false
% 3.10/1.00  --dbg_dump_prop_clauses                 false
% 3.10/1.00  --dbg_dump_prop_clauses_file            -
% 3.10/1.00  --dbg_out_stat                          false
% 3.10/1.00  
% 3.10/1.00  
% 3.10/1.00  
% 3.10/1.00  
% 3.10/1.00  ------ Proving...
% 3.10/1.00  
% 3.10/1.00  
% 3.10/1.00  % SZS status Theorem for theBenchmark.p
% 3.10/1.00  
% 3.10/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.10/1.00  
% 3.10/1.00  fof(f19,conjecture,(
% 3.10/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 3.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f20,negated_conjecture,(
% 3.10/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 3.10/1.00    inference(negated_conjecture,[],[f19])).
% 3.10/1.00  
% 3.10/1.00  fof(f47,plain,(
% 3.10/1.00    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.10/1.00    inference(ennf_transformation,[],[f20])).
% 3.10/1.00  
% 3.10/1.00  fof(f48,plain,(
% 3.10/1.00    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.10/1.00    inference(flattening,[],[f47])).
% 3.10/1.00  
% 3.10/1.00  fof(f58,plain,(
% 3.10/1.00    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.10/1.00    inference(nnf_transformation,[],[f48])).
% 3.10/1.00  
% 3.10/1.00  fof(f59,plain,(
% 3.10/1.00    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.10/1.00    inference(flattening,[],[f58])).
% 3.10/1.00  
% 3.10/1.00  fof(f61,plain,(
% 3.10/1.00    ( ! [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK3) | ~v2_tex_2(sK3,X0)) & (v1_zfmisc_1(sK3) | v2_tex_2(sK3,X0)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK3))) )),
% 3.10/1.00    introduced(choice_axiom,[])).
% 3.10/1.00  
% 3.10/1.00  fof(f60,plain,(
% 3.10/1.00    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK2)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK2) & v2_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.10/1.00    introduced(choice_axiom,[])).
% 3.10/1.00  
% 3.10/1.00  fof(f62,plain,(
% 3.10/1.00    ((~v1_zfmisc_1(sK3) | ~v2_tex_2(sK3,sK2)) & (v1_zfmisc_1(sK3) | v2_tex_2(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(sK3)) & l1_pre_topc(sK2) & v2_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.10/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f59,f61,f60])).
% 3.10/1.00  
% 3.10/1.00  fof(f98,plain,(
% 3.10/1.00    v1_zfmisc_1(sK3) | v2_tex_2(sK3,sK2)),
% 3.10/1.00    inference(cnf_transformation,[],[f62])).
% 3.10/1.00  
% 3.10/1.00  fof(f97,plain,(
% 3.10/1.00    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 3.10/1.00    inference(cnf_transformation,[],[f62])).
% 3.10/1.00  
% 3.10/1.00  fof(f17,axiom,(
% 3.10/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 3.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f21,plain,(
% 3.10/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 3.10/1.00    inference(pure_predicate_removal,[],[f17])).
% 3.10/1.00  
% 3.10/1.00  fof(f43,plain,(
% 3.10/1.00    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.10/1.00    inference(ennf_transformation,[],[f21])).
% 3.10/1.00  
% 3.10/1.00  fof(f44,plain,(
% 3.10/1.00    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.10/1.00    inference(flattening,[],[f43])).
% 3.10/1.00  
% 3.10/1.00  fof(f56,plain,(
% 3.10/1.00    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK1(X0,X1)) = X1 & m1_pre_topc(sK1(X0,X1),X0) & v1_tdlat_3(sK1(X0,X1)) & ~v2_struct_0(sK1(X0,X1))))),
% 3.10/1.00    introduced(choice_axiom,[])).
% 3.10/1.00  
% 3.10/1.00  fof(f57,plain,(
% 3.10/1.00    ! [X0] : (! [X1] : ((u1_struct_0(sK1(X0,X1)) = X1 & m1_pre_topc(sK1(X0,X1),X0) & v1_tdlat_3(sK1(X0,X1)) & ~v2_struct_0(sK1(X0,X1))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.10/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f44,f56])).
% 3.10/1.00  
% 3.10/1.00  fof(f90,plain,(
% 3.10/1.00    ( ! [X0,X1] : (u1_struct_0(sK1(X0,X1)) = X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f57])).
% 3.10/1.00  
% 3.10/1.00  fof(f92,plain,(
% 3.10/1.00    ~v2_struct_0(sK2)),
% 3.10/1.00    inference(cnf_transformation,[],[f62])).
% 3.10/1.00  
% 3.10/1.00  fof(f93,plain,(
% 3.10/1.00    v2_pre_topc(sK2)),
% 3.10/1.00    inference(cnf_transformation,[],[f62])).
% 3.10/1.00  
% 3.10/1.00  fof(f95,plain,(
% 3.10/1.00    l1_pre_topc(sK2)),
% 3.10/1.00    inference(cnf_transformation,[],[f62])).
% 3.10/1.00  
% 3.10/1.00  fof(f96,plain,(
% 3.10/1.00    ~v1_xboole_0(sK3)),
% 3.10/1.00    inference(cnf_transformation,[],[f62])).
% 3.10/1.00  
% 3.10/1.00  fof(f1,axiom,(
% 3.10/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f49,plain,(
% 3.10/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.10/1.00    inference(nnf_transformation,[],[f1])).
% 3.10/1.00  
% 3.10/1.00  fof(f50,plain,(
% 3.10/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.10/1.00    inference(rectify,[],[f49])).
% 3.10/1.00  
% 3.10/1.00  fof(f51,plain,(
% 3.10/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.10/1.00    introduced(choice_axiom,[])).
% 3.10/1.00  
% 3.10/1.00  fof(f52,plain,(
% 3.10/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.10/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f50,f51])).
% 3.10/1.00  
% 3.10/1.00  fof(f64,plain,(
% 3.10/1.00    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f52])).
% 3.10/1.00  
% 3.10/1.00  fof(f4,axiom,(
% 3.10/1.00    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f53,plain,(
% 3.10/1.00    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 3.10/1.00    inference(nnf_transformation,[],[f4])).
% 3.10/1.00  
% 3.10/1.00  fof(f68,plain,(
% 3.10/1.00    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f53])).
% 3.10/1.00  
% 3.10/1.00  fof(f16,axiom,(
% 3.10/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 3.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f41,plain,(
% 3.10/1.00    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 3.10/1.00    inference(ennf_transformation,[],[f16])).
% 3.10/1.00  
% 3.10/1.00  fof(f42,plain,(
% 3.10/1.00    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.10/1.00    inference(flattening,[],[f41])).
% 3.10/1.00  
% 3.10/1.00  fof(f86,plain,(
% 3.10/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f42])).
% 3.10/1.00  
% 3.10/1.00  fof(f3,axiom,(
% 3.10/1.00    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 3.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f66,plain,(
% 3.10/1.00    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 3.10/1.00    inference(cnf_transformation,[],[f3])).
% 3.10/1.00  
% 3.10/1.00  fof(f18,axiom,(
% 3.10/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 3.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f45,plain,(
% 3.10/1.00    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.10/1.00    inference(ennf_transformation,[],[f18])).
% 3.10/1.00  
% 3.10/1.00  fof(f46,plain,(
% 3.10/1.00    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.10/1.00    inference(flattening,[],[f45])).
% 3.10/1.00  
% 3.10/1.00  fof(f91,plain,(
% 3.10/1.00    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f46])).
% 3.10/1.00  
% 3.10/1.00  fof(f14,axiom,(
% 3.10/1.00    ! [X0] : (l1_pre_topc(X0) => ((v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0))))),
% 3.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f37,plain,(
% 3.10/1.00    ! [X0] : (((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | (~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.10/1.00    inference(ennf_transformation,[],[f14])).
% 3.10/1.00  
% 3.10/1.00  fof(f38,plain,(
% 3.10/1.00    ! [X0] : ((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.10/1.00    inference(flattening,[],[f37])).
% 3.10/1.00  
% 3.10/1.00  fof(f83,plain,(
% 3.10/1.00    ( ! [X0] : (v7_struct_0(X0) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f38])).
% 3.10/1.00  
% 3.10/1.00  fof(f13,axiom,(
% 3.10/1.00    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 3.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f35,plain,(
% 3.10/1.00    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 3.10/1.00    inference(ennf_transformation,[],[f13])).
% 3.10/1.00  
% 3.10/1.00  fof(f36,plain,(
% 3.10/1.00    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 3.10/1.00    inference(flattening,[],[f35])).
% 3.10/1.00  
% 3.10/1.00  fof(f81,plain,(
% 3.10/1.00    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f36])).
% 3.10/1.00  
% 3.10/1.00  fof(f8,axiom,(
% 3.10/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f27,plain,(
% 3.10/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.10/1.00    inference(ennf_transformation,[],[f8])).
% 3.10/1.00  
% 3.10/1.00  fof(f76,plain,(
% 3.10/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f27])).
% 3.10/1.00  
% 3.10/1.00  fof(f7,axiom,(
% 3.10/1.00    ! [X0] : (l1_struct_0(X0) => (v2_struct_0(X0) => v7_struct_0(X0)))),
% 3.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f25,plain,(
% 3.10/1.00    ! [X0] : ((v7_struct_0(X0) | ~v2_struct_0(X0)) | ~l1_struct_0(X0))),
% 3.10/1.00    inference(ennf_transformation,[],[f7])).
% 3.10/1.00  
% 3.10/1.00  fof(f26,plain,(
% 3.10/1.00    ! [X0] : (v7_struct_0(X0) | ~v2_struct_0(X0) | ~l1_struct_0(X0))),
% 3.10/1.00    inference(flattening,[],[f25])).
% 3.10/1.00  
% 3.10/1.00  fof(f75,plain,(
% 3.10/1.00    ( ! [X0] : (v7_struct_0(X0) | ~v2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f26])).
% 3.10/1.00  
% 3.10/1.00  fof(f10,axiom,(
% 3.10/1.00    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 3.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f29,plain,(
% 3.10/1.00    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 3.10/1.00    inference(ennf_transformation,[],[f10])).
% 3.10/1.00  
% 3.10/1.00  fof(f30,plain,(
% 3.10/1.00    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 3.10/1.00    inference(flattening,[],[f29])).
% 3.10/1.00  
% 3.10/1.00  fof(f78,plain,(
% 3.10/1.00    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f30])).
% 3.10/1.00  
% 3.10/1.00  fof(f88,plain,(
% 3.10/1.00    ( ! [X0,X1] : (v1_tdlat_3(sK1(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f57])).
% 3.10/1.00  
% 3.10/1.00  fof(f89,plain,(
% 3.10/1.00    ( ! [X0,X1] : (m1_pre_topc(sK1(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f57])).
% 3.10/1.00  
% 3.10/1.00  fof(f9,axiom,(
% 3.10/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f28,plain,(
% 3.10/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.10/1.00    inference(ennf_transformation,[],[f9])).
% 3.10/1.00  
% 3.10/1.00  fof(f77,plain,(
% 3.10/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f28])).
% 3.10/1.00  
% 3.10/1.00  fof(f15,axiom,(
% 3.10/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_tdlat_3(X1)))),
% 3.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f39,plain,(
% 3.10/1.00    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.10/1.00    inference(ennf_transformation,[],[f15])).
% 3.10/1.00  
% 3.10/1.00  fof(f40,plain,(
% 3.10/1.00    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.10/1.00    inference(flattening,[],[f39])).
% 3.10/1.00  
% 3.10/1.00  fof(f85,plain,(
% 3.10/1.00    ( ! [X0,X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f40])).
% 3.10/1.00  
% 3.10/1.00  fof(f94,plain,(
% 3.10/1.00    v2_tdlat_3(sK2)),
% 3.10/1.00    inference(cnf_transformation,[],[f62])).
% 3.10/1.00  
% 3.10/1.00  fof(f6,axiom,(
% 3.10/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f55,plain,(
% 3.10/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.10/1.00    inference(nnf_transformation,[],[f6])).
% 3.10/1.00  
% 3.10/1.00  fof(f73,plain,(
% 3.10/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.10/1.00    inference(cnf_transformation,[],[f55])).
% 3.10/1.00  
% 3.10/1.00  fof(f2,axiom,(
% 3.10/1.00    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f22,plain,(
% 3.10/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.10/1.00    inference(ennf_transformation,[],[f2])).
% 3.10/1.00  
% 3.10/1.00  fof(f23,plain,(
% 3.10/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.10/1.00    inference(flattening,[],[f22])).
% 3.10/1.00  
% 3.10/1.00  fof(f65,plain,(
% 3.10/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f23])).
% 3.10/1.00  
% 3.10/1.00  fof(f67,plain,(
% 3.10/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f53])).
% 3.10/1.00  
% 3.10/1.00  fof(f5,axiom,(
% 3.10/1.00    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f24,plain,(
% 3.10/1.00    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.10/1.00    inference(ennf_transformation,[],[f5])).
% 3.10/1.00  
% 3.10/1.00  fof(f54,plain,(
% 3.10/1.00    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.10/1.00    inference(nnf_transformation,[],[f24])).
% 3.10/1.00  
% 3.10/1.00  fof(f70,plain,(
% 3.10/1.00    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f54])).
% 3.10/1.00  
% 3.10/1.00  fof(f63,plain,(
% 3.10/1.00    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f52])).
% 3.10/1.00  
% 3.10/1.00  fof(f11,axiom,(
% 3.10/1.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 3.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f31,plain,(
% 3.10/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.10/1.00    inference(ennf_transformation,[],[f11])).
% 3.10/1.00  
% 3.10/1.00  fof(f32,plain,(
% 3.10/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.10/1.00    inference(flattening,[],[f31])).
% 3.10/1.00  
% 3.10/1.00  fof(f79,plain,(
% 3.10/1.00    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f32])).
% 3.10/1.00  
% 3.10/1.00  fof(f99,plain,(
% 3.10/1.00    ~v1_zfmisc_1(sK3) | ~v2_tex_2(sK3,sK2)),
% 3.10/1.00    inference(cnf_transformation,[],[f62])).
% 3.10/1.00  
% 3.10/1.00  cnf(c_5068,plain,
% 3.10/1.00      ( ~ v1_zfmisc_1(X0) | v1_zfmisc_1(X1) | X1 != X0 ),
% 3.10/1.00      theory(equality) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_9054,plain,
% 3.10/1.00      ( v1_zfmisc_1(X0)
% 3.10/1.00      | ~ v1_zfmisc_1(u1_struct_0(sK1(X1,sK3)))
% 3.10/1.00      | X0 != u1_struct_0(sK1(X1,sK3)) ),
% 3.10/1.00      inference(instantiation,[status(thm)],[c_5068]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_11492,plain,
% 3.10/1.00      ( ~ v1_zfmisc_1(u1_struct_0(sK1(X0,sK3)))
% 3.10/1.00      | v1_zfmisc_1(sK3)
% 3.10/1.00      | sK3 != u1_struct_0(sK1(X0,sK3)) ),
% 3.10/1.00      inference(instantiation,[status(thm)],[c_9054]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_11494,plain,
% 3.10/1.00      ( ~ v1_zfmisc_1(u1_struct_0(sK1(sK2,sK3)))
% 3.10/1.00      | v1_zfmisc_1(sK3)
% 3.10/1.00      | sK3 != u1_struct_0(sK1(sK2,sK3)) ),
% 3.10/1.00      inference(instantiation,[status(thm)],[c_11492]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_30,negated_conjecture,
% 3.10/1.00      ( v2_tex_2(sK3,sK2) | v1_zfmisc_1(sK3) ),
% 3.10/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_5883,plain,
% 3.10/1.00      ( v2_tex_2(sK3,sK2) = iProver_top
% 3.10/1.00      | v1_zfmisc_1(sK3) = iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_31,negated_conjecture,
% 3.10/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.10/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_5882,plain,
% 3.10/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_24,plain,
% 3.10/1.00      ( ~ v2_tex_2(X0,X1)
% 3.10/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.10/1.00      | ~ v2_pre_topc(X1)
% 3.10/1.00      | ~ l1_pre_topc(X1)
% 3.10/1.00      | v2_struct_0(X1)
% 3.10/1.00      | v1_xboole_0(X0)
% 3.10/1.00      | u1_struct_0(sK1(X1,X0)) = X0 ),
% 3.10/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_5889,plain,
% 3.10/1.00      ( u1_struct_0(sK1(X0,X1)) = X1
% 3.10/1.00      | v2_tex_2(X1,X0) != iProver_top
% 3.10/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.10/1.00      | v2_pre_topc(X0) != iProver_top
% 3.10/1.00      | l1_pre_topc(X0) != iProver_top
% 3.10/1.00      | v2_struct_0(X0) = iProver_top
% 3.10/1.00      | v1_xboole_0(X1) = iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_7612,plain,
% 3.10/1.00      ( u1_struct_0(sK1(sK2,sK3)) = sK3
% 3.10/1.00      | v2_tex_2(sK3,sK2) != iProver_top
% 3.10/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.10/1.00      | l1_pre_topc(sK2) != iProver_top
% 3.10/1.00      | v2_struct_0(sK2) = iProver_top
% 3.10/1.00      | v1_xboole_0(sK3) = iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_5882,c_5889]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_36,negated_conjecture,
% 3.10/1.00      ( ~ v2_struct_0(sK2) ),
% 3.10/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_37,plain,
% 3.10/1.00      ( v2_struct_0(sK2) != iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_35,negated_conjecture,
% 3.10/1.00      ( v2_pre_topc(sK2) ),
% 3.10/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_38,plain,
% 3.10/1.00      ( v2_pre_topc(sK2) = iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_33,negated_conjecture,
% 3.10/1.00      ( l1_pre_topc(sK2) ),
% 3.10/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_40,plain,
% 3.10/1.00      ( l1_pre_topc(sK2) = iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_32,negated_conjecture,
% 3.10/1.00      ( ~ v1_xboole_0(sK3) ),
% 3.10/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_41,plain,
% 3.10/1.00      ( v1_xboole_0(sK3) != iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_7756,plain,
% 3.10/1.00      ( u1_struct_0(sK1(sK2,sK3)) = sK3
% 3.10/1.00      | v2_tex_2(sK3,sK2) != iProver_top ),
% 3.10/1.00      inference(global_propositional_subsumption,
% 3.10/1.00                [status(thm)],
% 3.10/1.00                [c_7612,c_37,c_38,c_40,c_41]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_7762,plain,
% 3.10/1.00      ( u1_struct_0(sK1(sK2,sK3)) = sK3
% 3.10/1.00      | v1_zfmisc_1(sK3) = iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_5883,c_7756]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_0,plain,
% 3.10/1.00      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.10/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_4,plain,
% 3.10/1.00      ( r1_tarski(k1_tarski(X0),X1) | ~ r2_hidden(X0,X1) ),
% 3.10/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_282,plain,
% 3.10/1.00      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1) ),
% 3.10/1.00      inference(prop_impl,[status(thm)],[c_4]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_283,plain,
% 3.10/1.00      ( r1_tarski(k1_tarski(X0),X1) | ~ r2_hidden(X0,X1) ),
% 3.10/1.00      inference(renaming,[status(thm)],[c_282]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_755,plain,
% 3.10/1.00      ( r1_tarski(k1_tarski(X0),X1)
% 3.10/1.00      | v1_xboole_0(X2)
% 3.10/1.00      | X1 != X2
% 3.10/1.00      | sK0(X2) != X0 ),
% 3.10/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_283]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_756,plain,
% 3.10/1.00      ( r1_tarski(k1_tarski(sK0(X0)),X0) | v1_xboole_0(X0) ),
% 3.10/1.00      inference(unflattening,[status(thm)],[c_755]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_5870,plain,
% 3.10/1.00      ( r1_tarski(k1_tarski(sK0(X0)),X0) = iProver_top
% 3.10/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_756]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_23,plain,
% 3.10/1.00      ( ~ r1_tarski(X0,X1)
% 3.10/1.00      | ~ v1_zfmisc_1(X1)
% 3.10/1.00      | v1_xboole_0(X0)
% 3.10/1.00      | v1_xboole_0(X1)
% 3.10/1.00      | X1 = X0 ),
% 3.10/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_5890,plain,
% 3.10/1.00      ( X0 = X1
% 3.10/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.10/1.00      | v1_zfmisc_1(X0) != iProver_top
% 3.10/1.00      | v1_xboole_0(X1) = iProver_top
% 3.10/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_7383,plain,
% 3.10/1.00      ( k1_tarski(sK0(X0)) = X0
% 3.10/1.00      | v1_zfmisc_1(X0) != iProver_top
% 3.10/1.00      | v1_xboole_0(X0) = iProver_top
% 3.10/1.00      | v1_xboole_0(k1_tarski(sK0(X0))) = iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_5870,c_5890]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_3,plain,
% 3.10/1.00      ( ~ v1_xboole_0(k1_tarski(X0)) ),
% 3.10/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_5899,plain,
% 3.10/1.00      ( v1_xboole_0(k1_tarski(X0)) != iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_10039,plain,
% 3.10/1.00      ( k1_tarski(sK0(X0)) = X0
% 3.10/1.00      | v1_zfmisc_1(X0) != iProver_top
% 3.10/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.10/1.00      inference(forward_subsumption_resolution,
% 3.10/1.00                [status(thm)],
% 3.10/1.00                [c_7383,c_5899]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_10045,plain,
% 3.10/1.00      ( u1_struct_0(sK1(sK2,sK3)) = sK3
% 3.10/1.00      | k1_tarski(sK0(sK3)) = sK3
% 3.10/1.00      | v1_xboole_0(sK3) = iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_7762,c_10039]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_10074,plain,
% 3.10/1.00      ( v1_xboole_0(sK3)
% 3.10/1.00      | u1_struct_0(sK1(sK2,sK3)) = sK3
% 3.10/1.00      | k1_tarski(sK0(sK3)) = sK3 ),
% 3.10/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_10045]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_10191,plain,
% 3.10/1.00      ( k1_tarski(sK0(sK3)) = sK3 | u1_struct_0(sK1(sK2,sK3)) = sK3 ),
% 3.10/1.00      inference(global_propositional_subsumption,
% 3.10/1.00                [status(thm)],
% 3.10/1.00                [c_10045,c_32,c_10074]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_10192,plain,
% 3.10/1.00      ( u1_struct_0(sK1(sK2,sK3)) = sK3 | k1_tarski(sK0(sK3)) = sK3 ),
% 3.10/1.00      inference(renaming,[status(thm)],[c_10191]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_28,plain,
% 3.10/1.00      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 3.10/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.10/1.00      | ~ v2_pre_topc(X0)
% 3.10/1.00      | ~ l1_pre_topc(X0)
% 3.10/1.00      | v2_struct_0(X0) ),
% 3.10/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_5885,plain,
% 3.10/1.00      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) = iProver_top
% 3.10/1.00      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.10/1.00      | v2_pre_topc(X0) != iProver_top
% 3.10/1.00      | l1_pre_topc(X0) != iProver_top
% 3.10/1.00      | v2_struct_0(X0) = iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_10197,plain,
% 3.10/1.00      ( k1_tarski(sK0(sK3)) = sK3
% 3.10/1.00      | v2_tex_2(k6_domain_1(sK3,X0),sK1(sK2,sK3)) = iProver_top
% 3.10/1.00      | m1_subset_1(X0,u1_struct_0(sK1(sK2,sK3))) != iProver_top
% 3.10/1.00      | v2_pre_topc(sK1(sK2,sK3)) != iProver_top
% 3.10/1.00      | l1_pre_topc(sK1(sK2,sK3)) != iProver_top
% 3.10/1.00      | v2_struct_0(sK1(sK2,sK3)) = iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_10192,c_5885]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_20,plain,
% 3.10/1.00      ( ~ v2_tdlat_3(X0)
% 3.10/1.00      | ~ v1_tdlat_3(X0)
% 3.10/1.00      | ~ v2_pre_topc(X0)
% 3.10/1.00      | ~ l1_pre_topc(X0)
% 3.10/1.00      | v2_struct_0(X0)
% 3.10/1.00      | v7_struct_0(X0) ),
% 3.10/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_18,plain,
% 3.10/1.00      ( ~ v2_tdlat_3(X0) | v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 3.10/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_13,plain,
% 3.10/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.10/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_12,plain,
% 3.10/1.00      ( ~ l1_struct_0(X0) | ~ v2_struct_0(X0) | v7_struct_0(X0) ),
% 3.10/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_204,plain,
% 3.10/1.00      ( ~ l1_pre_topc(X0)
% 3.10/1.00      | ~ v2_tdlat_3(X0)
% 3.10/1.00      | ~ v1_tdlat_3(X0)
% 3.10/1.00      | v7_struct_0(X0) ),
% 3.10/1.00      inference(global_propositional_subsumption,
% 3.10/1.00                [status(thm)],
% 3.10/1.00                [c_20,c_18,c_13,c_12]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_205,plain,
% 3.10/1.00      ( ~ v2_tdlat_3(X0)
% 3.10/1.00      | ~ v1_tdlat_3(X0)
% 3.10/1.00      | ~ l1_pre_topc(X0)
% 3.10/1.00      | v7_struct_0(X0) ),
% 3.10/1.00      inference(renaming,[status(thm)],[c_204]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_15,plain,
% 3.10/1.00      ( v1_zfmisc_1(u1_struct_0(X0))
% 3.10/1.00      | ~ l1_struct_0(X0)
% 3.10/1.00      | ~ v7_struct_0(X0) ),
% 3.10/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_479,plain,
% 3.10/1.00      ( v1_zfmisc_1(u1_struct_0(X0))
% 3.10/1.00      | ~ l1_pre_topc(X0)
% 3.10/1.00      | ~ v7_struct_0(X0) ),
% 3.10/1.00      inference(resolution,[status(thm)],[c_13,c_15]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_525,plain,
% 3.10/1.00      ( ~ v2_tdlat_3(X0)
% 3.10/1.00      | ~ v1_tdlat_3(X0)
% 3.10/1.00      | v1_zfmisc_1(u1_struct_0(X0))
% 3.10/1.00      | ~ l1_pre_topc(X0) ),
% 3.10/1.00      inference(resolution,[status(thm)],[c_205,c_479]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_5875,plain,
% 3.10/1.00      ( v2_tdlat_3(X0) != iProver_top
% 3.10/1.00      | v1_tdlat_3(X0) != iProver_top
% 3.10/1.00      | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top
% 3.10/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_525]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_10195,plain,
% 3.10/1.00      ( k1_tarski(sK0(sK3)) = sK3
% 3.10/1.00      | v2_tdlat_3(sK1(sK2,sK3)) != iProver_top
% 3.10/1.00      | v1_tdlat_3(sK1(sK2,sK3)) != iProver_top
% 3.10/1.00      | v1_zfmisc_1(sK3) = iProver_top
% 3.10/1.00      | l1_pre_topc(sK1(sK2,sK3)) != iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_10192,c_5875]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_43,plain,
% 3.10/1.00      ( v2_tex_2(sK3,sK2) = iProver_top
% 3.10/1.00      | v1_zfmisc_1(sK3) = iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_26,plain,
% 3.10/1.00      ( ~ v2_tex_2(X0,X1)
% 3.10/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.10/1.00      | v1_tdlat_3(sK1(X1,X0))
% 3.10/1.00      | ~ v2_pre_topc(X1)
% 3.10/1.00      | ~ l1_pre_topc(X1)
% 3.10/1.00      | v2_struct_0(X1)
% 3.10/1.00      | v1_xboole_0(X0) ),
% 3.10/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_290,plain,
% 3.10/1.00      ( v1_zfmisc_1(sK3) | v2_tex_2(sK3,sK2) ),
% 3.10/1.00      inference(prop_impl,[status(thm)],[c_30]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_291,plain,
% 3.10/1.00      ( v2_tex_2(sK3,sK2) | v1_zfmisc_1(sK3) ),
% 3.10/1.00      inference(renaming,[status(thm)],[c_290]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1043,plain,
% 3.10/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.10/1.00      | v1_tdlat_3(sK1(X1,X0))
% 3.10/1.00      | ~ v2_pre_topc(X1)
% 3.10/1.00      | v1_zfmisc_1(sK3)
% 3.10/1.00      | ~ l1_pre_topc(X1)
% 3.10/1.00      | v2_struct_0(X1)
% 3.10/1.00      | v1_xboole_0(X0)
% 3.10/1.00      | sK2 != X1
% 3.10/1.00      | sK3 != X0 ),
% 3.10/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_291]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1044,plain,
% 3.10/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.10/1.00      | v1_tdlat_3(sK1(sK2,sK3))
% 3.10/1.00      | ~ v2_pre_topc(sK2)
% 3.10/1.00      | v1_zfmisc_1(sK3)
% 3.10/1.00      | ~ l1_pre_topc(sK2)
% 3.10/1.00      | v2_struct_0(sK2)
% 3.10/1.00      | v1_xboole_0(sK3) ),
% 3.10/1.00      inference(unflattening,[status(thm)],[c_1043]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1046,plain,
% 3.10/1.00      ( v1_zfmisc_1(sK3) | v1_tdlat_3(sK1(sK2,sK3)) ),
% 3.10/1.00      inference(global_propositional_subsumption,
% 3.10/1.00                [status(thm)],
% 3.10/1.00                [c_1044,c_36,c_35,c_33,c_32,c_31]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1047,plain,
% 3.10/1.00      ( v1_tdlat_3(sK1(sK2,sK3)) | v1_zfmisc_1(sK3) ),
% 3.10/1.00      inference(renaming,[status(thm)],[c_1046]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1048,plain,
% 3.10/1.00      ( v1_tdlat_3(sK1(sK2,sK3)) = iProver_top
% 3.10/1.00      | v1_zfmisc_1(sK3) = iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_1047]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_25,plain,
% 3.10/1.00      ( ~ v2_tex_2(X0,X1)
% 3.10/1.00      | m1_pre_topc(sK1(X1,X0),X1)
% 3.10/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.10/1.00      | ~ v2_pre_topc(X1)
% 3.10/1.00      | ~ l1_pre_topc(X1)
% 3.10/1.00      | v2_struct_0(X1)
% 3.10/1.00      | v1_xboole_0(X0) ),
% 3.10/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_5888,plain,
% 3.10/1.00      ( v2_tex_2(X0,X1) != iProver_top
% 3.10/1.00      | m1_pre_topc(sK1(X1,X0),X1) = iProver_top
% 3.10/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.10/1.00      | v2_pre_topc(X1) != iProver_top
% 3.10/1.00      | l1_pre_topc(X1) != iProver_top
% 3.10/1.00      | v2_struct_0(X1) = iProver_top
% 3.10/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_8406,plain,
% 3.10/1.00      ( v2_tex_2(sK3,sK2) != iProver_top
% 3.10/1.00      | m1_pre_topc(sK1(sK2,sK3),sK2) = iProver_top
% 3.10/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.10/1.00      | l1_pre_topc(sK2) != iProver_top
% 3.10/1.00      | v2_struct_0(sK2) = iProver_top
% 3.10/1.00      | v1_xboole_0(sK3) = iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_5882,c_5888]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_2663,plain,
% 3.10/1.00      ( ~ v2_tex_2(X0,X1)
% 3.10/1.00      | m1_pre_topc(sK1(X1,X0),X1)
% 3.10/1.00      | ~ v2_pre_topc(X1)
% 3.10/1.00      | ~ l1_pre_topc(X1)
% 3.10/1.00      | v2_struct_0(X1)
% 3.10/1.00      | v1_xboole_0(X0)
% 3.10/1.00      | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(sK2))
% 3.10/1.00      | sK3 != X0 ),
% 3.10/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_31]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_2664,plain,
% 3.10/1.00      ( ~ v2_tex_2(sK3,X0)
% 3.10/1.00      | m1_pre_topc(sK1(X0,sK3),X0)
% 3.10/1.00      | ~ v2_pre_topc(X0)
% 3.10/1.00      | ~ l1_pre_topc(X0)
% 3.10/1.00      | v2_struct_0(X0)
% 3.10/1.00      | v1_xboole_0(sK3)
% 3.10/1.00      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK2)) ),
% 3.10/1.00      inference(unflattening,[status(thm)],[c_2663]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_2668,plain,
% 3.10/1.00      ( v2_struct_0(X0)
% 3.10/1.00      | ~ l1_pre_topc(X0)
% 3.10/1.00      | ~ v2_pre_topc(X0)
% 3.10/1.00      | m1_pre_topc(sK1(X0,sK3),X0)
% 3.10/1.00      | ~ v2_tex_2(sK3,X0)
% 3.10/1.00      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK2)) ),
% 3.10/1.00      inference(global_propositional_subsumption,
% 3.10/1.00                [status(thm)],
% 3.10/1.00                [c_2664,c_32]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_2669,plain,
% 3.10/1.00      ( ~ v2_tex_2(sK3,X0)
% 3.10/1.00      | m1_pre_topc(sK1(X0,sK3),X0)
% 3.10/1.00      | ~ v2_pre_topc(X0)
% 3.10/1.00      | ~ l1_pre_topc(X0)
% 3.10/1.00      | v2_struct_0(X0)
% 3.10/1.00      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK2)) ),
% 3.10/1.00      inference(renaming,[status(thm)],[c_2668]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_2670,plain,
% 3.10/1.00      ( k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK2))
% 3.10/1.00      | v2_tex_2(sK3,X0) != iProver_top
% 3.10/1.00      | m1_pre_topc(sK1(X0,sK3),X0) = iProver_top
% 3.10/1.00      | v2_pre_topc(X0) != iProver_top
% 3.10/1.00      | l1_pre_topc(X0) != iProver_top
% 3.10/1.00      | v2_struct_0(X0) = iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_2669]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_2672,plain,
% 3.10/1.00      ( k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
% 3.10/1.00      | v2_tex_2(sK3,sK2) != iProver_top
% 3.10/1.00      | m1_pre_topc(sK1(sK2,sK3),sK2) = iProver_top
% 3.10/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.10/1.00      | l1_pre_topc(sK2) != iProver_top
% 3.10/1.00      | v2_struct_0(sK2) = iProver_top ),
% 3.10/1.00      inference(instantiation,[status(thm)],[c_2670]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_5057,plain,( X0 = X0 ),theory(equality) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_7799,plain,
% 3.10/1.00      ( k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(u1_struct_0(sK2)) ),
% 3.10/1.00      inference(instantiation,[status(thm)],[c_5057]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_8841,plain,
% 3.10/1.00      ( v2_tex_2(sK3,sK2) != iProver_top
% 3.10/1.00      | m1_pre_topc(sK1(sK2,sK3),sK2) = iProver_top ),
% 3.10/1.00      inference(global_propositional_subsumption,
% 3.10/1.00                [status(thm)],
% 3.10/1.00                [c_8406,c_37,c_38,c_40,c_41,c_42,c_6309]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_14,plain,
% 3.10/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.10/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_5894,plain,
% 3.10/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.10/1.00      | l1_pre_topc(X1) != iProver_top
% 3.10/1.00      | l1_pre_topc(X0) = iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_8847,plain,
% 3.10/1.00      ( v2_tex_2(sK3,sK2) != iProver_top
% 3.10/1.00      | l1_pre_topc(sK1(sK2,sK3)) = iProver_top
% 3.10/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_8841,c_5894]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_22,plain,
% 3.10/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.10/1.00      | ~ v2_tdlat_3(X1)
% 3.10/1.00      | v2_tdlat_3(X0)
% 3.10/1.00      | ~ v2_pre_topc(X1)
% 3.10/1.00      | ~ l1_pre_topc(X1)
% 3.10/1.00      | v2_struct_0(X1) ),
% 3.10/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1293,plain,
% 3.10/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.10/1.00      | ~ v2_tdlat_3(X2)
% 3.10/1.00      | ~ v2_tdlat_3(X1)
% 3.10/1.00      | v2_tdlat_3(X0)
% 3.10/1.00      | ~ l1_pre_topc(X2)
% 3.10/1.00      | ~ l1_pre_topc(X1)
% 3.10/1.00      | v2_struct_0(X1)
% 3.10/1.00      | X1 != X2 ),
% 3.10/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_22]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1294,plain,
% 3.10/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.10/1.00      | ~ v2_tdlat_3(X1)
% 3.10/1.00      | v2_tdlat_3(X0)
% 3.10/1.00      | ~ l1_pre_topc(X1)
% 3.10/1.00      | v2_struct_0(X1) ),
% 3.10/1.00      inference(unflattening,[status(thm)],[c_1293]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_5869,plain,
% 3.10/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.10/1.00      | v2_tdlat_3(X1) != iProver_top
% 3.10/1.00      | v2_tdlat_3(X0) = iProver_top
% 3.10/1.00      | l1_pre_topc(X1) != iProver_top
% 3.10/1.00      | v2_struct_0(X1) = iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_1294]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_8848,plain,
% 3.10/1.00      ( v2_tex_2(sK3,sK2) != iProver_top
% 3.10/1.00      | v2_tdlat_3(sK1(sK2,sK3)) = iProver_top
% 3.10/1.00      | v2_tdlat_3(sK2) != iProver_top
% 3.10/1.00      | l1_pre_topc(sK2) != iProver_top
% 3.10/1.00      | v2_struct_0(sK2) = iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_8841,c_5869]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_34,negated_conjecture,
% 3.10/1.00      ( v2_tdlat_3(sK2) ),
% 3.10/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_39,plain,
% 3.10/1.00      ( v2_tdlat_3(sK2) = iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_9047,plain,
% 3.10/1.00      ( v2_tdlat_3(sK1(sK2,sK3)) = iProver_top
% 3.10/1.00      | v2_tex_2(sK3,sK2) != iProver_top ),
% 3.10/1.00      inference(global_propositional_subsumption,
% 3.10/1.00                [status(thm)],
% 3.10/1.00                [c_8848,c_37,c_39,c_40]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_9048,plain,
% 3.10/1.00      ( v2_tex_2(sK3,sK2) != iProver_top
% 3.10/1.00      | v2_tdlat_3(sK1(sK2,sK3)) = iProver_top ),
% 3.10/1.00      inference(renaming,[status(thm)],[c_9047]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_10514,plain,
% 3.10/1.00      ( v1_zfmisc_1(sK3) = iProver_top | k1_tarski(sK0(sK3)) = sK3 ),
% 3.10/1.00      inference(global_propositional_subsumption,
% 3.10/1.00                [status(thm)],
% 3.10/1.00                [c_10195,c_37,c_39,c_40,c_43,c_1048,c_8847,c_8848]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_10515,plain,
% 3.10/1.00      ( k1_tarski(sK0(sK3)) = sK3 | v1_zfmisc_1(sK3) = iProver_top ),
% 3.10/1.00      inference(renaming,[status(thm)],[c_10514]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_10520,plain,
% 3.10/1.00      ( k1_tarski(sK0(sK3)) = sK3 | v1_xboole_0(sK3) = iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_10515,c_10039]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_10523,plain,
% 3.10/1.00      ( k1_tarski(sK0(sK3)) = sK3 ),
% 3.10/1.00      inference(global_propositional_subsumption,
% 3.10/1.00                [status(thm)],
% 3.10/1.00                [c_10197,c_41,c_10520]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_11,plain,
% 3.10/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.10/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_5895,plain,
% 3.10/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.10/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_6384,plain,
% 3.10/1.00      ( r1_tarski(sK3,u1_struct_0(sK2)) = iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_5882,c_5895]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_2,plain,
% 3.10/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 3.10/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_5900,plain,
% 3.10/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.10/1.00      | r1_tarski(X2,X0) != iProver_top
% 3.10/1.00      | r1_tarski(X2,X1) = iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_6863,plain,
% 3.10/1.00      ( r1_tarski(X0,u1_struct_0(sK2)) = iProver_top
% 3.10/1.00      | r1_tarski(X0,sK3) != iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_6384,c_5900]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_5,plain,
% 3.10/1.00      ( ~ r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1) ),
% 3.10/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_280,plain,
% 3.10/1.00      ( r2_hidden(X0,X1) | ~ r1_tarski(k1_tarski(X0),X1) ),
% 3.10/1.00      inference(prop_impl,[status(thm)],[c_5]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_281,plain,
% 3.10/1.00      ( ~ r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1) ),
% 3.10/1.00      inference(renaming,[status(thm)],[c_280]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_8,plain,
% 3.10/1.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.10/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1,plain,
% 3.10/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.10/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_221,plain,
% 3.10/1.00      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 3.10/1.00      inference(global_propositional_subsumption,[status(thm)],[c_8,c_1]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_222,plain,
% 3.10/1.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.10/1.00      inference(renaming,[status(thm)],[c_221]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_720,plain,
% 3.10/1.00      ( m1_subset_1(X0,X1) | ~ r1_tarski(k1_tarski(X0),X1) ),
% 3.10/1.00      inference(resolution,[status(thm)],[c_281,c_222]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_5873,plain,
% 3.10/1.00      ( m1_subset_1(X0,X1) = iProver_top
% 3.10/1.00      | r1_tarski(k1_tarski(X0),X1) != iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_720]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_7046,plain,
% 3.10/1.00      ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
% 3.10/1.00      | r1_tarski(k1_tarski(X0),sK3) != iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_6863,c_5873]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_7072,plain,
% 3.10/1.00      ( m1_subset_1(sK0(sK3),u1_struct_0(sK2)) = iProver_top
% 3.10/1.00      | v1_xboole_0(sK3) = iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_5870,c_7046]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_7285,plain,
% 3.10/1.00      ( m1_subset_1(sK0(sK3),u1_struct_0(sK2)) = iProver_top ),
% 3.10/1.00      inference(global_propositional_subsumption,
% 3.10/1.00                [status(thm)],
% 3.10/1.00                [c_7072,c_41]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_16,plain,
% 3.10/1.00      ( ~ m1_subset_1(X0,X1)
% 3.10/1.00      | v1_xboole_0(X1)
% 3.10/1.00      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 3.10/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_5893,plain,
% 3.10/1.00      ( k6_domain_1(X0,X1) = k1_tarski(X1)
% 3.10/1.00      | m1_subset_1(X1,X0) != iProver_top
% 3.10/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_7291,plain,
% 3.10/1.00      ( k6_domain_1(u1_struct_0(sK2),sK0(sK3)) = k1_tarski(sK0(sK3))
% 3.10/1.00      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_7285,c_5893]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_732,plain,
% 3.10/1.00      ( ~ r1_tarski(k1_tarski(X0),X1) | ~ v1_xboole_0(X1) ),
% 3.10/1.00      inference(resolution,[status(thm)],[c_281,c_1]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_5872,plain,
% 3.10/1.00      ( r1_tarski(k1_tarski(X0),X1) != iProver_top
% 3.10/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_732]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_7047,plain,
% 3.10/1.00      ( r1_tarski(k1_tarski(X0),sK3) != iProver_top
% 3.10/1.00      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_6863,c_5872]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_7162,plain,
% 3.10/1.00      ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top
% 3.10/1.00      | v1_xboole_0(sK3) = iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_5870,c_7047]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_8169,plain,
% 3.10/1.00      ( k6_domain_1(u1_struct_0(sK2),sK0(sK3)) = k1_tarski(sK0(sK3)) ),
% 3.10/1.00      inference(global_propositional_subsumption,
% 3.10/1.00                [status(thm)],
% 3.10/1.00                [c_7291,c_41,c_7162]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_10527,plain,
% 3.10/1.00      ( k6_domain_1(u1_struct_0(sK2),sK0(sK3)) = sK3 ),
% 3.10/1.00      inference(demodulation,[status(thm)],[c_10523,c_8169]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_11224,plain,
% 3.10/1.00      ( v2_tex_2(sK3,sK2) = iProver_top
% 3.10/1.00      | m1_subset_1(sK0(sK3),u1_struct_0(sK2)) != iProver_top
% 3.10/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.10/1.00      | l1_pre_topc(sK2) != iProver_top
% 3.10/1.00      | v2_struct_0(sK2) = iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_10527,c_5885]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_11225,plain,
% 3.10/1.00      ( v2_tex_2(sK3,sK2)
% 3.10/1.00      | ~ m1_subset_1(sK0(sK3),u1_struct_0(sK2))
% 3.10/1.00      | ~ v2_pre_topc(sK2)
% 3.10/1.00      | ~ l1_pre_topc(sK2)
% 3.10/1.00      | v2_struct_0(sK2) ),
% 3.10/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_11224]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_9049,plain,
% 3.10/1.00      ( ~ v2_tex_2(sK3,sK2) | v2_tdlat_3(sK1(sK2,sK3)) ),
% 3.10/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_9048]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_8865,plain,
% 3.10/1.00      ( ~ v2_tex_2(sK3,sK2)
% 3.10/1.00      | l1_pre_topc(sK1(sK2,sK3))
% 3.10/1.00      | ~ l1_pre_topc(sK2) ),
% 3.10/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_8847]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_5887,plain,
% 3.10/1.00      ( v2_tex_2(X0,X1) != iProver_top
% 3.10/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.10/1.00      | v1_tdlat_3(sK1(X1,X0)) = iProver_top
% 3.10/1.00      | v2_pre_topc(X1) != iProver_top
% 3.10/1.00      | l1_pre_topc(X1) != iProver_top
% 3.10/1.00      | v2_struct_0(X1) = iProver_top
% 3.10/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_7469,plain,
% 3.10/1.00      ( v2_tex_2(sK3,sK2) != iProver_top
% 3.10/1.00      | v1_tdlat_3(sK1(sK2,sK3)) = iProver_top
% 3.10/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.10/1.00      | l1_pre_topc(sK2) != iProver_top
% 3.10/1.00      | v2_struct_0(sK2) = iProver_top
% 3.10/1.00      | v1_xboole_0(sK3) = iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_5882,c_5887]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_7660,plain,
% 3.10/1.00      ( v2_tex_2(sK3,sK2) != iProver_top
% 3.10/1.00      | v1_tdlat_3(sK1(sK2,sK3)) = iProver_top ),
% 3.10/1.00      inference(global_propositional_subsumption,
% 3.10/1.00                [status(thm)],
% 3.10/1.00                [c_7469,c_37,c_38,c_40,c_41]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_7662,plain,
% 3.10/1.00      ( ~ v2_tex_2(sK3,sK2) | v1_tdlat_3(sK1(sK2,sK3)) ),
% 3.10/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_7660]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_7073,plain,
% 3.10/1.00      ( m1_subset_1(sK0(sK3),u1_struct_0(sK2)) | v1_xboole_0(sK3) ),
% 3.10/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_7072]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_5058,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_6350,plain,
% 3.10/1.00      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 3.10/1.00      inference(instantiation,[status(thm)],[c_5058]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_6543,plain,
% 3.10/1.00      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 3.10/1.00      inference(instantiation,[status(thm)],[c_6350]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_6890,plain,
% 3.10/1.00      ( u1_struct_0(sK1(X0,sK3)) != sK3
% 3.10/1.00      | sK3 = u1_struct_0(sK1(X0,sK3))
% 3.10/1.00      | sK3 != sK3 ),
% 3.10/1.00      inference(instantiation,[status(thm)],[c_6543]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_6891,plain,
% 3.10/1.00      ( u1_struct_0(sK1(sK2,sK3)) != sK3
% 3.10/1.00      | sK3 = u1_struct_0(sK1(sK2,sK3))
% 3.10/1.00      | sK3 != sK3 ),
% 3.10/1.00      inference(instantiation,[status(thm)],[c_6890]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_6779,plain,
% 3.10/1.00      ( ~ v2_tdlat_3(sK1(X0,sK3))
% 3.10/1.00      | ~ v1_tdlat_3(sK1(X0,sK3))
% 3.10/1.00      | v1_zfmisc_1(u1_struct_0(sK1(X0,sK3)))
% 3.10/1.00      | ~ l1_pre_topc(sK1(X0,sK3)) ),
% 3.10/1.00      inference(instantiation,[status(thm)],[c_525]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_6781,plain,
% 3.10/1.00      ( ~ v2_tdlat_3(sK1(sK2,sK3))
% 3.10/1.00      | ~ v1_tdlat_3(sK1(sK2,sK3))
% 3.10/1.00      | v1_zfmisc_1(u1_struct_0(sK1(sK2,sK3)))
% 3.10/1.00      | ~ l1_pre_topc(sK1(sK2,sK3)) ),
% 3.10/1.00      inference(instantiation,[status(thm)],[c_6779]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_6544,plain,
% 3.10/1.00      ( sK3 = sK3 ),
% 3.10/1.00      inference(instantiation,[status(thm)],[c_5057]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_29,negated_conjecture,
% 3.10/1.00      ( ~ v2_tex_2(sK3,sK2) | ~ v1_zfmisc_1(sK3) ),
% 3.10/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(contradiction,plain,
% 3.10/1.00      ( $false ),
% 3.10/1.00      inference(minisat,
% 3.10/1.00                [status(thm)],
% 3.10/1.00                [c_11494,c_11225,c_11224,c_9049,c_8865,c_7756,c_7662,
% 3.10/1.00                 c_7073,c_7072,c_6891,c_6781,c_6544,c_29,c_41,c_32,c_40,
% 3.10/1.00                 c_33,c_38,c_35,c_37,c_36]) ).
% 3.10/1.00  
% 3.10/1.00  
% 3.10/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.10/1.00  
% 3.10/1.00  ------                               Statistics
% 3.10/1.00  
% 3.10/1.00  ------ General
% 3.10/1.00  
% 3.10/1.00  abstr_ref_over_cycles:                  0
% 3.10/1.00  abstr_ref_under_cycles:                 0
% 3.10/1.00  gc_basic_clause_elim:                   0
% 3.10/1.00  forced_gc_time:                         0
% 3.10/1.00  parsing_time:                           0.009
% 3.10/1.00  unif_index_cands_time:                  0.
% 3.10/1.00  unif_index_add_time:                    0.
% 3.10/1.00  orderings_time:                         0.
% 3.10/1.00  out_proof_time:                         0.011
% 3.10/1.00  total_time:                             0.256
% 3.10/1.00  num_of_symbols:                         53
% 3.10/1.00  num_of_terms:                           4967
% 3.10/1.00  
% 3.10/1.00  ------ Preprocessing
% 3.10/1.00  
% 3.10/1.00  num_of_splits:                          0
% 3.10/1.00  num_of_split_atoms:                     0
% 3.10/1.00  num_of_reused_defs:                     0
% 3.10/1.00  num_eq_ax_congr_red:                    22
% 3.10/1.00  num_of_sem_filtered_clauses:            1
% 3.10/1.00  num_of_subtypes:                        0
% 3.10/1.00  monotx_restored_types:                  0
% 3.10/1.00  sat_num_of_epr_types:                   0
% 3.10/1.00  sat_num_of_non_cyclic_types:            0
% 3.10/1.00  sat_guarded_non_collapsed_types:        0
% 3.10/1.00  num_pure_diseq_elim:                    0
% 3.10/1.00  simp_replaced_by:                       0
% 3.10/1.00  res_preprocessed:                       166
% 3.10/1.00  prep_upred:                             0
% 3.10/1.00  prep_unflattend:                        234
% 3.10/1.00  smt_new_axioms:                         0
% 3.10/1.00  pred_elim_cands:                        11
% 3.10/1.00  pred_elim:                              3
% 3.10/1.00  pred_elim_cl:                           3
% 3.10/1.00  pred_elim_cycles:                       17
% 3.10/1.00  merged_defs:                            18
% 3.10/1.00  merged_defs_ncl:                        0
% 3.10/1.00  bin_hyper_res:                          18
% 3.10/1.00  prep_cycles:                            4
% 3.10/1.00  pred_elim_time:                         0.068
% 3.10/1.00  splitting_time:                         0.
% 3.10/1.00  sem_filter_time:                        0.
% 3.10/1.00  monotx_time:                            0.001
% 3.10/1.00  subtype_inf_time:                       0.
% 3.10/1.00  
% 3.10/1.00  ------ Problem properties
% 3.10/1.00  
% 3.10/1.00  clauses:                                32
% 3.10/1.00  conjectures:                            8
% 3.10/1.00  epr:                                    15
% 3.10/1.00  horn:                                   20
% 3.10/1.00  ground:                                 8
% 3.10/1.00  unary:                                  7
% 3.10/1.00  binary:                                 8
% 3.10/1.00  lits:                                   97
% 3.10/1.00  lits_eq:                                3
% 3.10/1.00  fd_pure:                                0
% 3.10/1.00  fd_pseudo:                              0
% 3.10/1.00  fd_cond:                                0
% 3.10/1.00  fd_pseudo_cond:                         1
% 3.10/1.00  ac_symbols:                             0
% 3.10/1.00  
% 3.10/1.00  ------ Propositional Solver
% 3.10/1.00  
% 3.10/1.00  prop_solver_calls:                      29
% 3.10/1.00  prop_fast_solver_calls:                 2468
% 3.10/1.00  smt_solver_calls:                       0
% 3.10/1.00  smt_fast_solver_calls:                  0
% 3.10/1.00  prop_num_of_clauses:                    2546
% 3.10/1.00  prop_preprocess_simplified:             8433
% 3.10/1.00  prop_fo_subsumed:                       168
% 3.10/1.00  prop_solver_time:                       0.
% 3.10/1.00  smt_solver_time:                        0.
% 3.10/1.00  smt_fast_solver_time:                   0.
% 3.10/1.00  prop_fast_solver_time:                  0.
% 3.10/1.00  prop_unsat_core_time:                   0.
% 3.10/1.00  
% 3.10/1.00  ------ QBF
% 3.10/1.00  
% 3.10/1.00  qbf_q_res:                              0
% 3.10/1.00  qbf_num_tautologies:                    0
% 3.10/1.00  qbf_prep_cycles:                        0
% 3.10/1.00  
% 3.10/1.00  ------ BMC1
% 3.10/1.00  
% 3.10/1.00  bmc1_current_bound:                     -1
% 3.10/1.00  bmc1_last_solved_bound:                 -1
% 3.10/1.00  bmc1_unsat_core_size:                   -1
% 3.10/1.00  bmc1_unsat_core_parents_size:           -1
% 3.10/1.00  bmc1_merge_next_fun:                    0
% 3.10/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.10/1.00  
% 3.10/1.00  ------ Instantiation
% 3.10/1.00  
% 3.10/1.00  inst_num_of_clauses:                    642
% 3.10/1.00  inst_num_in_passive:                    219
% 3.10/1.00  inst_num_in_active:                     420
% 3.10/1.00  inst_num_in_unprocessed:                2
% 3.10/1.00  inst_num_of_loops:                      463
% 3.10/1.00  inst_num_of_learning_restarts:          0
% 3.10/1.00  inst_num_moves_active_passive:          37
% 3.10/1.00  inst_lit_activity:                      0
% 3.10/1.00  inst_lit_activity_moves:                0
% 3.10/1.00  inst_num_tautologies:                   0
% 3.10/1.00  inst_num_prop_implied:                  0
% 3.10/1.00  inst_num_existing_simplified:           0
% 3.10/1.00  inst_num_eq_res_simplified:             0
% 3.10/1.00  inst_num_child_elim:                    0
% 3.10/1.00  inst_num_of_dismatching_blockings:      270
% 3.10/1.00  inst_num_of_non_proper_insts:           877
% 3.10/1.00  inst_num_of_duplicates:                 0
% 3.10/1.00  inst_inst_num_from_inst_to_res:         0
% 3.10/1.00  inst_dismatching_checking_time:         0.
% 3.10/1.00  
% 3.10/1.00  ------ Resolution
% 3.10/1.00  
% 3.10/1.00  res_num_of_clauses:                     0
% 3.10/1.00  res_num_in_passive:                     0
% 3.10/1.00  res_num_in_active:                      0
% 3.10/1.00  res_num_of_loops:                       170
% 3.10/1.00  res_forward_subset_subsumed:            101
% 3.10/1.00  res_backward_subset_subsumed:           0
% 3.10/1.00  res_forward_subsumed:                   1
% 3.10/1.00  res_backward_subsumed:                  1
% 3.10/1.00  res_forward_subsumption_resolution:     1
% 3.10/1.00  res_backward_subsumption_resolution:    2
% 3.10/1.00  res_clause_to_clause_subsumption:       391
% 3.10/1.00  res_orphan_elimination:                 0
% 3.10/1.00  res_tautology_del:                      209
% 3.10/1.00  res_num_eq_res_simplified:              0
% 3.10/1.00  res_num_sel_changes:                    0
% 3.10/1.00  res_moves_from_active_to_pass:          0
% 3.10/1.00  
% 3.10/1.00  ------ Superposition
% 3.10/1.00  
% 3.10/1.00  sup_time_total:                         0.
% 3.10/1.00  sup_time_generating:                    0.
% 3.10/1.00  sup_time_sim_full:                      0.
% 3.10/1.00  sup_time_sim_immed:                     0.
% 3.10/1.00  
% 3.10/1.00  sup_num_of_clauses:                     150
% 3.10/1.00  sup_num_in_active:                      88
% 3.10/1.00  sup_num_in_passive:                     62
% 3.10/1.00  sup_num_of_loops:                       92
% 3.10/1.00  sup_fw_superposition:                   105
% 3.10/1.00  sup_bw_superposition:                   81
% 3.10/1.00  sup_immediate_simplified:               36
% 3.10/1.00  sup_given_eliminated:                   0
% 3.10/1.00  comparisons_done:                       0
% 3.10/1.00  comparisons_avoided:                    0
% 3.10/1.00  
% 3.10/1.00  ------ Simplifications
% 3.10/1.00  
% 3.10/1.00  
% 3.10/1.00  sim_fw_subset_subsumed:                 25
% 3.10/1.00  sim_bw_subset_subsumed:                 5
% 3.10/1.00  sim_fw_subsumed:                        7
% 3.10/1.00  sim_bw_subsumed:                        0
% 3.10/1.00  sim_fw_subsumption_res:                 1
% 3.10/1.00  sim_bw_subsumption_res:                 0
% 3.10/1.00  sim_tautology_del:                      16
% 3.10/1.00  sim_eq_tautology_del:                   1
% 3.10/1.00  sim_eq_res_simp:                        0
% 3.10/1.00  sim_fw_demodulated:                     1
% 3.10/1.00  sim_bw_demodulated:                     3
% 3.10/1.00  sim_light_normalised:                   6
% 3.10/1.00  sim_joinable_taut:                      0
% 3.10/1.00  sim_joinable_simp:                      0
% 3.10/1.00  sim_ac_normalised:                      0
% 3.10/1.00  sim_smt_subsumption:                    0
% 3.10/1.00  
%------------------------------------------------------------------------------
