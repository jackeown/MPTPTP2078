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
% DateTime   : Thu Dec  3 12:26:51 EST 2020

% Result     : Theorem 3.30s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_658)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f44])).

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
     => ( ( ~ v1_zfmisc_1(sK4)
          | ~ v2_tex_2(sK4,X0) )
        & ( v1_zfmisc_1(sK4)
          | v2_tex_2(sK4,X0) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
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
            | ~ v2_tex_2(X1,sK3) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,sK3) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK3)
      & v2_tdlat_3(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ( ~ v1_zfmisc_1(sK4)
      | ~ v2_tex_2(sK4,sK3) )
    & ( v1_zfmisc_1(sK4)
      | v2_tex_2(sK4,sK3) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & ~ v1_xboole_0(sK4)
    & l1_pre_topc(sK3)
    & v2_tdlat_3(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f55,f57,f56])).

fof(f88,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f58])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK1(X0,X1)) = X1
        & m1_pre_topc(sK1(X0,X1),X0)
        & ~ v2_struct_0(sK1(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK1(X0,X1)) = X1
            & m1_pre_topc(sK1(X0,X1),X0)
            & ~ v2_struct_0(sK1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f50])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f86,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f87,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f58])).

fof(f76,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f46,f47])).

fof(f60,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f89,plain,
    ( v1_zfmisc_1(sK4)
    | v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(pure_predicate_removal,[],[f15])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_tdlat_3(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK2(X0,X1)) = X1
        & m1_pre_topc(sK2(X0,X1),X0)
        & v1_tdlat_3(sK2(X0,X1))
        & ~ v2_struct_0(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK2(X0,X1)) = X1
            & m1_pre_topc(sK2(X0,X1),X0)
            & v1_tdlat_3(sK2(X0,X1))
            & ~ v2_struct_0(sK2(X0,X1)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f52])).

fof(f81,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK2(X0,X1)) = X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f84,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f77,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f59,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( ~ v7_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ( ~ v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_tdlat_3(X1)
      | v7_struct_0(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f66,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f68,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f67,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f71,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f85,plain,(
    v2_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK2(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f90,plain,
    ( ~ v1_zfmisc_1(sK4)
    | ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2300,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_16,plain,
    ( m1_pre_topc(sK1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2304,plain,
    ( m1_pre_topc(sK1(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3113,plain,
    ( m1_pre_topc(sK1(sK3,sK4),sK3) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2300,c_2304])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_32,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_35,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_36,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_37,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2600,plain,
    ( m1_pre_topc(sK1(X0,sK4),X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2601,plain,
    ( m1_pre_topc(sK1(X0,sK4),X0) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2600])).

cnf(c_2603,plain,
    ( m1_pre_topc(sK1(sK3,sK4),sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2601])).

cnf(c_3366,plain,
    ( m1_pre_topc(sK1(sK3,sK4),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3113,c_32,c_35,c_36,c_37,c_2603])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2305,plain,
    ( u1_struct_0(sK1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3051,plain,
    ( u1_struct_0(sK1(sK3,sK4)) = sK4
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2300,c_2305])).

cnf(c_2590,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(sK4)
    | u1_struct_0(sK1(X0,sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2592,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(sK4)
    | u1_struct_0(sK1(sK3,sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_2590])).

cnf(c_3247,plain,
    ( u1_struct_0(sK1(sK3,sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3051,c_31,c_28,c_27,c_26,c_2592])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_475,plain,
    ( m1_subset_1(X0,X1)
    | v1_xboole_0(X2)
    | X1 != X2
    | sK0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_6])).

cnf(c_476,plain,
    ( m1_subset_1(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_475])).

cnf(c_2295,plain,
    ( m1_subset_1(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_476])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2307,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3554,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(X0)),u1_struct_0(X1)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2295,c_2307])).

cnf(c_4720,plain,
    ( m1_pre_topc(sK1(sK3,sK4),X0) != iProver_top
    | m1_subset_1(sK0(sK4),u1_struct_0(X0)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1(sK3,sK4)) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3247,c_3554])).

cnf(c_4774,plain,
    ( m1_pre_topc(sK1(sK3,sK4),X0) != iProver_top
    | m1_subset_1(sK0(sK4),u1_struct_0(X0)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1(sK3,sK4)) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4720,c_3247])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK1(X1,X0))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2580,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK1(X0,sK4))
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2581,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1(X0,sK4)) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2580])).

cnf(c_2583,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK1(sK3,sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2581])).

cnf(c_5194,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(sK1(sK3,sK4),X0) != iProver_top
    | m1_subset_1(sK0(sK4),u1_struct_0(X0)) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4774,c_32,c_35,c_36,c_37,c_2583])).

cnf(c_5195,plain,
    ( m1_pre_topc(sK1(sK3,sK4),X0) != iProver_top
    | m1_subset_1(sK0(sK4),u1_struct_0(X0)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5194])).

cnf(c_5204,plain,
    ( m1_subset_1(sK0(sK4),u1_struct_0(sK3)) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3366,c_5195])).

cnf(c_2525,plain,
    ( m1_subset_1(sK0(sK4),sK4)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_476])).

cnf(c_2526,plain,
    ( m1_subset_1(sK0(sK4),sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2525])).

cnf(c_1738,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2957,plain,
    ( sK0(sK4) = sK0(sK4) ),
    inference(instantiation,[status(thm)],[c_1738])).

cnf(c_1743,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2628,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK0(sK4),sK4)
    | X0 != sK0(sK4)
    | X1 != sK4 ),
    inference(instantiation,[status(thm)],[c_1743])).

cnf(c_2814,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1(X1,sK4)))
    | ~ m1_subset_1(sK0(sK4),sK4)
    | X0 != sK0(sK4)
    | u1_struct_0(sK1(X1,sK4)) != sK4 ),
    inference(instantiation,[status(thm)],[c_2628])).

cnf(c_3138,plain,
    ( m1_subset_1(sK0(sK4),u1_struct_0(sK1(X0,sK4)))
    | ~ m1_subset_1(sK0(sK4),sK4)
    | u1_struct_0(sK1(X0,sK4)) != sK4
    | sK0(sK4) != sK0(sK4) ),
    inference(instantiation,[status(thm)],[c_2814])).

cnf(c_3143,plain,
    ( u1_struct_0(sK1(X0,sK4)) != sK4
    | sK0(sK4) != sK0(sK4)
    | m1_subset_1(sK0(sK4),u1_struct_0(sK1(X0,sK4))) = iProver_top
    | m1_subset_1(sK0(sK4),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3138])).

cnf(c_3145,plain,
    ( u1_struct_0(sK1(sK3,sK4)) != sK4
    | sK0(sK4) != sK0(sK4)
    | m1_subset_1(sK0(sK4),u1_struct_0(sK1(sK3,sK4))) = iProver_top
    | m1_subset_1(sK0(sK4),sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3143])).

cnf(c_2732,plain,
    ( ~ m1_pre_topc(sK1(X0,sK4),X0)
    | m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK1(X0,sK4)))
    | v2_struct_0(X0)
    | v2_struct_0(sK1(X0,sK4))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3779,plain,
    ( ~ m1_pre_topc(sK1(X0,sK4),X0)
    | m1_subset_1(sK0(sK4),u1_struct_0(X0))
    | ~ m1_subset_1(sK0(sK4),u1_struct_0(sK1(X0,sK4)))
    | v2_struct_0(X0)
    | v2_struct_0(sK1(X0,sK4))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_2732])).

cnf(c_3780,plain,
    ( m1_pre_topc(sK1(X0,sK4),X0) != iProver_top
    | m1_subset_1(sK0(sK4),u1_struct_0(X0)) = iProver_top
    | m1_subset_1(sK0(sK4),u1_struct_0(sK1(X0,sK4))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1(X0,sK4)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3779])).

cnf(c_3782,plain,
    ( m1_pre_topc(sK1(sK3,sK4),sK3) != iProver_top
    | m1_subset_1(sK0(sK4),u1_struct_0(sK1(sK3,sK4))) != iProver_top
    | m1_subset_1(sK0(sK4),u1_struct_0(sK3)) = iProver_top
    | v2_struct_0(sK1(sK3,sK4)) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3780])).

cnf(c_5207,plain,
    ( m1_subset_1(sK0(sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5204,c_31,c_32,c_28,c_35,c_27,c_36,c_26,c_37,c_2526,c_2583,c_2592,c_2603,c_2957,c_3145,c_3782])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2306,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5213,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k1_tarski(sK0(sK4))
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5207,c_2306])).

cnf(c_25,negated_conjecture,
    ( v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(sK4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2301,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_19,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK2(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_772,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK2(X1,X0)) = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_773,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(X0)
    | u1_struct_0(sK2(sK3,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_772])).

cnf(c_777,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(X0)
    | u1_struct_0(sK2(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_773,c_31,c_28])).

cnf(c_2291,plain,
    ( u1_struct_0(sK2(sK3,X0)) = X0
    | v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_777])).

cnf(c_2931,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | v2_tex_2(sK4,sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2300,c_2291])).

cnf(c_2967,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | u1_struct_0(sK2(sK3,sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2931,c_36])).

cnf(c_2968,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | v2_tex_2(sK4,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_2967])).

cnf(c_2973,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2301,c_2968])).

cnf(c_3,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_238,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_tarski(X0),X1) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_239,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_238])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_435,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_zfmisc_1(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | X2 != X1
    | X2 = X3
    | k1_tarski(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_239,c_18])).

cnf(c_436,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(k1_tarski(X0))
    | X1 = k1_tarski(X0) ),
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_440,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | X1 = k1_tarski(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_436,c_2,c_1])).

cnf(c_460,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X1)
    | X0 != X1
    | k1_tarski(X2) = X0
    | sK0(X1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_440])).

cnf(c_461,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | k1_tarski(sK0(X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_460])).

cnf(c_2296,plain,
    ( k1_tarski(sK0(X0)) = X0
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_461])).

cnf(c_4179,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | k1_tarski(sK0(sK4)) = sK4
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2973,c_2296])).

cnf(c_242,plain,
    ( v1_zfmisc_1(sK4)
    | v2_tex_2(sK4,sK3) ),
    inference(prop_impl,[status(thm)],[c_25])).

cnf(c_243,plain,
    ( v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(sK4) ),
    inference(renaming,[status(thm)],[c_242])).

cnf(c_656,plain,
    ( v2_tex_2(sK4,sK3)
    | v1_xboole_0(X0)
    | k1_tarski(sK0(X0)) = X0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_243,c_461])).

cnf(c_657,plain,
    ( v2_tex_2(sK4,sK3)
    | v1_xboole_0(sK4)
    | k1_tarski(sK0(sK4)) = sK4 ),
    inference(unflattening,[status(thm)],[c_656])).

cnf(c_659,plain,
    ( v2_tex_2(sK4,sK3)
    | k1_tarski(sK0(sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_657,c_27])).

cnf(c_2543,plain,
    ( ~ v1_zfmisc_1(sK4)
    | v1_xboole_0(sK4)
    | k1_tarski(sK0(sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_461])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_7,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_9,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_416,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_7,c_9])).

cnf(c_496,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_13,c_416])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_500,plain,
    ( v1_zfmisc_1(u1_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v1_tdlat_3(X0)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_496,c_8])).

cnf(c_501,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_500])).

cnf(c_12,plain,
    ( ~ v2_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_520,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_501,c_12])).

cnf(c_29,negated_conjecture,
    ( v2_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_541,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_520,c_29])).

cnf(c_542,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_541])).

cnf(c_546,plain,
    ( v1_zfmisc_1(u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK3)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_542,c_31,c_28])).

cnf(c_547,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0)) ),
    inference(renaming,[status(thm)],[c_546])).

cnf(c_21,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tdlat_3(sK2(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_724,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tdlat_3(sK2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_30])).

cnf(c_725,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_tdlat_3(sK2(sK3,X0))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_724])).

cnf(c_729,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_tdlat_3(sK2(sK3,X0))
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_725,c_31,c_28])).

cnf(c_819,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_pre_topc(X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(X1)
    | v1_zfmisc_1(u1_struct_0(X1))
    | v1_xboole_0(X0)
    | sK2(sK3,X0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_547,c_729])).

cnf(c_820,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_pre_topc(sK2(sK3,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK2(sK3,X0))
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_819])).

cnf(c_22,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK2(X1,X0))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_700,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK2(X1,X0))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_30])).

cnf(c_701,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_struct_0(sK2(sK3,X0))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_700])).

cnf(c_705,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_struct_0(sK2(sK3,X0))
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_701,c_31,c_28])).

cnf(c_20,plain,
    ( ~ v2_tex_2(X0,X1)
    | m1_pre_topc(sK2(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_748,plain,
    ( ~ v2_tex_2(X0,X1)
    | m1_pre_topc(sK2(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_30])).

cnf(c_749,plain,
    ( ~ v2_tex_2(X0,sK3)
    | m1_pre_topc(sK2(sK3,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_748])).

cnf(c_753,plain,
    ( ~ v2_tex_2(X0,sK3)
    | m1_pre_topc(sK2(sK3,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_749,c_31,c_28])).

cnf(c_824,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_tex_2(X0,sK3)
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_820,c_705,c_753])).

cnf(c_825,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_824])).

cnf(c_2290,plain,
    ( v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0))) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_825])).

cnf(c_2626,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2300,c_2290])).

cnf(c_2627,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
    | v1_xboole_0(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2626])).

cnf(c_2654,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1738])).

cnf(c_1739,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2636,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_1739])).

cnf(c_2827,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2636])).

cnf(c_3027,plain,
    ( u1_struct_0(sK2(sK3,sK4)) != sK4
    | sK4 = u1_struct_0(sK2(sK3,sK4))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2827])).

cnf(c_1747,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_zfmisc_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2764,plain,
    ( v1_zfmisc_1(X0)
    | ~ v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
    | X0 != u1_struct_0(sK2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1747])).

cnf(c_3536,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
    | v1_zfmisc_1(sK4)
    | sK4 != u1_struct_0(sK2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2764])).

cnf(c_4379,plain,
    ( k1_tarski(sK0(sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4179,c_36,c_39,c_658,c_2626,c_2654,c_2931,c_3027,c_3537])).

cnf(c_5216,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = sK4
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5213,c_4379])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2533,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2633,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2533])).

cnf(c_2634,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2633])).

cnf(c_5560,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5216,c_36,c_37,c_2634])).

cnf(c_23,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_682,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_683,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_682])).

cnf(c_687,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_683,c_31,c_28])).

cnf(c_2294,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_687])).

cnf(c_5563,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top
    | m1_subset_1(sK0(sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5560,c_2294])).

cnf(c_2920,plain,
    ( v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) = iProver_top
    | v2_tex_2(sK4,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2626,c_36])).

cnf(c_2921,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) = iProver_top ),
    inference(renaming,[status(thm)],[c_2920])).

cnf(c_4180,plain,
    ( k1_tarski(sK0(u1_struct_0(sK2(sK3,sK4)))) = u1_struct_0(sK2(sK3,sK4))
    | v2_tex_2(sK4,sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2921,c_2296])).

cnf(c_24,negated_conjecture,
    ( ~ v2_tex_2(sK4,sK3)
    | ~ v1_zfmisc_1(sK4) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_39,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v1_zfmisc_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3537,plain,
    ( sK4 != u1_struct_0(sK2(sK3,sK4))
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) != iProver_top
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3536])).

cnf(c_4479,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4180,c_36,c_39,c_2626,c_2654,c_2931,c_3027,c_3537])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5563,c_4479,c_3782,c_3145,c_2957,c_2603,c_2592,c_2583,c_2526,c_37,c_26,c_36,c_27,c_35,c_28,c_32,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:14:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.08/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/0.99  
% 3.08/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.08/0.99  
% 3.08/0.99  ------  iProver source info
% 3.08/0.99  
% 3.08/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.08/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.08/0.99  git: non_committed_changes: false
% 3.08/0.99  git: last_make_outside_of_git: false
% 3.08/0.99  
% 3.08/0.99  ------ 
% 3.08/0.99  
% 3.08/0.99  ------ Input Options
% 3.08/0.99  
% 3.08/0.99  --out_options                           all
% 3.08/0.99  --tptp_safe_out                         true
% 3.08/0.99  --problem_path                          ""
% 3.08/0.99  --include_path                          ""
% 3.08/0.99  --clausifier                            res/vclausify_rel
% 3.08/0.99  --clausifier_options                    --mode clausify
% 3.08/0.99  --stdin                                 false
% 3.08/0.99  --stats_out                             all
% 3.08/0.99  
% 3.08/0.99  ------ General Options
% 3.08/0.99  
% 3.08/0.99  --fof                                   false
% 3.08/0.99  --time_out_real                         305.
% 3.08/0.99  --time_out_virtual                      -1.
% 3.08/0.99  --symbol_type_check                     false
% 3.08/0.99  --clausify_out                          false
% 3.08/0.99  --sig_cnt_out                           false
% 3.08/0.99  --trig_cnt_out                          false
% 3.08/0.99  --trig_cnt_out_tolerance                1.
% 3.08/0.99  --trig_cnt_out_sk_spl                   false
% 3.08/0.99  --abstr_cl_out                          false
% 3.08/0.99  
% 3.08/0.99  ------ Global Options
% 3.08/0.99  
% 3.08/0.99  --schedule                              default
% 3.08/0.99  --add_important_lit                     false
% 3.08/0.99  --prop_solver_per_cl                    1000
% 3.08/0.99  --min_unsat_core                        false
% 3.08/0.99  --soft_assumptions                      false
% 3.08/0.99  --soft_lemma_size                       3
% 3.08/0.99  --prop_impl_unit_size                   0
% 3.08/0.99  --prop_impl_unit                        []
% 3.08/0.99  --share_sel_clauses                     true
% 3.08/0.99  --reset_solvers                         false
% 3.08/0.99  --bc_imp_inh                            [conj_cone]
% 3.08/0.99  --conj_cone_tolerance                   3.
% 3.08/0.99  --extra_neg_conj                        none
% 3.08/0.99  --large_theory_mode                     true
% 3.08/0.99  --prolific_symb_bound                   200
% 3.08/0.99  --lt_threshold                          2000
% 3.08/0.99  --clause_weak_htbl                      true
% 3.08/0.99  --gc_record_bc_elim                     false
% 3.08/0.99  
% 3.08/0.99  ------ Preprocessing Options
% 3.08/0.99  
% 3.08/0.99  --preprocessing_flag                    true
% 3.08/0.99  --time_out_prep_mult                    0.1
% 3.08/0.99  --splitting_mode                        input
% 3.08/0.99  --splitting_grd                         true
% 3.08/0.99  --splitting_cvd                         false
% 3.08/0.99  --splitting_cvd_svl                     false
% 3.08/0.99  --splitting_nvd                         32
% 3.08/0.99  --sub_typing                            true
% 3.08/0.99  --prep_gs_sim                           true
% 3.08/0.99  --prep_unflatten                        true
% 3.08/0.99  --prep_res_sim                          true
% 3.08/0.99  --prep_upred                            true
% 3.08/0.99  --prep_sem_filter                       exhaustive
% 3.08/0.99  --prep_sem_filter_out                   false
% 3.08/0.99  --pred_elim                             true
% 3.08/0.99  --res_sim_input                         true
% 3.08/0.99  --eq_ax_congr_red                       true
% 3.08/0.99  --pure_diseq_elim                       true
% 3.08/0.99  --brand_transform                       false
% 3.08/0.99  --non_eq_to_eq                          false
% 3.08/0.99  --prep_def_merge                        true
% 3.08/0.99  --prep_def_merge_prop_impl              false
% 3.30/0.99  --prep_def_merge_mbd                    true
% 3.30/0.99  --prep_def_merge_tr_red                 false
% 3.30/0.99  --prep_def_merge_tr_cl                  false
% 3.30/0.99  --smt_preprocessing                     true
% 3.30/0.99  --smt_ac_axioms                         fast
% 3.30/0.99  --preprocessed_out                      false
% 3.30/0.99  --preprocessed_stats                    false
% 3.30/0.99  
% 3.30/0.99  ------ Abstraction refinement Options
% 3.30/0.99  
% 3.30/0.99  --abstr_ref                             []
% 3.30/0.99  --abstr_ref_prep                        false
% 3.30/0.99  --abstr_ref_until_sat                   false
% 3.30/0.99  --abstr_ref_sig_restrict                funpre
% 3.30/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.30/0.99  --abstr_ref_under                       []
% 3.30/0.99  
% 3.30/0.99  ------ SAT Options
% 3.30/0.99  
% 3.30/0.99  --sat_mode                              false
% 3.30/0.99  --sat_fm_restart_options                ""
% 3.30/0.99  --sat_gr_def                            false
% 3.30/0.99  --sat_epr_types                         true
% 3.30/0.99  --sat_non_cyclic_types                  false
% 3.30/0.99  --sat_finite_models                     false
% 3.30/0.99  --sat_fm_lemmas                         false
% 3.30/0.99  --sat_fm_prep                           false
% 3.30/0.99  --sat_fm_uc_incr                        true
% 3.30/0.99  --sat_out_model                         small
% 3.30/0.99  --sat_out_clauses                       false
% 3.30/0.99  
% 3.30/0.99  ------ QBF Options
% 3.30/0.99  
% 3.30/0.99  --qbf_mode                              false
% 3.30/0.99  --qbf_elim_univ                         false
% 3.30/0.99  --qbf_dom_inst                          none
% 3.30/0.99  --qbf_dom_pre_inst                      false
% 3.30/0.99  --qbf_sk_in                             false
% 3.30/0.99  --qbf_pred_elim                         true
% 3.30/0.99  --qbf_split                             512
% 3.30/0.99  
% 3.30/0.99  ------ BMC1 Options
% 3.30/0.99  
% 3.30/0.99  --bmc1_incremental                      false
% 3.30/0.99  --bmc1_axioms                           reachable_all
% 3.30/0.99  --bmc1_min_bound                        0
% 3.30/0.99  --bmc1_max_bound                        -1
% 3.30/0.99  --bmc1_max_bound_default                -1
% 3.30/0.99  --bmc1_symbol_reachability              true
% 3.30/0.99  --bmc1_property_lemmas                  false
% 3.30/0.99  --bmc1_k_induction                      false
% 3.30/0.99  --bmc1_non_equiv_states                 false
% 3.30/0.99  --bmc1_deadlock                         false
% 3.30/0.99  --bmc1_ucm                              false
% 3.30/0.99  --bmc1_add_unsat_core                   none
% 3.30/0.99  --bmc1_unsat_core_children              false
% 3.30/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.30/0.99  --bmc1_out_stat                         full
% 3.30/0.99  --bmc1_ground_init                      false
% 3.30/0.99  --bmc1_pre_inst_next_state              false
% 3.30/0.99  --bmc1_pre_inst_state                   false
% 3.30/0.99  --bmc1_pre_inst_reach_state             false
% 3.30/0.99  --bmc1_out_unsat_core                   false
% 3.30/0.99  --bmc1_aig_witness_out                  false
% 3.30/0.99  --bmc1_verbose                          false
% 3.30/0.99  --bmc1_dump_clauses_tptp                false
% 3.30/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.30/0.99  --bmc1_dump_file                        -
% 3.30/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.30/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.30/0.99  --bmc1_ucm_extend_mode                  1
% 3.30/0.99  --bmc1_ucm_init_mode                    2
% 3.30/0.99  --bmc1_ucm_cone_mode                    none
% 3.30/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.30/0.99  --bmc1_ucm_relax_model                  4
% 3.30/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.30/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.30/0.99  --bmc1_ucm_layered_model                none
% 3.30/0.99  --bmc1_ucm_max_lemma_size               10
% 3.30/0.99  
% 3.30/0.99  ------ AIG Options
% 3.30/0.99  
% 3.30/0.99  --aig_mode                              false
% 3.30/0.99  
% 3.30/0.99  ------ Instantiation Options
% 3.30/0.99  
% 3.30/0.99  --instantiation_flag                    true
% 3.30/0.99  --inst_sos_flag                         false
% 3.30/0.99  --inst_sos_phase                        true
% 3.30/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.30/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.30/0.99  --inst_lit_sel_side                     num_symb
% 3.30/0.99  --inst_solver_per_active                1400
% 3.30/0.99  --inst_solver_calls_frac                1.
% 3.30/0.99  --inst_passive_queue_type               priority_queues
% 3.30/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.30/0.99  --inst_passive_queues_freq              [25;2]
% 3.30/0.99  --inst_dismatching                      true
% 3.30/0.99  --inst_eager_unprocessed_to_passive     true
% 3.30/0.99  --inst_prop_sim_given                   true
% 3.30/0.99  --inst_prop_sim_new                     false
% 3.30/0.99  --inst_subs_new                         false
% 3.30/0.99  --inst_eq_res_simp                      false
% 3.30/0.99  --inst_subs_given                       false
% 3.30/0.99  --inst_orphan_elimination               true
% 3.30/0.99  --inst_learning_loop_flag               true
% 3.30/0.99  --inst_learning_start                   3000
% 3.30/0.99  --inst_learning_factor                  2
% 3.30/0.99  --inst_start_prop_sim_after_learn       3
% 3.30/0.99  --inst_sel_renew                        solver
% 3.30/0.99  --inst_lit_activity_flag                true
% 3.30/0.99  --inst_restr_to_given                   false
% 3.30/0.99  --inst_activity_threshold               500
% 3.30/0.99  --inst_out_proof                        true
% 3.30/0.99  
% 3.30/0.99  ------ Resolution Options
% 3.30/0.99  
% 3.30/0.99  --resolution_flag                       true
% 3.30/0.99  --res_lit_sel                           adaptive
% 3.30/0.99  --res_lit_sel_side                      none
% 3.30/0.99  --res_ordering                          kbo
% 3.30/0.99  --res_to_prop_solver                    active
% 3.30/0.99  --res_prop_simpl_new                    false
% 3.30/0.99  --res_prop_simpl_given                  true
% 3.30/0.99  --res_passive_queue_type                priority_queues
% 3.30/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.30/0.99  --res_passive_queues_freq               [15;5]
% 3.30/0.99  --res_forward_subs                      full
% 3.30/0.99  --res_backward_subs                     full
% 3.30/0.99  --res_forward_subs_resolution           true
% 3.30/0.99  --res_backward_subs_resolution          true
% 3.30/0.99  --res_orphan_elimination                true
% 3.30/0.99  --res_time_limit                        2.
% 3.30/0.99  --res_out_proof                         true
% 3.30/0.99  
% 3.30/0.99  ------ Superposition Options
% 3.30/0.99  
% 3.30/0.99  --superposition_flag                    true
% 3.30/0.99  --sup_passive_queue_type                priority_queues
% 3.30/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.30/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.30/0.99  --demod_completeness_check              fast
% 3.30/0.99  --demod_use_ground                      true
% 3.30/0.99  --sup_to_prop_solver                    passive
% 3.30/0.99  --sup_prop_simpl_new                    true
% 3.30/0.99  --sup_prop_simpl_given                  true
% 3.30/0.99  --sup_fun_splitting                     false
% 3.30/0.99  --sup_smt_interval                      50000
% 3.30/0.99  
% 3.30/0.99  ------ Superposition Simplification Setup
% 3.30/0.99  
% 3.30/0.99  --sup_indices_passive                   []
% 3.30/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.30/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.30/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.30/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.30/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.30/0.99  --sup_full_bw                           [BwDemod]
% 3.30/0.99  --sup_immed_triv                        [TrivRules]
% 3.30/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.30/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.30/0.99  --sup_immed_bw_main                     []
% 3.30/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.30/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.30/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.30/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.30/0.99  
% 3.30/0.99  ------ Combination Options
% 3.30/0.99  
% 3.30/0.99  --comb_res_mult                         3
% 3.30/0.99  --comb_sup_mult                         2
% 3.30/0.99  --comb_inst_mult                        10
% 3.30/0.99  
% 3.30/0.99  ------ Debug Options
% 3.30/0.99  
% 3.30/0.99  --dbg_backtrace                         false
% 3.30/0.99  --dbg_dump_prop_clauses                 false
% 3.30/0.99  --dbg_dump_prop_clauses_file            -
% 3.30/0.99  --dbg_out_stat                          false
% 3.30/0.99  ------ Parsing...
% 3.30/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.30/0.99  
% 3.30/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.30/0.99  
% 3.30/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.30/0.99  
% 3.30/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.30/0.99  ------ Proving...
% 3.30/0.99  ------ Problem Properties 
% 3.30/0.99  
% 3.30/0.99  
% 3.30/0.99  clauses                                 21
% 3.30/0.99  conjectures                             6
% 3.30/0.99  EPR                                     6
% 3.30/0.99  Horn                                    10
% 3.30/0.99  unary                                   5
% 3.30/0.99  binary                                  4
% 3.30/0.99  lits                                    62
% 3.30/0.99  lits eq                                 4
% 3.30/0.99  fd_pure                                 0
% 3.30/0.99  fd_pseudo                               0
% 3.30/0.99  fd_cond                                 0
% 3.30/0.99  fd_pseudo_cond                          0
% 3.30/0.99  AC symbols                              0
% 3.30/0.99  
% 3.30/0.99  ------ Schedule dynamic 5 is on 
% 3.30/0.99  
% 3.30/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.30/0.99  
% 3.30/0.99  
% 3.30/0.99  ------ 
% 3.30/0.99  Current options:
% 3.30/0.99  ------ 
% 3.30/0.99  
% 3.30/0.99  ------ Input Options
% 3.30/0.99  
% 3.30/0.99  --out_options                           all
% 3.30/0.99  --tptp_safe_out                         true
% 3.30/0.99  --problem_path                          ""
% 3.30/0.99  --include_path                          ""
% 3.30/0.99  --clausifier                            res/vclausify_rel
% 3.30/0.99  --clausifier_options                    --mode clausify
% 3.30/0.99  --stdin                                 false
% 3.30/0.99  --stats_out                             all
% 3.30/0.99  
% 3.30/0.99  ------ General Options
% 3.30/0.99  
% 3.30/0.99  --fof                                   false
% 3.30/0.99  --time_out_real                         305.
% 3.30/0.99  --time_out_virtual                      -1.
% 3.30/0.99  --symbol_type_check                     false
% 3.30/0.99  --clausify_out                          false
% 3.30/0.99  --sig_cnt_out                           false
% 3.30/0.99  --trig_cnt_out                          false
% 3.30/0.99  --trig_cnt_out_tolerance                1.
% 3.30/0.99  --trig_cnt_out_sk_spl                   false
% 3.30/0.99  --abstr_cl_out                          false
% 3.30/0.99  
% 3.30/0.99  ------ Global Options
% 3.30/0.99  
% 3.30/0.99  --schedule                              default
% 3.30/0.99  --add_important_lit                     false
% 3.30/0.99  --prop_solver_per_cl                    1000
% 3.30/0.99  --min_unsat_core                        false
% 3.30/0.99  --soft_assumptions                      false
% 3.30/0.99  --soft_lemma_size                       3
% 3.30/0.99  --prop_impl_unit_size                   0
% 3.30/0.99  --prop_impl_unit                        []
% 3.30/0.99  --share_sel_clauses                     true
% 3.30/0.99  --reset_solvers                         false
% 3.30/0.99  --bc_imp_inh                            [conj_cone]
% 3.30/0.99  --conj_cone_tolerance                   3.
% 3.30/0.99  --extra_neg_conj                        none
% 3.30/0.99  --large_theory_mode                     true
% 3.30/0.99  --prolific_symb_bound                   200
% 3.30/0.99  --lt_threshold                          2000
% 3.30/0.99  --clause_weak_htbl                      true
% 3.30/0.99  --gc_record_bc_elim                     false
% 3.30/0.99  
% 3.30/0.99  ------ Preprocessing Options
% 3.30/0.99  
% 3.30/0.99  --preprocessing_flag                    true
% 3.30/0.99  --time_out_prep_mult                    0.1
% 3.30/0.99  --splitting_mode                        input
% 3.30/0.99  --splitting_grd                         true
% 3.30/0.99  --splitting_cvd                         false
% 3.30/0.99  --splitting_cvd_svl                     false
% 3.30/0.99  --splitting_nvd                         32
% 3.30/0.99  --sub_typing                            true
% 3.30/0.99  --prep_gs_sim                           true
% 3.30/0.99  --prep_unflatten                        true
% 3.30/0.99  --prep_res_sim                          true
% 3.30/0.99  --prep_upred                            true
% 3.30/0.99  --prep_sem_filter                       exhaustive
% 3.30/0.99  --prep_sem_filter_out                   false
% 3.30/0.99  --pred_elim                             true
% 3.30/0.99  --res_sim_input                         true
% 3.30/0.99  --eq_ax_congr_red                       true
% 3.30/0.99  --pure_diseq_elim                       true
% 3.30/0.99  --brand_transform                       false
% 3.30/0.99  --non_eq_to_eq                          false
% 3.30/0.99  --prep_def_merge                        true
% 3.30/0.99  --prep_def_merge_prop_impl              false
% 3.30/0.99  --prep_def_merge_mbd                    true
% 3.30/0.99  --prep_def_merge_tr_red                 false
% 3.30/0.99  --prep_def_merge_tr_cl                  false
% 3.30/0.99  --smt_preprocessing                     true
% 3.30/0.99  --smt_ac_axioms                         fast
% 3.30/0.99  --preprocessed_out                      false
% 3.30/0.99  --preprocessed_stats                    false
% 3.30/0.99  
% 3.30/0.99  ------ Abstraction refinement Options
% 3.30/0.99  
% 3.30/0.99  --abstr_ref                             []
% 3.30/0.99  --abstr_ref_prep                        false
% 3.30/0.99  --abstr_ref_until_sat                   false
% 3.30/0.99  --abstr_ref_sig_restrict                funpre
% 3.30/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.30/0.99  --abstr_ref_under                       []
% 3.30/0.99  
% 3.30/0.99  ------ SAT Options
% 3.30/0.99  
% 3.30/0.99  --sat_mode                              false
% 3.30/0.99  --sat_fm_restart_options                ""
% 3.30/0.99  --sat_gr_def                            false
% 3.30/0.99  --sat_epr_types                         true
% 3.30/0.99  --sat_non_cyclic_types                  false
% 3.30/0.99  --sat_finite_models                     false
% 3.30/0.99  --sat_fm_lemmas                         false
% 3.30/0.99  --sat_fm_prep                           false
% 3.30/0.99  --sat_fm_uc_incr                        true
% 3.30/0.99  --sat_out_model                         small
% 3.30/0.99  --sat_out_clauses                       false
% 3.30/0.99  
% 3.30/0.99  ------ QBF Options
% 3.30/0.99  
% 3.30/0.99  --qbf_mode                              false
% 3.30/0.99  --qbf_elim_univ                         false
% 3.30/0.99  --qbf_dom_inst                          none
% 3.30/0.99  --qbf_dom_pre_inst                      false
% 3.30/0.99  --qbf_sk_in                             false
% 3.30/0.99  --qbf_pred_elim                         true
% 3.30/0.99  --qbf_split                             512
% 3.30/0.99  
% 3.30/0.99  ------ BMC1 Options
% 3.30/0.99  
% 3.30/0.99  --bmc1_incremental                      false
% 3.30/0.99  --bmc1_axioms                           reachable_all
% 3.30/0.99  --bmc1_min_bound                        0
% 3.30/0.99  --bmc1_max_bound                        -1
% 3.30/0.99  --bmc1_max_bound_default                -1
% 3.30/0.99  --bmc1_symbol_reachability              true
% 3.30/0.99  --bmc1_property_lemmas                  false
% 3.30/0.99  --bmc1_k_induction                      false
% 3.30/0.99  --bmc1_non_equiv_states                 false
% 3.30/0.99  --bmc1_deadlock                         false
% 3.30/0.99  --bmc1_ucm                              false
% 3.30/0.99  --bmc1_add_unsat_core                   none
% 3.30/0.99  --bmc1_unsat_core_children              false
% 3.30/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.30/0.99  --bmc1_out_stat                         full
% 3.30/0.99  --bmc1_ground_init                      false
% 3.30/0.99  --bmc1_pre_inst_next_state              false
% 3.30/0.99  --bmc1_pre_inst_state                   false
% 3.30/0.99  --bmc1_pre_inst_reach_state             false
% 3.30/0.99  --bmc1_out_unsat_core                   false
% 3.30/0.99  --bmc1_aig_witness_out                  false
% 3.30/0.99  --bmc1_verbose                          false
% 3.30/0.99  --bmc1_dump_clauses_tptp                false
% 3.30/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.30/0.99  --bmc1_dump_file                        -
% 3.30/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.30/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.30/0.99  --bmc1_ucm_extend_mode                  1
% 3.30/0.99  --bmc1_ucm_init_mode                    2
% 3.30/0.99  --bmc1_ucm_cone_mode                    none
% 3.30/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.30/0.99  --bmc1_ucm_relax_model                  4
% 3.30/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.30/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.30/0.99  --bmc1_ucm_layered_model                none
% 3.30/0.99  --bmc1_ucm_max_lemma_size               10
% 3.30/0.99  
% 3.30/0.99  ------ AIG Options
% 3.30/0.99  
% 3.30/0.99  --aig_mode                              false
% 3.30/0.99  
% 3.30/0.99  ------ Instantiation Options
% 3.30/0.99  
% 3.30/0.99  --instantiation_flag                    true
% 3.30/0.99  --inst_sos_flag                         false
% 3.30/0.99  --inst_sos_phase                        true
% 3.30/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.30/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.30/0.99  --inst_lit_sel_side                     none
% 3.30/0.99  --inst_solver_per_active                1400
% 3.30/0.99  --inst_solver_calls_frac                1.
% 3.30/0.99  --inst_passive_queue_type               priority_queues
% 3.30/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.30/0.99  --inst_passive_queues_freq              [25;2]
% 3.30/0.99  --inst_dismatching                      true
% 3.30/0.99  --inst_eager_unprocessed_to_passive     true
% 3.30/0.99  --inst_prop_sim_given                   true
% 3.30/0.99  --inst_prop_sim_new                     false
% 3.30/0.99  --inst_subs_new                         false
% 3.30/0.99  --inst_eq_res_simp                      false
% 3.30/0.99  --inst_subs_given                       false
% 3.30/0.99  --inst_orphan_elimination               true
% 3.30/0.99  --inst_learning_loop_flag               true
% 3.30/0.99  --inst_learning_start                   3000
% 3.30/0.99  --inst_learning_factor                  2
% 3.30/0.99  --inst_start_prop_sim_after_learn       3
% 3.30/0.99  --inst_sel_renew                        solver
% 3.30/0.99  --inst_lit_activity_flag                true
% 3.30/0.99  --inst_restr_to_given                   false
% 3.30/0.99  --inst_activity_threshold               500
% 3.30/0.99  --inst_out_proof                        true
% 3.30/0.99  
% 3.30/0.99  ------ Resolution Options
% 3.30/0.99  
% 3.30/0.99  --resolution_flag                       false
% 3.30/0.99  --res_lit_sel                           adaptive
% 3.30/0.99  --res_lit_sel_side                      none
% 3.30/0.99  --res_ordering                          kbo
% 3.30/0.99  --res_to_prop_solver                    active
% 3.30/0.99  --res_prop_simpl_new                    false
% 3.30/0.99  --res_prop_simpl_given                  true
% 3.30/0.99  --res_passive_queue_type                priority_queues
% 3.30/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.30/0.99  --res_passive_queues_freq               [15;5]
% 3.30/0.99  --res_forward_subs                      full
% 3.30/0.99  --res_backward_subs                     full
% 3.30/0.99  --res_forward_subs_resolution           true
% 3.30/0.99  --res_backward_subs_resolution          true
% 3.30/0.99  --res_orphan_elimination                true
% 3.30/0.99  --res_time_limit                        2.
% 3.30/0.99  --res_out_proof                         true
% 3.30/0.99  
% 3.30/0.99  ------ Superposition Options
% 3.30/0.99  
% 3.30/0.99  --superposition_flag                    true
% 3.30/0.99  --sup_passive_queue_type                priority_queues
% 3.30/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.30/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.30/0.99  --demod_completeness_check              fast
% 3.30/0.99  --demod_use_ground                      true
% 3.30/0.99  --sup_to_prop_solver                    passive
% 3.30/0.99  --sup_prop_simpl_new                    true
% 3.30/0.99  --sup_prop_simpl_given                  true
% 3.30/0.99  --sup_fun_splitting                     false
% 3.30/0.99  --sup_smt_interval                      50000
% 3.30/0.99  
% 3.30/0.99  ------ Superposition Simplification Setup
% 3.30/0.99  
% 3.30/0.99  --sup_indices_passive                   []
% 3.30/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.30/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.30/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.30/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.30/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.30/0.99  --sup_full_bw                           [BwDemod]
% 3.30/0.99  --sup_immed_triv                        [TrivRules]
% 3.30/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.30/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.30/0.99  --sup_immed_bw_main                     []
% 3.30/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.30/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.30/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.30/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.30/0.99  
% 3.30/0.99  ------ Combination Options
% 3.30/0.99  
% 3.30/0.99  --comb_res_mult                         3
% 3.30/0.99  --comb_sup_mult                         2
% 3.30/0.99  --comb_inst_mult                        10
% 3.30/0.99  
% 3.30/0.99  ------ Debug Options
% 3.30/0.99  
% 3.30/0.99  --dbg_backtrace                         false
% 3.30/0.99  --dbg_dump_prop_clauses                 false
% 3.30/0.99  --dbg_dump_prop_clauses_file            -
% 3.30/0.99  --dbg_out_stat                          false
% 3.30/0.99  
% 3.30/0.99  
% 3.30/0.99  
% 3.30/0.99  
% 3.30/0.99  ------ Proving...
% 3.30/0.99  
% 3.30/0.99  
% 3.30/0.99  % SZS status Theorem for theBenchmark.p
% 3.30/0.99  
% 3.30/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.30/0.99  
% 3.30/0.99  fof(f17,conjecture,(
% 3.30/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 3.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f18,negated_conjecture,(
% 3.30/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 3.30/0.99    inference(negated_conjecture,[],[f17])).
% 3.30/0.99  
% 3.30/0.99  fof(f43,plain,(
% 3.30/0.99    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.30/0.99    inference(ennf_transformation,[],[f18])).
% 3.30/0.99  
% 3.30/0.99  fof(f44,plain,(
% 3.30/0.99    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.30/0.99    inference(flattening,[],[f43])).
% 3.30/0.99  
% 3.30/0.99  fof(f54,plain,(
% 3.30/0.99    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.30/0.99    inference(nnf_transformation,[],[f44])).
% 3.30/0.99  
% 3.30/0.99  fof(f55,plain,(
% 3.30/0.99    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.30/0.99    inference(flattening,[],[f54])).
% 3.30/0.99  
% 3.30/0.99  fof(f57,plain,(
% 3.30/0.99    ( ! [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,X0)) & (v1_zfmisc_1(sK4) | v2_tex_2(sK4,X0)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK4))) )),
% 3.30/0.99    introduced(choice_axiom,[])).
% 3.30/0.99  
% 3.30/0.99  fof(f56,plain,(
% 3.30/0.99    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK3)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 3.30/0.99    introduced(choice_axiom,[])).
% 3.30/0.99  
% 3.30/0.99  fof(f58,plain,(
% 3.30/0.99    ((~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3)) & (v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 3.30/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f55,f57,f56])).
% 3.30/0.99  
% 3.30/0.99  fof(f88,plain,(
% 3.30/0.99    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 3.30/0.99    inference(cnf_transformation,[],[f58])).
% 3.30/0.99  
% 3.30/0.99  fof(f13,axiom,(
% 3.30/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 3.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f20,plain,(
% 3.30/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2))))),
% 3.30/0.99    inference(pure_predicate_removal,[],[f13])).
% 3.30/0.99  
% 3.30/0.99  fof(f35,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.30/0.99    inference(ennf_transformation,[],[f20])).
% 3.30/0.99  
% 3.30/0.99  fof(f36,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.30/0.99    inference(flattening,[],[f35])).
% 3.30/0.99  
% 3.30/0.99  fof(f50,plain,(
% 3.30/0.99    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(sK1(X0,X1)) = X1 & m1_pre_topc(sK1(X0,X1),X0) & ~v2_struct_0(sK1(X0,X1))))),
% 3.30/0.99    introduced(choice_axiom,[])).
% 3.30/0.99  
% 3.30/0.99  fof(f51,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : ((u1_struct_0(sK1(X0,X1)) = X1 & m1_pre_topc(sK1(X0,X1),X0) & ~v2_struct_0(sK1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.30/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f50])).
% 3.30/0.99  
% 3.30/0.99  fof(f75,plain,(
% 3.30/0.99    ( ! [X0,X1] : (m1_pre_topc(sK1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f51])).
% 3.30/0.99  
% 3.30/0.99  fof(f83,plain,(
% 3.30/0.99    ~v2_struct_0(sK3)),
% 3.30/0.99    inference(cnf_transformation,[],[f58])).
% 3.30/0.99  
% 3.30/0.99  fof(f86,plain,(
% 3.30/0.99    l1_pre_topc(sK3)),
% 3.30/0.99    inference(cnf_transformation,[],[f58])).
% 3.30/0.99  
% 3.30/0.99  fof(f87,plain,(
% 3.30/0.99    ~v1_xboole_0(sK4)),
% 3.30/0.99    inference(cnf_transformation,[],[f58])).
% 3.30/0.99  
% 3.30/0.99  fof(f76,plain,(
% 3.30/0.99    ( ! [X0,X1] : (u1_struct_0(sK1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f51])).
% 3.30/0.99  
% 3.30/0.99  fof(f1,axiom,(
% 3.30/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f45,plain,(
% 3.30/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.30/0.99    inference(nnf_transformation,[],[f1])).
% 3.30/0.99  
% 3.30/0.99  fof(f46,plain,(
% 3.30/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.30/0.99    inference(rectify,[],[f45])).
% 3.30/0.99  
% 3.30/0.99  fof(f47,plain,(
% 3.30/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.30/0.99    introduced(choice_axiom,[])).
% 3.30/0.99  
% 3.30/0.99  fof(f48,plain,(
% 3.30/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.30/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f46,f47])).
% 3.30/0.99  
% 3.30/0.99  fof(f60,plain,(
% 3.30/0.99    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f48])).
% 3.30/0.99  
% 3.30/0.99  fof(f5,axiom,(
% 3.30/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f22,plain,(
% 3.30/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.30/0.99    inference(ennf_transformation,[],[f5])).
% 3.30/0.99  
% 3.30/0.99  fof(f65,plain,(
% 3.30/0.99    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f22])).
% 3.30/0.99  
% 3.30/0.99  fof(f9,axiom,(
% 3.30/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 3.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f27,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.30/0.99    inference(ennf_transformation,[],[f9])).
% 3.30/0.99  
% 3.30/0.99  fof(f28,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.30/0.99    inference(flattening,[],[f27])).
% 3.30/0.99  
% 3.30/0.99  fof(f69,plain,(
% 3.30/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f28])).
% 3.30/0.99  
% 3.30/0.99  fof(f74,plain,(
% 3.30/0.99    ( ! [X0,X1] : (~v2_struct_0(sK1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f51])).
% 3.30/0.99  
% 3.30/0.99  fof(f10,axiom,(
% 3.30/0.99    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 3.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f29,plain,(
% 3.30/0.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.30/0.99    inference(ennf_transformation,[],[f10])).
% 3.30/0.99  
% 3.30/0.99  fof(f30,plain,(
% 3.30/0.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.30/0.99    inference(flattening,[],[f29])).
% 3.30/0.99  
% 3.30/0.99  fof(f70,plain,(
% 3.30/0.99    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f30])).
% 3.30/0.99  
% 3.30/0.99  fof(f89,plain,(
% 3.30/0.99    v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3)),
% 3.30/0.99    inference(cnf_transformation,[],[f58])).
% 3.30/0.99  
% 3.30/0.99  fof(f15,axiom,(
% 3.30/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 3.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f19,plain,(
% 3.30/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 3.30/0.99    inference(pure_predicate_removal,[],[f15])).
% 3.30/0.99  
% 3.30/0.99  fof(f39,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.30/0.99    inference(ennf_transformation,[],[f19])).
% 3.30/0.99  
% 3.30/0.99  fof(f40,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.30/0.99    inference(flattening,[],[f39])).
% 3.30/0.99  
% 3.30/0.99  fof(f52,plain,(
% 3.30/0.99    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_tdlat_3(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))))),
% 3.30/0.99    introduced(choice_axiom,[])).
% 3.30/0.99  
% 3.30/0.99  fof(f53,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : ((u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_tdlat_3(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.30/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f52])).
% 3.30/0.99  
% 3.30/0.99  fof(f81,plain,(
% 3.30/0.99    ( ! [X0,X1] : (u1_struct_0(sK2(X0,X1)) = X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f53])).
% 3.30/0.99  
% 3.30/0.99  fof(f84,plain,(
% 3.30/0.99    v2_pre_topc(sK3)),
% 3.30/0.99    inference(cnf_transformation,[],[f58])).
% 3.30/0.99  
% 3.30/0.99  fof(f3,axiom,(
% 3.30/0.99    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f49,plain,(
% 3.30/0.99    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 3.30/0.99    inference(nnf_transformation,[],[f3])).
% 3.30/0.99  
% 3.30/0.99  fof(f63,plain,(
% 3.30/0.99    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f49])).
% 3.30/0.99  
% 3.30/0.99  fof(f14,axiom,(
% 3.30/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 3.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f37,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 3.30/0.99    inference(ennf_transformation,[],[f14])).
% 3.30/0.99  
% 3.30/0.99  fof(f38,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.30/0.99    inference(flattening,[],[f37])).
% 3.30/0.99  
% 3.30/0.99  fof(f77,plain,(
% 3.30/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f38])).
% 3.30/0.99  
% 3.30/0.99  fof(f2,axiom,(
% 3.30/0.99    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 3.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f61,plain,(
% 3.30/0.99    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 3.30/0.99    inference(cnf_transformation,[],[f2])).
% 3.30/0.99  
% 3.30/0.99  fof(f59,plain,(
% 3.30/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f48])).
% 3.30/0.99  
% 3.30/0.99  fof(f12,axiom,(
% 3.30/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((~v7_struct_0(X1) & ~v2_struct_0(X1)) => (~v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 3.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f33,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : (((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (v7_struct_0(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.30/0.99    inference(ennf_transformation,[],[f12])).
% 3.30/0.99  
% 3.30/0.99  fof(f34,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : ((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.30/0.99    inference(flattening,[],[f33])).
% 3.30/0.99  
% 3.30/0.99  fof(f73,plain,(
% 3.30/0.99    ( ! [X0,X1] : (~v1_tdlat_3(X1) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f34])).
% 3.30/0.99  
% 3.30/0.99  fof(f6,axiom,(
% 3.30/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f23,plain,(
% 3.30/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.30/0.99    inference(ennf_transformation,[],[f6])).
% 3.30/0.99  
% 3.30/0.99  fof(f66,plain,(
% 3.30/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f23])).
% 3.30/0.99  
% 3.30/0.99  fof(f8,axiom,(
% 3.30/0.99    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 3.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f25,plain,(
% 3.30/0.99    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 3.30/0.99    inference(ennf_transformation,[],[f8])).
% 3.30/0.99  
% 3.30/0.99  fof(f26,plain,(
% 3.30/0.99    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 3.30/0.99    inference(flattening,[],[f25])).
% 3.30/0.99  
% 3.30/0.99  fof(f68,plain,(
% 3.30/0.99    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f26])).
% 3.30/0.99  
% 3.30/0.99  fof(f7,axiom,(
% 3.30/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f24,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.30/0.99    inference(ennf_transformation,[],[f7])).
% 3.30/0.99  
% 3.30/0.99  fof(f67,plain,(
% 3.30/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f24])).
% 3.30/0.99  
% 3.30/0.99  fof(f11,axiom,(
% 3.30/0.99    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 3.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f31,plain,(
% 3.30/0.99    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 3.30/0.99    inference(ennf_transformation,[],[f11])).
% 3.30/0.99  
% 3.30/0.99  fof(f32,plain,(
% 3.30/0.99    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 3.30/0.99    inference(flattening,[],[f31])).
% 3.30/0.99  
% 3.30/0.99  fof(f71,plain,(
% 3.30/0.99    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f32])).
% 3.30/0.99  
% 3.30/0.99  fof(f85,plain,(
% 3.30/0.99    v2_tdlat_3(sK3)),
% 3.30/0.99    inference(cnf_transformation,[],[f58])).
% 3.30/0.99  
% 3.30/0.99  fof(f79,plain,(
% 3.30/0.99    ( ! [X0,X1] : (v1_tdlat_3(sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f53])).
% 3.30/0.99  
% 3.30/0.99  fof(f78,plain,(
% 3.30/0.99    ( ! [X0,X1] : (~v2_struct_0(sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f53])).
% 3.30/0.99  
% 3.30/0.99  fof(f80,plain,(
% 3.30/0.99    ( ! [X0,X1] : (m1_pre_topc(sK2(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f53])).
% 3.30/0.99  
% 3.30/0.99  fof(f4,axiom,(
% 3.30/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f21,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.30/0.99    inference(ennf_transformation,[],[f4])).
% 3.30/0.99  
% 3.30/0.99  fof(f64,plain,(
% 3.30/0.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f21])).
% 3.30/0.99  
% 3.30/0.99  fof(f16,axiom,(
% 3.30/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 3.30/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f41,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.30/0.99    inference(ennf_transformation,[],[f16])).
% 3.30/0.99  
% 3.30/0.99  fof(f42,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.30/0.99    inference(flattening,[],[f41])).
% 3.30/0.99  
% 3.30/0.99  fof(f82,plain,(
% 3.30/0.99    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f42])).
% 3.30/0.99  
% 3.30/0.99  fof(f90,plain,(
% 3.30/0.99    ~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3)),
% 3.30/0.99    inference(cnf_transformation,[],[f58])).
% 3.30/0.99  
% 3.30/0.99  cnf(c_26,negated_conjecture,
% 3.30/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.30/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2300,plain,
% 3.30/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_16,plain,
% 3.30/0.99      ( m1_pre_topc(sK1(X0,X1),X0)
% 3.30/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.30/0.99      | v2_struct_0(X0)
% 3.30/0.99      | ~ l1_pre_topc(X0)
% 3.30/0.99      | v1_xboole_0(X1) ),
% 3.30/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2304,plain,
% 3.30/0.99      ( m1_pre_topc(sK1(X0,X1),X0) = iProver_top
% 3.30/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.30/0.99      | v2_struct_0(X0) = iProver_top
% 3.30/0.99      | l1_pre_topc(X0) != iProver_top
% 3.30/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3113,plain,
% 3.30/0.99      ( m1_pre_topc(sK1(sK3,sK4),sK3) = iProver_top
% 3.30/0.99      | v2_struct_0(sK3) = iProver_top
% 3.30/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.30/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_2300,c_2304]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_31,negated_conjecture,
% 3.30/0.99      ( ~ v2_struct_0(sK3) ),
% 3.30/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_32,plain,
% 3.30/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_28,negated_conjecture,
% 3.30/0.99      ( l1_pre_topc(sK3) ),
% 3.30/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_35,plain,
% 3.30/0.99      ( l1_pre_topc(sK3) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_27,negated_conjecture,
% 3.30/0.99      ( ~ v1_xboole_0(sK4) ),
% 3.30/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_36,plain,
% 3.30/0.99      ( v1_xboole_0(sK4) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_37,plain,
% 3.30/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2600,plain,
% 3.30/0.99      ( m1_pre_topc(sK1(X0,sK4),X0)
% 3.30/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
% 3.30/0.99      | v2_struct_0(X0)
% 3.30/0.99      | ~ l1_pre_topc(X0)
% 3.30/0.99      | v1_xboole_0(sK4) ),
% 3.30/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2601,plain,
% 3.30/0.99      ( m1_pre_topc(sK1(X0,sK4),X0) = iProver_top
% 3.30/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.30/0.99      | v2_struct_0(X0) = iProver_top
% 3.30/0.99      | l1_pre_topc(X0) != iProver_top
% 3.30/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_2600]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2603,plain,
% 3.30/0.99      ( m1_pre_topc(sK1(sK3,sK4),sK3) = iProver_top
% 3.30/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.30/0.99      | v2_struct_0(sK3) = iProver_top
% 3.30/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.30/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.30/0.99      inference(instantiation,[status(thm)],[c_2601]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3366,plain,
% 3.30/0.99      ( m1_pre_topc(sK1(sK3,sK4),sK3) = iProver_top ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_3113,c_32,c_35,c_36,c_37,c_2603]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_15,plain,
% 3.30/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/0.99      | v2_struct_0(X1)
% 3.30/0.99      | ~ l1_pre_topc(X1)
% 3.30/0.99      | v1_xboole_0(X0)
% 3.30/0.99      | u1_struct_0(sK1(X1,X0)) = X0 ),
% 3.30/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2305,plain,
% 3.30/0.99      ( u1_struct_0(sK1(X0,X1)) = X1
% 3.30/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.30/0.99      | v2_struct_0(X0) = iProver_top
% 3.30/0.99      | l1_pre_topc(X0) != iProver_top
% 3.30/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3051,plain,
% 3.30/0.99      ( u1_struct_0(sK1(sK3,sK4)) = sK4
% 3.30/0.99      | v2_struct_0(sK3) = iProver_top
% 3.30/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.30/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_2300,c_2305]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2590,plain,
% 3.30/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
% 3.30/0.99      | v2_struct_0(X0)
% 3.30/0.99      | ~ l1_pre_topc(X0)
% 3.30/0.99      | v1_xboole_0(sK4)
% 3.30/0.99      | u1_struct_0(sK1(X0,sK4)) = sK4 ),
% 3.30/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2592,plain,
% 3.30/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.30/0.99      | v2_struct_0(sK3)
% 3.30/0.99      | ~ l1_pre_topc(sK3)
% 3.30/0.99      | v1_xboole_0(sK4)
% 3.30/0.99      | u1_struct_0(sK1(sK3,sK4)) = sK4 ),
% 3.30/0.99      inference(instantiation,[status(thm)],[c_2590]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3247,plain,
% 3.30/0.99      ( u1_struct_0(sK1(sK3,sK4)) = sK4 ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_3051,c_31,c_28,c_27,c_26,c_2592]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_0,plain,
% 3.30/0.99      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.30/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_6,plain,
% 3.30/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.30/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_475,plain,
% 3.30/0.99      ( m1_subset_1(X0,X1) | v1_xboole_0(X2) | X1 != X2 | sK0(X2) != X0 ),
% 3.30/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_6]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_476,plain,
% 3.30/0.99      ( m1_subset_1(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.30/0.99      inference(unflattening,[status(thm)],[c_475]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2295,plain,
% 3.30/0.99      ( m1_subset_1(sK0(X0),X0) = iProver_top
% 3.30/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_476]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_10,plain,
% 3.30/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.30/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.30/0.99      | m1_subset_1(X2,u1_struct_0(X1))
% 3.30/0.99      | v2_struct_0(X1)
% 3.30/0.99      | v2_struct_0(X0)
% 3.30/0.99      | ~ l1_pre_topc(X1) ),
% 3.30/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2307,plain,
% 3.30/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.30/0.99      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.30/0.99      | m1_subset_1(X2,u1_struct_0(X1)) = iProver_top
% 3.30/0.99      | v2_struct_0(X0) = iProver_top
% 3.30/0.99      | v2_struct_0(X1) = iProver_top
% 3.30/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3554,plain,
% 3.30/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.30/0.99      | m1_subset_1(sK0(u1_struct_0(X0)),u1_struct_0(X1)) = iProver_top
% 3.30/0.99      | v2_struct_0(X0) = iProver_top
% 3.30/0.99      | v2_struct_0(X1) = iProver_top
% 3.30/0.99      | l1_pre_topc(X1) != iProver_top
% 3.30/0.99      | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_2295,c_2307]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_4720,plain,
% 3.30/0.99      ( m1_pre_topc(sK1(sK3,sK4),X0) != iProver_top
% 3.30/0.99      | m1_subset_1(sK0(sK4),u1_struct_0(X0)) = iProver_top
% 3.30/0.99      | v2_struct_0(X0) = iProver_top
% 3.30/0.99      | v2_struct_0(sK1(sK3,sK4)) = iProver_top
% 3.30/0.99      | l1_pre_topc(X0) != iProver_top
% 3.30/0.99      | v1_xboole_0(u1_struct_0(sK1(sK3,sK4))) = iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_3247,c_3554]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_4774,plain,
% 3.30/0.99      ( m1_pre_topc(sK1(sK3,sK4),X0) != iProver_top
% 3.30/0.99      | m1_subset_1(sK0(sK4),u1_struct_0(X0)) = iProver_top
% 3.30/0.99      | v2_struct_0(X0) = iProver_top
% 3.30/0.99      | v2_struct_0(sK1(sK3,sK4)) = iProver_top
% 3.30/0.99      | l1_pre_topc(X0) != iProver_top
% 3.30/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.30/0.99      inference(light_normalisation,[status(thm)],[c_4720,c_3247]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_17,plain,
% 3.30/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/0.99      | v2_struct_0(X1)
% 3.30/0.99      | ~ v2_struct_0(sK1(X1,X0))
% 3.30/0.99      | ~ l1_pre_topc(X1)
% 3.30/0.99      | v1_xboole_0(X0) ),
% 3.30/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2580,plain,
% 3.30/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
% 3.30/0.99      | v2_struct_0(X0)
% 3.30/0.99      | ~ v2_struct_0(sK1(X0,sK4))
% 3.30/0.99      | ~ l1_pre_topc(X0)
% 3.30/0.99      | v1_xboole_0(sK4) ),
% 3.30/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2581,plain,
% 3.30/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.30/0.99      | v2_struct_0(X0) = iProver_top
% 3.30/0.99      | v2_struct_0(sK1(X0,sK4)) != iProver_top
% 3.30/0.99      | l1_pre_topc(X0) != iProver_top
% 3.30/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_2580]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2583,plain,
% 3.30/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.30/0.99      | v2_struct_0(sK1(sK3,sK4)) != iProver_top
% 3.30/0.99      | v2_struct_0(sK3) = iProver_top
% 3.30/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.30/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.30/0.99      inference(instantiation,[status(thm)],[c_2581]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_5194,plain,
% 3.30/0.99      ( l1_pre_topc(X0) != iProver_top
% 3.30/0.99      | m1_pre_topc(sK1(sK3,sK4),X0) != iProver_top
% 3.30/0.99      | m1_subset_1(sK0(sK4),u1_struct_0(X0)) = iProver_top
% 3.30/0.99      | v2_struct_0(X0) = iProver_top ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_4774,c_32,c_35,c_36,c_37,c_2583]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_5195,plain,
% 3.30/0.99      ( m1_pre_topc(sK1(sK3,sK4),X0) != iProver_top
% 3.30/0.99      | m1_subset_1(sK0(sK4),u1_struct_0(X0)) = iProver_top
% 3.30/0.99      | v2_struct_0(X0) = iProver_top
% 3.30/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.30/0.99      inference(renaming,[status(thm)],[c_5194]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_5204,plain,
% 3.30/0.99      ( m1_subset_1(sK0(sK4),u1_struct_0(sK3)) = iProver_top
% 3.30/0.99      | v2_struct_0(sK3) = iProver_top
% 3.30/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_3366,c_5195]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2525,plain,
% 3.30/0.99      ( m1_subset_1(sK0(sK4),sK4) | v1_xboole_0(sK4) ),
% 3.30/0.99      inference(instantiation,[status(thm)],[c_476]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2526,plain,
% 3.30/0.99      ( m1_subset_1(sK0(sK4),sK4) = iProver_top
% 3.30/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_2525]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1738,plain,( X0 = X0 ),theory(equality) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2957,plain,
% 3.30/0.99      ( sK0(sK4) = sK0(sK4) ),
% 3.30/0.99      inference(instantiation,[status(thm)],[c_1738]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1743,plain,
% 3.30/0.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.30/0.99      theory(equality) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2628,plain,
% 3.30/0.99      ( m1_subset_1(X0,X1)
% 3.30/0.99      | ~ m1_subset_1(sK0(sK4),sK4)
% 3.30/0.99      | X0 != sK0(sK4)
% 3.30/0.99      | X1 != sK4 ),
% 3.30/0.99      inference(instantiation,[status(thm)],[c_1743]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2814,plain,
% 3.30/0.99      ( m1_subset_1(X0,u1_struct_0(sK1(X1,sK4)))
% 3.30/0.99      | ~ m1_subset_1(sK0(sK4),sK4)
% 3.30/0.99      | X0 != sK0(sK4)
% 3.30/0.99      | u1_struct_0(sK1(X1,sK4)) != sK4 ),
% 3.30/0.99      inference(instantiation,[status(thm)],[c_2628]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3138,plain,
% 3.30/0.99      ( m1_subset_1(sK0(sK4),u1_struct_0(sK1(X0,sK4)))
% 3.30/0.99      | ~ m1_subset_1(sK0(sK4),sK4)
% 3.30/0.99      | u1_struct_0(sK1(X0,sK4)) != sK4
% 3.30/0.99      | sK0(sK4) != sK0(sK4) ),
% 3.30/0.99      inference(instantiation,[status(thm)],[c_2814]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3143,plain,
% 3.30/0.99      ( u1_struct_0(sK1(X0,sK4)) != sK4
% 3.30/0.99      | sK0(sK4) != sK0(sK4)
% 3.30/0.99      | m1_subset_1(sK0(sK4),u1_struct_0(sK1(X0,sK4))) = iProver_top
% 3.30/0.99      | m1_subset_1(sK0(sK4),sK4) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_3138]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3145,plain,
% 3.30/0.99      ( u1_struct_0(sK1(sK3,sK4)) != sK4
% 3.30/0.99      | sK0(sK4) != sK0(sK4)
% 3.30/0.99      | m1_subset_1(sK0(sK4),u1_struct_0(sK1(sK3,sK4))) = iProver_top
% 3.30/0.99      | m1_subset_1(sK0(sK4),sK4) != iProver_top ),
% 3.30/0.99      inference(instantiation,[status(thm)],[c_3143]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2732,plain,
% 3.30/0.99      ( ~ m1_pre_topc(sK1(X0,sK4),X0)
% 3.30/0.99      | m1_subset_1(X1,u1_struct_0(X0))
% 3.30/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1(X0,sK4)))
% 3.30/0.99      | v2_struct_0(X0)
% 3.30/0.99      | v2_struct_0(sK1(X0,sK4))
% 3.30/0.99      | ~ l1_pre_topc(X0) ),
% 3.30/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3779,plain,
% 3.30/0.99      ( ~ m1_pre_topc(sK1(X0,sK4),X0)
% 3.30/0.99      | m1_subset_1(sK0(sK4),u1_struct_0(X0))
% 3.30/0.99      | ~ m1_subset_1(sK0(sK4),u1_struct_0(sK1(X0,sK4)))
% 3.30/0.99      | v2_struct_0(X0)
% 3.30/0.99      | v2_struct_0(sK1(X0,sK4))
% 3.30/0.99      | ~ l1_pre_topc(X0) ),
% 3.30/0.99      inference(instantiation,[status(thm)],[c_2732]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3780,plain,
% 3.30/0.99      ( m1_pre_topc(sK1(X0,sK4),X0) != iProver_top
% 3.30/0.99      | m1_subset_1(sK0(sK4),u1_struct_0(X0)) = iProver_top
% 3.30/0.99      | m1_subset_1(sK0(sK4),u1_struct_0(sK1(X0,sK4))) != iProver_top
% 3.30/0.99      | v2_struct_0(X0) = iProver_top
% 3.30/0.99      | v2_struct_0(sK1(X0,sK4)) = iProver_top
% 3.30/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_3779]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3782,plain,
% 3.30/0.99      ( m1_pre_topc(sK1(sK3,sK4),sK3) != iProver_top
% 3.30/0.99      | m1_subset_1(sK0(sK4),u1_struct_0(sK1(sK3,sK4))) != iProver_top
% 3.30/0.99      | m1_subset_1(sK0(sK4),u1_struct_0(sK3)) = iProver_top
% 3.30/0.99      | v2_struct_0(sK1(sK3,sK4)) = iProver_top
% 3.30/0.99      | v2_struct_0(sK3) = iProver_top
% 3.30/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.30/0.99      inference(instantiation,[status(thm)],[c_3780]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_5207,plain,
% 3.30/0.99      ( m1_subset_1(sK0(sK4),u1_struct_0(sK3)) = iProver_top ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_5204,c_31,c_32,c_28,c_35,c_27,c_36,c_26,c_37,c_2526,
% 3.30/0.99                 c_2583,c_2592,c_2603,c_2957,c_3145,c_3782]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_11,plain,
% 3.30/0.99      ( ~ m1_subset_1(X0,X1)
% 3.30/0.99      | v1_xboole_0(X1)
% 3.30/0.99      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 3.30/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2306,plain,
% 3.30/0.99      ( k6_domain_1(X0,X1) = k1_tarski(X1)
% 3.30/0.99      | m1_subset_1(X1,X0) != iProver_top
% 3.30/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_5213,plain,
% 3.30/0.99      ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k1_tarski(sK0(sK4))
% 3.30/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_5207,c_2306]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_25,negated_conjecture,
% 3.30/0.99      ( v2_tex_2(sK4,sK3) | v1_zfmisc_1(sK4) ),
% 3.30/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2301,plain,
% 3.30/0.99      ( v2_tex_2(sK4,sK3) = iProver_top
% 3.30/0.99      | v1_zfmisc_1(sK4) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_19,plain,
% 3.30/0.99      ( ~ v2_tex_2(X0,X1)
% 3.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/0.99      | ~ v2_pre_topc(X1)
% 3.30/0.99      | v2_struct_0(X1)
% 3.30/0.99      | ~ l1_pre_topc(X1)
% 3.30/0.99      | v1_xboole_0(X0)
% 3.30/0.99      | u1_struct_0(sK2(X1,X0)) = X0 ),
% 3.30/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_30,negated_conjecture,
% 3.30/0.99      ( v2_pre_topc(sK3) ),
% 3.30/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_772,plain,
% 3.30/0.99      ( ~ v2_tex_2(X0,X1)
% 3.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/0.99      | v2_struct_0(X1)
% 3.30/0.99      | ~ l1_pre_topc(X1)
% 3.30/0.99      | v1_xboole_0(X0)
% 3.30/0.99      | u1_struct_0(sK2(X1,X0)) = X0
% 3.30/0.99      | sK3 != X1 ),
% 3.30/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_773,plain,
% 3.30/0.99      ( ~ v2_tex_2(X0,sK3)
% 3.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.30/0.99      | v2_struct_0(sK3)
% 3.30/0.99      | ~ l1_pre_topc(sK3)
% 3.30/0.99      | v1_xboole_0(X0)
% 3.30/0.99      | u1_struct_0(sK2(sK3,X0)) = X0 ),
% 3.30/0.99      inference(unflattening,[status(thm)],[c_772]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_777,plain,
% 3.30/0.99      ( ~ v2_tex_2(X0,sK3)
% 3.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.30/0.99      | v1_xboole_0(X0)
% 3.30/0.99      | u1_struct_0(sK2(sK3,X0)) = X0 ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_773,c_31,c_28]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2291,plain,
% 3.30/0.99      ( u1_struct_0(sK2(sK3,X0)) = X0
% 3.30/0.99      | v2_tex_2(X0,sK3) != iProver_top
% 3.30/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.30/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_777]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2931,plain,
% 3.30/0.99      ( u1_struct_0(sK2(sK3,sK4)) = sK4
% 3.30/0.99      | v2_tex_2(sK4,sK3) != iProver_top
% 3.30/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_2300,c_2291]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2967,plain,
% 3.30/0.99      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.30/0.99      | u1_struct_0(sK2(sK3,sK4)) = sK4 ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_2931,c_36]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2968,plain,
% 3.30/0.99      ( u1_struct_0(sK2(sK3,sK4)) = sK4
% 3.30/0.99      | v2_tex_2(sK4,sK3) != iProver_top ),
% 3.30/0.99      inference(renaming,[status(thm)],[c_2967]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2973,plain,
% 3.30/0.99      ( u1_struct_0(sK2(sK3,sK4)) = sK4
% 3.30/0.99      | v1_zfmisc_1(sK4) = iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_2301,c_2968]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3,plain,
% 3.30/0.99      ( r1_tarski(k1_tarski(X0),X1) | ~ r2_hidden(X0,X1) ),
% 3.30/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_238,plain,
% 3.30/0.99      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1) ),
% 3.30/0.99      inference(prop_impl,[status(thm)],[c_3]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_239,plain,
% 3.30/0.99      ( r1_tarski(k1_tarski(X0),X1) | ~ r2_hidden(X0,X1) ),
% 3.30/0.99      inference(renaming,[status(thm)],[c_238]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_18,plain,
% 3.30/0.99      ( ~ r1_tarski(X0,X1)
% 3.30/0.99      | ~ v1_zfmisc_1(X1)
% 3.30/0.99      | v1_xboole_0(X0)
% 3.30/0.99      | v1_xboole_0(X1)
% 3.30/0.99      | X1 = X0 ),
% 3.30/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_435,plain,
% 3.30/0.99      ( ~ r2_hidden(X0,X1)
% 3.30/0.99      | ~ v1_zfmisc_1(X2)
% 3.30/0.99      | v1_xboole_0(X3)
% 3.30/0.99      | v1_xboole_0(X2)
% 3.30/0.99      | X2 != X1
% 3.30/0.99      | X2 = X3
% 3.30/0.99      | k1_tarski(X0) != X3 ),
% 3.30/0.99      inference(resolution_lifted,[status(thm)],[c_239,c_18]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_436,plain,
% 3.30/0.99      ( ~ r2_hidden(X0,X1)
% 3.30/0.99      | ~ v1_zfmisc_1(X1)
% 3.30/0.99      | v1_xboole_0(X1)
% 3.30/0.99      | v1_xboole_0(k1_tarski(X0))
% 3.30/0.99      | X1 = k1_tarski(X0) ),
% 3.30/0.99      inference(unflattening,[status(thm)],[c_435]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2,plain,
% 3.30/0.99      ( ~ v1_xboole_0(k1_tarski(X0)) ),
% 3.30/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1,plain,
% 3.30/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.30/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_440,plain,
% 3.30/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_zfmisc_1(X1) | X1 = k1_tarski(X0) ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_436,c_2,c_1]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_460,plain,
% 3.30/0.99      ( ~ v1_zfmisc_1(X0)
% 3.30/0.99      | v1_xboole_0(X1)
% 3.30/0.99      | X0 != X1
% 3.30/0.99      | k1_tarski(X2) = X0
% 3.30/0.99      | sK0(X1) != X2 ),
% 3.30/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_440]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_461,plain,
% 3.30/0.99      ( ~ v1_zfmisc_1(X0) | v1_xboole_0(X0) | k1_tarski(sK0(X0)) = X0 ),
% 3.30/0.99      inference(unflattening,[status(thm)],[c_460]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2296,plain,
% 3.30/0.99      ( k1_tarski(sK0(X0)) = X0
% 3.30/0.99      | v1_zfmisc_1(X0) != iProver_top
% 3.30/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_461]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_4179,plain,
% 3.30/0.99      ( u1_struct_0(sK2(sK3,sK4)) = sK4
% 3.30/0.99      | k1_tarski(sK0(sK4)) = sK4
% 3.30/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_2973,c_2296]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_242,plain,
% 3.30/0.99      ( v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3) ),
% 3.30/0.99      inference(prop_impl,[status(thm)],[c_25]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_243,plain,
% 3.30/0.99      ( v2_tex_2(sK4,sK3) | v1_zfmisc_1(sK4) ),
% 3.30/0.99      inference(renaming,[status(thm)],[c_242]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_656,plain,
% 3.30/0.99      ( v2_tex_2(sK4,sK3)
% 3.30/0.99      | v1_xboole_0(X0)
% 3.30/0.99      | k1_tarski(sK0(X0)) = X0
% 3.30/0.99      | sK4 != X0 ),
% 3.30/0.99      inference(resolution_lifted,[status(thm)],[c_243,c_461]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_657,plain,
% 3.30/0.99      ( v2_tex_2(sK4,sK3)
% 3.30/0.99      | v1_xboole_0(sK4)
% 3.30/0.99      | k1_tarski(sK0(sK4)) = sK4 ),
% 3.30/0.99      inference(unflattening,[status(thm)],[c_656]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_659,plain,
% 3.30/0.99      ( v2_tex_2(sK4,sK3) | k1_tarski(sK0(sK4)) = sK4 ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_657,c_27]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2543,plain,
% 3.30/0.99      ( ~ v1_zfmisc_1(sK4)
% 3.30/0.99      | v1_xboole_0(sK4)
% 3.30/0.99      | k1_tarski(sK0(sK4)) = sK4 ),
% 3.30/0.99      inference(instantiation,[status(thm)],[c_461]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_13,plain,
% 3.30/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.30/0.99      | ~ v1_tdlat_3(X0)
% 3.30/0.99      | ~ v2_tdlat_3(X1)
% 3.30/0.99      | ~ v2_pre_topc(X1)
% 3.30/0.99      | v2_struct_0(X1)
% 3.30/0.99      | v2_struct_0(X0)
% 3.30/0.99      | v7_struct_0(X0)
% 3.30/0.99      | ~ l1_pre_topc(X1) ),
% 3.30/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_7,plain,
% 3.30/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.30/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_9,plain,
% 3.30/0.99      ( ~ v7_struct_0(X0)
% 3.30/0.99      | v1_zfmisc_1(u1_struct_0(X0))
% 3.30/0.99      | ~ l1_struct_0(X0) ),
% 3.30/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_416,plain,
% 3.30/0.99      ( ~ v7_struct_0(X0)
% 3.30/0.99      | v1_zfmisc_1(u1_struct_0(X0))
% 3.30/0.99      | ~ l1_pre_topc(X0) ),
% 3.30/0.99      inference(resolution,[status(thm)],[c_7,c_9]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_496,plain,
% 3.30/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.30/0.99      | ~ v1_tdlat_3(X0)
% 3.30/0.99      | ~ v2_tdlat_3(X1)
% 3.30/0.99      | ~ v2_pre_topc(X1)
% 3.30/0.99      | v2_struct_0(X0)
% 3.30/0.99      | v2_struct_0(X1)
% 3.30/0.99      | v1_zfmisc_1(u1_struct_0(X0))
% 3.30/0.99      | ~ l1_pre_topc(X0)
% 3.30/0.99      | ~ l1_pre_topc(X1) ),
% 3.30/0.99      inference(resolution,[status(thm)],[c_13,c_416]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_8,plain,
% 3.30/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.30/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_500,plain,
% 3.30/0.99      ( v1_zfmisc_1(u1_struct_0(X0))
% 3.30/0.99      | v2_struct_0(X1)
% 3.30/0.99      | v2_struct_0(X0)
% 3.30/0.99      | ~ v2_pre_topc(X1)
% 3.30/0.99      | ~ v2_tdlat_3(X1)
% 3.30/0.99      | ~ v1_tdlat_3(X0)
% 3.30/0.99      | ~ m1_pre_topc(X0,X1)
% 3.30/0.99      | ~ l1_pre_topc(X1) ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_496,c_8]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_501,plain,
% 3.30/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.30/0.99      | ~ v1_tdlat_3(X0)
% 3.30/0.99      | ~ v2_tdlat_3(X1)
% 3.30/0.99      | ~ v2_pre_topc(X1)
% 3.30/0.99      | v2_struct_0(X0)
% 3.30/0.99      | v2_struct_0(X1)
% 3.30/0.99      | v1_zfmisc_1(u1_struct_0(X0))
% 3.30/0.99      | ~ l1_pre_topc(X1) ),
% 3.30/0.99      inference(renaming,[status(thm)],[c_500]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_12,plain,
% 3.30/0.99      ( ~ v2_tdlat_3(X0) | v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 3.30/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_520,plain,
% 3.30/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.30/0.99      | ~ v1_tdlat_3(X0)
% 3.30/0.99      | ~ v2_tdlat_3(X1)
% 3.30/0.99      | v2_struct_0(X0)
% 3.30/0.99      | v2_struct_0(X1)
% 3.30/0.99      | v1_zfmisc_1(u1_struct_0(X0))
% 3.30/0.99      | ~ l1_pre_topc(X1) ),
% 3.30/0.99      inference(forward_subsumption_resolution,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_501,c_12]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_29,negated_conjecture,
% 3.30/0.99      ( v2_tdlat_3(sK3) ),
% 3.30/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_541,plain,
% 3.30/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.30/0.99      | ~ v1_tdlat_3(X0)
% 3.30/0.99      | v2_struct_0(X0)
% 3.30/0.99      | v2_struct_0(X1)
% 3.30/0.99      | v1_zfmisc_1(u1_struct_0(X0))
% 3.30/0.99      | ~ l1_pre_topc(X1)
% 3.30/0.99      | sK3 != X1 ),
% 3.30/0.99      inference(resolution_lifted,[status(thm)],[c_520,c_29]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_542,plain,
% 3.30/0.99      ( ~ m1_pre_topc(X0,sK3)
% 3.30/0.99      | ~ v1_tdlat_3(X0)
% 3.30/0.99      | v2_struct_0(X0)
% 3.30/0.99      | v2_struct_0(sK3)
% 3.30/0.99      | v1_zfmisc_1(u1_struct_0(X0))
% 3.30/0.99      | ~ l1_pre_topc(sK3) ),
% 3.30/0.99      inference(unflattening,[status(thm)],[c_541]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_546,plain,
% 3.30/0.99      ( v1_zfmisc_1(u1_struct_0(X0))
% 3.30/0.99      | ~ m1_pre_topc(X0,sK3)
% 3.30/0.99      | ~ v1_tdlat_3(X0)
% 3.30/0.99      | v2_struct_0(X0) ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_542,c_31,c_28]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_547,plain,
% 3.30/0.99      ( ~ m1_pre_topc(X0,sK3)
% 3.30/0.99      | ~ v1_tdlat_3(X0)
% 3.30/0.99      | v2_struct_0(X0)
% 3.30/0.99      | v1_zfmisc_1(u1_struct_0(X0)) ),
% 3.30/0.99      inference(renaming,[status(thm)],[c_546]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_21,plain,
% 3.30/0.99      ( ~ v2_tex_2(X0,X1)
% 3.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/0.99      | v1_tdlat_3(sK2(X1,X0))
% 3.30/0.99      | ~ v2_pre_topc(X1)
% 3.30/0.99      | v2_struct_0(X1)
% 3.30/0.99      | ~ l1_pre_topc(X1)
% 3.30/0.99      | v1_xboole_0(X0) ),
% 3.30/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_724,plain,
% 3.30/0.99      ( ~ v2_tex_2(X0,X1)
% 3.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/0.99      | v1_tdlat_3(sK2(X1,X0))
% 3.30/0.99      | v2_struct_0(X1)
% 3.30/0.99      | ~ l1_pre_topc(X1)
% 3.30/0.99      | v1_xboole_0(X0)
% 3.30/0.99      | sK3 != X1 ),
% 3.30/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_30]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_725,plain,
% 3.30/0.99      ( ~ v2_tex_2(X0,sK3)
% 3.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.30/0.99      | v1_tdlat_3(sK2(sK3,X0))
% 3.30/0.99      | v2_struct_0(sK3)
% 3.30/0.99      | ~ l1_pre_topc(sK3)
% 3.30/0.99      | v1_xboole_0(X0) ),
% 3.30/0.99      inference(unflattening,[status(thm)],[c_724]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_729,plain,
% 3.30/0.99      ( ~ v2_tex_2(X0,sK3)
% 3.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.30/0.99      | v1_tdlat_3(sK2(sK3,X0))
% 3.30/0.99      | v1_xboole_0(X0) ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_725,c_31,c_28]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_819,plain,
% 3.30/0.99      ( ~ v2_tex_2(X0,sK3)
% 3.30/0.99      | ~ m1_pre_topc(X1,sK3)
% 3.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.30/0.99      | v2_struct_0(X1)
% 3.30/0.99      | v1_zfmisc_1(u1_struct_0(X1))
% 3.30/0.99      | v1_xboole_0(X0)
% 3.30/0.99      | sK2(sK3,X0) != X1 ),
% 3.30/0.99      inference(resolution_lifted,[status(thm)],[c_547,c_729]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_820,plain,
% 3.30/0.99      ( ~ v2_tex_2(X0,sK3)
% 3.30/0.99      | ~ m1_pre_topc(sK2(sK3,X0),sK3)
% 3.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.30/0.99      | v2_struct_0(sK2(sK3,X0))
% 3.30/0.99      | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
% 3.30/0.99      | v1_xboole_0(X0) ),
% 3.30/0.99      inference(unflattening,[status(thm)],[c_819]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_22,plain,
% 3.30/0.99      ( ~ v2_tex_2(X0,X1)
% 3.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/0.99      | ~ v2_pre_topc(X1)
% 3.30/0.99      | v2_struct_0(X1)
% 3.30/0.99      | ~ v2_struct_0(sK2(X1,X0))
% 3.30/0.99      | ~ l1_pre_topc(X1)
% 3.30/0.99      | v1_xboole_0(X0) ),
% 3.30/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_700,plain,
% 3.30/0.99      ( ~ v2_tex_2(X0,X1)
% 3.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/0.99      | v2_struct_0(X1)
% 3.30/0.99      | ~ v2_struct_0(sK2(X1,X0))
% 3.30/0.99      | ~ l1_pre_topc(X1)
% 3.30/0.99      | v1_xboole_0(X0)
% 3.30/0.99      | sK3 != X1 ),
% 3.30/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_30]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_701,plain,
% 3.30/0.99      ( ~ v2_tex_2(X0,sK3)
% 3.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.30/0.99      | ~ v2_struct_0(sK2(sK3,X0))
% 3.30/0.99      | v2_struct_0(sK3)
% 3.30/0.99      | ~ l1_pre_topc(sK3)
% 3.30/0.99      | v1_xboole_0(X0) ),
% 3.30/0.99      inference(unflattening,[status(thm)],[c_700]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_705,plain,
% 3.30/0.99      ( ~ v2_tex_2(X0,sK3)
% 3.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.30/0.99      | ~ v2_struct_0(sK2(sK3,X0))
% 3.30/0.99      | v1_xboole_0(X0) ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_701,c_31,c_28]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_20,plain,
% 3.30/0.99      ( ~ v2_tex_2(X0,X1)
% 3.30/0.99      | m1_pre_topc(sK2(X1,X0),X1)
% 3.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/0.99      | ~ v2_pre_topc(X1)
% 3.30/0.99      | v2_struct_0(X1)
% 3.30/0.99      | ~ l1_pre_topc(X1)
% 3.30/0.99      | v1_xboole_0(X0) ),
% 3.30/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_748,plain,
% 3.30/0.99      ( ~ v2_tex_2(X0,X1)
% 3.30/0.99      | m1_pre_topc(sK2(X1,X0),X1)
% 3.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.30/0.99      | v2_struct_0(X1)
% 3.30/0.99      | ~ l1_pre_topc(X1)
% 3.30/0.99      | v1_xboole_0(X0)
% 3.30/0.99      | sK3 != X1 ),
% 3.30/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_30]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_749,plain,
% 3.30/0.99      ( ~ v2_tex_2(X0,sK3)
% 3.30/0.99      | m1_pre_topc(sK2(sK3,X0),sK3)
% 3.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.30/0.99      | v2_struct_0(sK3)
% 3.30/0.99      | ~ l1_pre_topc(sK3)
% 3.30/0.99      | v1_xboole_0(X0) ),
% 3.30/0.99      inference(unflattening,[status(thm)],[c_748]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_753,plain,
% 3.30/0.99      ( ~ v2_tex_2(X0,sK3)
% 3.30/0.99      | m1_pre_topc(sK2(sK3,X0),sK3)
% 3.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.30/0.99      | v1_xboole_0(X0) ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_749,c_31,c_28]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_824,plain,
% 3.30/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.30/0.99      | ~ v2_tex_2(X0,sK3)
% 3.30/0.99      | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
% 3.30/0.99      | v1_xboole_0(X0) ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_820,c_705,c_753]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_825,plain,
% 3.30/0.99      ( ~ v2_tex_2(X0,sK3)
% 3.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.30/0.99      | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
% 3.30/0.99      | v1_xboole_0(X0) ),
% 3.30/0.99      inference(renaming,[status(thm)],[c_824]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2290,plain,
% 3.30/0.99      ( v2_tex_2(X0,sK3) != iProver_top
% 3.30/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.30/0.99      | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0))) = iProver_top
% 3.30/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_825]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2626,plain,
% 3.30/0.99      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.30/0.99      | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) = iProver_top
% 3.30/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_2300,c_2290]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2627,plain,
% 3.30/0.99      ( ~ v2_tex_2(sK4,sK3)
% 3.30/0.99      | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
% 3.30/0.99      | v1_xboole_0(sK4) ),
% 3.30/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2626]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2654,plain,
% 3.30/0.99      ( sK4 = sK4 ),
% 3.30/0.99      inference(instantiation,[status(thm)],[c_1738]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1739,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2636,plain,
% 3.30/0.99      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 3.30/0.99      inference(instantiation,[status(thm)],[c_1739]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2827,plain,
% 3.30/0.99      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 3.30/0.99      inference(instantiation,[status(thm)],[c_2636]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3027,plain,
% 3.30/0.99      ( u1_struct_0(sK2(sK3,sK4)) != sK4
% 3.30/0.99      | sK4 = u1_struct_0(sK2(sK3,sK4))
% 3.30/0.99      | sK4 != sK4 ),
% 3.30/0.99      inference(instantiation,[status(thm)],[c_2827]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1747,plain,
% 3.30/0.99      ( ~ v1_zfmisc_1(X0) | v1_zfmisc_1(X1) | X1 != X0 ),
% 3.30/0.99      theory(equality) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2764,plain,
% 3.30/0.99      ( v1_zfmisc_1(X0)
% 3.30/0.99      | ~ v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
% 3.30/0.99      | X0 != u1_struct_0(sK2(sK3,sK4)) ),
% 3.30/0.99      inference(instantiation,[status(thm)],[c_1747]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3536,plain,
% 3.30/0.99      ( ~ v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
% 3.30/0.99      | v1_zfmisc_1(sK4)
% 3.30/0.99      | sK4 != u1_struct_0(sK2(sK3,sK4)) ),
% 3.30/0.99      inference(instantiation,[status(thm)],[c_2764]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_4379,plain,
% 3.30/0.99      ( k1_tarski(sK0(sK4)) = sK4 ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_4179,c_36,c_39,c_658,c_2626,c_2654,c_2931,c_3027,
% 3.30/0.99                 c_3537]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_5216,plain,
% 3.30/0.99      ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = sK4
% 3.30/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.30/0.99      inference(light_normalisation,[status(thm)],[c_5213,c_4379]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_5,plain,
% 3.30/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.30/0.99      | ~ v1_xboole_0(X1)
% 3.30/0.99      | v1_xboole_0(X0) ),
% 3.30/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2533,plain,
% 3.30/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
% 3.30/0.99      | ~ v1_xboole_0(X0)
% 3.30/0.99      | v1_xboole_0(sK4) ),
% 3.30/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2633,plain,
% 3.30/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.30/0.99      | ~ v1_xboole_0(u1_struct_0(sK3))
% 3.30/0.99      | v1_xboole_0(sK4) ),
% 3.30/0.99      inference(instantiation,[status(thm)],[c_2533]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2634,plain,
% 3.30/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.30/0.99      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top
% 3.30/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_2633]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_5560,plain,
% 3.30/0.99      ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = sK4 ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_5216,c_36,c_37,c_2634]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_23,plain,
% 3.30/0.99      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 3.30/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.30/0.99      | ~ v2_pre_topc(X0)
% 3.30/0.99      | v2_struct_0(X0)
% 3.30/0.99      | ~ l1_pre_topc(X0) ),
% 3.30/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_682,plain,
% 3.30/0.99      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 3.30/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.30/0.99      | v2_struct_0(X0)
% 3.30/0.99      | ~ l1_pre_topc(X0)
% 3.30/0.99      | sK3 != X0 ),
% 3.30/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_30]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_683,plain,
% 3.30/0.99      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
% 3.30/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.30/0.99      | v2_struct_0(sK3)
% 3.30/0.99      | ~ l1_pre_topc(sK3) ),
% 3.30/0.99      inference(unflattening,[status(thm)],[c_682]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_687,plain,
% 3.30/0.99      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
% 3.30/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_683,c_31,c_28]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2294,plain,
% 3.30/0.99      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) = iProver_top
% 3.30/0.99      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_687]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_5563,plain,
% 3.30/0.99      ( v2_tex_2(sK4,sK3) = iProver_top
% 3.30/0.99      | m1_subset_1(sK0(sK4),u1_struct_0(sK3)) != iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_5560,c_2294]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2920,plain,
% 3.30/0.99      ( v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) = iProver_top
% 3.30/0.99      | v2_tex_2(sK4,sK3) != iProver_top ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_2626,c_36]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2921,plain,
% 3.30/0.99      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.30/0.99      | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) = iProver_top ),
% 3.30/0.99      inference(renaming,[status(thm)],[c_2920]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_4180,plain,
% 3.30/0.99      ( k1_tarski(sK0(u1_struct_0(sK2(sK3,sK4)))) = u1_struct_0(sK2(sK3,sK4))
% 3.30/0.99      | v2_tex_2(sK4,sK3) != iProver_top
% 3.30/0.99      | v1_xboole_0(u1_struct_0(sK2(sK3,sK4))) = iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_2921,c_2296]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_24,negated_conjecture,
% 3.30/0.99      ( ~ v2_tex_2(sK4,sK3) | ~ v1_zfmisc_1(sK4) ),
% 3.30/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_39,plain,
% 3.30/0.99      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.30/0.99      | v1_zfmisc_1(sK4) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3537,plain,
% 3.30/0.99      ( sK4 != u1_struct_0(sK2(sK3,sK4))
% 3.30/0.99      | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) != iProver_top
% 3.30/0.99      | v1_zfmisc_1(sK4) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_3536]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_4479,plain,
% 3.30/0.99      ( v2_tex_2(sK4,sK3) != iProver_top ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_4180,c_36,c_39,c_2626,c_2654,c_2931,c_3027,c_3537]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(contradiction,plain,
% 3.30/0.99      ( $false ),
% 3.30/0.99      inference(minisat,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_5563,c_4479,c_3782,c_3145,c_2957,c_2603,c_2592,c_2583,
% 3.30/0.99                 c_2526,c_37,c_26,c_36,c_27,c_35,c_28,c_32,c_31]) ).
% 3.30/0.99  
% 3.30/0.99  
% 3.30/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.30/0.99  
% 3.30/0.99  ------                               Statistics
% 3.30/0.99  
% 3.30/0.99  ------ General
% 3.30/0.99  
% 3.30/0.99  abstr_ref_over_cycles:                  0
% 3.30/0.99  abstr_ref_under_cycles:                 0
% 3.30/0.99  gc_basic_clause_elim:                   0
% 3.30/0.99  forced_gc_time:                         0
% 3.30/0.99  parsing_time:                           0.008
% 3.30/0.99  unif_index_cands_time:                  0.
% 3.30/0.99  unif_index_add_time:                    0.
% 3.30/0.99  orderings_time:                         0.
% 3.30/0.99  out_proof_time:                         0.023
% 3.30/0.99  total_time:                             0.206
% 3.30/0.99  num_of_symbols:                         54
% 3.30/0.99  num_of_terms:                           3334
% 3.30/0.99  
% 3.30/0.99  ------ Preprocessing
% 3.30/0.99  
% 3.30/0.99  num_of_splits:                          0
% 3.30/0.99  num_of_split_atoms:                     0
% 3.30/0.99  num_of_reused_defs:                     0
% 3.30/0.99  num_eq_ax_congr_red:                    22
% 3.30/0.99  num_of_sem_filtered_clauses:            1
% 3.30/0.99  num_of_subtypes:                        0
% 3.30/0.99  monotx_restored_types:                  0
% 3.30/0.99  sat_num_of_epr_types:                   0
% 3.30/0.99  sat_num_of_non_cyclic_types:            0
% 3.30/0.99  sat_guarded_non_collapsed_types:        0
% 3.30/0.99  num_pure_diseq_elim:                    0
% 3.30/0.99  simp_replaced_by:                       0
% 3.30/0.99  res_preprocessed:                       123
% 3.30/0.99  prep_upred:                             0
% 3.30/0.99  prep_unflattend:                        55
% 3.30/0.99  smt_new_axioms:                         0
% 3.30/0.99  pred_elim_cands:                        7
% 3.30/0.99  pred_elim:                              7
% 3.30/0.99  pred_elim_cl:                           10
% 3.30/0.99  pred_elim_cycles:                       15
% 3.30/0.99  merged_defs:                            10
% 3.30/0.99  merged_defs_ncl:                        0
% 3.30/0.99  bin_hyper_res:                          10
% 3.30/0.99  prep_cycles:                            4
% 3.30/0.99  pred_elim_time:                         0.022
% 3.30/0.99  splitting_time:                         0.
% 3.30/0.99  sem_filter_time:                        0.
% 3.30/0.99  monotx_time:                            0.001
% 3.30/0.99  subtype_inf_time:                       0.
% 3.30/0.99  
% 3.30/0.99  ------ Problem properties
% 3.30/0.99  
% 3.30/0.99  clauses:                                21
% 3.30/0.99  conjectures:                            6
% 3.30/0.99  epr:                                    6
% 3.30/0.99  horn:                                   10
% 3.30/0.99  ground:                                 6
% 3.30/0.99  unary:                                  5
% 3.30/0.99  binary:                                 4
% 3.30/0.99  lits:                                   62
% 3.30/0.99  lits_eq:                                4
% 3.30/0.99  fd_pure:                                0
% 3.30/0.99  fd_pseudo:                              0
% 3.30/0.99  fd_cond:                                0
% 3.30/0.99  fd_pseudo_cond:                         0
% 3.30/0.99  ac_symbols:                             0
% 3.30/0.99  
% 3.30/0.99  ------ Propositional Solver
% 3.30/0.99  
% 3.30/0.99  prop_solver_calls:                      28
% 3.30/0.99  prop_fast_solver_calls:                 1364
% 3.30/0.99  smt_solver_calls:                       0
% 3.30/0.99  smt_fast_solver_calls:                  0
% 3.30/0.99  prop_num_of_clauses:                    1573
% 3.30/0.99  prop_preprocess_simplified:             5605
% 3.30/0.99  prop_fo_subsumed:                       94
% 3.30/0.99  prop_solver_time:                       0.
% 3.30/0.99  smt_solver_time:                        0.
% 3.30/0.99  smt_fast_solver_time:                   0.
% 3.30/0.99  prop_fast_solver_time:                  0.
% 3.30/0.99  prop_unsat_core_time:                   0.
% 3.30/0.99  
% 3.30/0.99  ------ QBF
% 3.30/0.99  
% 3.30/0.99  qbf_q_res:                              0
% 3.30/0.99  qbf_num_tautologies:                    0
% 3.30/0.99  qbf_prep_cycles:                        0
% 3.30/0.99  
% 3.30/0.99  ------ BMC1
% 3.30/0.99  
% 3.30/0.99  bmc1_current_bound:                     -1
% 3.30/0.99  bmc1_last_solved_bound:                 -1
% 3.30/0.99  bmc1_unsat_core_size:                   -1
% 3.30/0.99  bmc1_unsat_core_parents_size:           -1
% 3.30/0.99  bmc1_merge_next_fun:                    0
% 3.30/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.30/0.99  
% 3.30/0.99  ------ Instantiation
% 3.30/0.99  
% 3.30/0.99  inst_num_of_clauses:                    494
% 3.30/0.99  inst_num_in_passive:                    1
% 3.30/0.99  inst_num_in_active:                     295
% 3.30/0.99  inst_num_in_unprocessed:                198
% 3.30/0.99  inst_num_of_loops:                      350
% 3.30/0.99  inst_num_of_learning_restarts:          0
% 3.30/0.99  inst_num_moves_active_passive:          51
% 3.30/0.99  inst_lit_activity:                      0
% 3.30/0.99  inst_lit_activity_moves:                0
% 3.30/0.99  inst_num_tautologies:                   0
% 3.30/0.99  inst_num_prop_implied:                  0
% 3.30/0.99  inst_num_existing_simplified:           0
% 3.30/0.99  inst_num_eq_res_simplified:             0
% 3.30/0.99  inst_num_child_elim:                    0
% 3.30/0.99  inst_num_of_dismatching_blockings:      123
% 3.30/0.99  inst_num_of_non_proper_insts:           551
% 3.30/0.99  inst_num_of_duplicates:                 0
% 3.30/0.99  inst_inst_num_from_inst_to_res:         0
% 3.30/0.99  inst_dismatching_checking_time:         0.
% 3.30/0.99  
% 3.30/0.99  ------ Resolution
% 3.30/0.99  
% 3.30/0.99  res_num_of_clauses:                     0
% 3.30/0.99  res_num_in_passive:                     0
% 3.30/0.99  res_num_in_active:                      0
% 3.30/0.99  res_num_of_loops:                       127
% 3.30/0.99  res_forward_subset_subsumed:            83
% 3.30/0.99  res_backward_subset_subsumed:           8
% 3.30/0.99  res_forward_subsumed:                   0
% 3.30/0.99  res_backward_subsumed:                  0
% 3.30/0.99  res_forward_subsumption_resolution:     2
% 3.30/0.99  res_backward_subsumption_resolution:    0
% 3.30/0.99  res_clause_to_clause_subsumption:       168
% 3.30/0.99  res_orphan_elimination:                 0
% 3.30/0.99  res_tautology_del:                      116
% 3.30/0.99  res_num_eq_res_simplified:              0
% 3.30/0.99  res_num_sel_changes:                    0
% 3.30/0.99  res_moves_from_active_to_pass:          0
% 3.30/0.99  
% 3.30/0.99  ------ Superposition
% 3.30/0.99  
% 3.30/0.99  sup_time_total:                         0.
% 3.30/0.99  sup_time_generating:                    0.
% 3.30/0.99  sup_time_sim_full:                      0.
% 3.30/0.99  sup_time_sim_immed:                     0.
% 3.30/0.99  
% 3.30/0.99  sup_num_of_clauses:                     78
% 3.30/0.99  sup_num_in_active:                      63
% 3.30/0.99  sup_num_in_passive:                     15
% 3.30/0.99  sup_num_of_loops:                       68
% 3.30/0.99  sup_fw_superposition:                   27
% 3.30/0.99  sup_bw_superposition:                   42
% 3.30/0.99  sup_immediate_simplified:               10
% 3.30/0.99  sup_given_eliminated:                   0
% 3.30/0.99  comparisons_done:                       0
% 3.30/0.99  comparisons_avoided:                    0
% 3.30/0.99  
% 3.30/0.99  ------ Simplifications
% 3.30/0.99  
% 3.30/0.99  
% 3.30/0.99  sim_fw_subset_subsumed:                 1
% 3.30/0.99  sim_bw_subset_subsumed:                 5
% 3.30/0.99  sim_fw_subsumed:                        2
% 3.30/0.99  sim_bw_subsumed:                        0
% 3.30/0.99  sim_fw_subsumption_res:                 0
% 3.30/0.99  sim_bw_subsumption_res:                 0
% 3.30/0.99  sim_tautology_del:                      2
% 3.30/0.99  sim_eq_tautology_del:                   0
% 3.30/0.99  sim_eq_res_simp:                        0
% 3.30/0.99  sim_fw_demodulated:                     0
% 3.30/0.99  sim_bw_demodulated:                     1
% 3.30/0.99  sim_light_normalised:                   9
% 3.30/0.99  sim_joinable_taut:                      0
% 3.30/0.99  sim_joinable_simp:                      0
% 3.30/0.99  sim_ac_normalised:                      0
% 3.30/0.99  sim_smt_subsumption:                    0
% 3.30/0.99  
%------------------------------------------------------------------------------
