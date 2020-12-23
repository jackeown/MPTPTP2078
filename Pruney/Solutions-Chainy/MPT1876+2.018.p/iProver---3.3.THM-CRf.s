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
% DateTime   : Thu Dec  3 12:26:50 EST 2020

% Result     : Theorem 3.51s
% Output     : CNFRefutation 3.51s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_4837)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,conjecture,(
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

fof(f25,negated_conjecture,(
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
    inference(negated_conjecture,[],[f24])).

fof(f58,plain,(
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
    inference(ennf_transformation,[],[f25])).

fof(f59,plain,(
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
    inference(flattening,[],[f58])).

fof(f74,plain,(
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
    inference(nnf_transformation,[],[f59])).

fof(f75,plain,(
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
    inference(flattening,[],[f74])).

fof(f77,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
     => ( ( ~ v1_zfmisc_1(sK5)
          | ~ v2_tex_2(sK5,X0) )
        & ( v1_zfmisc_1(sK5)
          | v2_tex_2(sK5,X0) )
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,
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
            | ~ v2_tex_2(X1,sK4) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,sK4) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK4)
      & v2_tdlat_3(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,
    ( ( ~ v1_zfmisc_1(sK5)
      | ~ v2_tex_2(sK5,sK4) )
    & ( v1_zfmisc_1(sK5)
      | v2_tex_2(sK5,sK4) )
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & ~ v1_xboole_0(sK5)
    & l1_pre_topc(sK4)
    & v2_tdlat_3(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f75,f77,f76])).

fof(f120,plain,
    ( v1_zfmisc_1(sK5)
    | v2_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f78])).

fof(f119,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f78])).

fof(f22,axiom,(
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

fof(f26,plain,(
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
    inference(pure_predicate_removal,[],[f22])).

fof(f54,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f72,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_tdlat_3(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK3(X0,X1)) = X1
        & m1_pre_topc(sK3(X0,X1),X0)
        & v1_tdlat_3(sK3(X0,X1))
        & ~ v2_struct_0(sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK3(X0,X1)) = X1
            & m1_pre_topc(sK3(X0,X1),X0)
            & v1_tdlat_3(sK3(X0,X1))
            & ~ v2_struct_0(sK3(X0,X1)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f55,f72])).

fof(f112,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK3(X0,X1)) = X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f114,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f78])).

fof(f115,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f78])).

fof(f117,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f78])).

fof(f118,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f78])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f61,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f60])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f61,f62])).

fof(f80,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f21,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f108,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f20,axiom,(
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

fof(f27,plain,(
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
    inference(pure_predicate_removal,[],[f20])).

fof(f50,plain,(
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
    inference(ennf_transformation,[],[f27])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f70,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK2(X0,X1)) = X1
        & m1_pre_topc(sK2(X0,X1),X0)
        & ~ v2_struct_0(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK2(X0,X1)) = X1
            & m1_pre_topc(sK2(X0,X1),X0)
            & ~ v2_struct_0(sK2(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f51,f70])).

fof(f107,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK2(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( v2_tdlat_3(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_pre_topc(X0)
          & v7_struct_0(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f102,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f100,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f95,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f97,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK3(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f110,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(sK3(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f111,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK3(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f96,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_tdlat_3(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f104,plain,(
    ! [X0,X1] :
      ( v2_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f116,plain,(
    v2_tdlat_3(sK4) ),
    inference(cnf_transformation,[],[f78])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f65])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f123,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(equality_resolution,[],[f86])).

fof(f121,plain,
    ( ~ v1_zfmisc_1(sK5)
    | ~ v2_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f78])).

fof(f106,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK2(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f15,axiom,(
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

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f113,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_36,negated_conjecture,
    ( v2_tex_2(sK5,sK4)
    | v1_zfmisc_1(sK5) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_4340,plain,
    ( v2_tex_2(sK5,sK4) = iProver_top
    | v1_zfmisc_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_4339,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_30,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK3(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_4346,plain,
    ( u1_struct_0(sK3(X0,X1)) = X1
    | v2_tex_2(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_7345,plain,
    ( u1_struct_0(sK3(sK4,sK5)) = sK5
    | v2_tex_2(sK5,sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4339,c_4346])).

cnf(c_42,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_43,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_41,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_44,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_39,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_46,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_38,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_47,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_7813,plain,
    ( u1_struct_0(sK3(sK4,sK5)) = sK5
    | v2_tex_2(sK5,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7345,c_43,c_44,c_46,c_47])).

cnf(c_7819,plain,
    ( u1_struct_0(sK3(sK4,sK5)) = sK5
    | v1_zfmisc_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4340,c_7813])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_4,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_314,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_tarski(X0),X1) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_315,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_314])).

cnf(c_797,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | v1_xboole_0(X2)
    | X1 != X2
    | sK0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_315])).

cnf(c_798,plain,
    ( r1_tarski(k1_tarski(sK0(X0)),X0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_797])).

cnf(c_4327,plain,
    ( r1_tarski(k1_tarski(sK0(X0)),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_798])).

cnf(c_29,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_4347,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5459,plain,
    ( k1_tarski(sK0(X0)) = X0
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_tarski(sK0(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4327,c_4347])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_4359,plain,
    ( v1_xboole_0(k1_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_9072,plain,
    ( k1_tarski(sK0(X0)) = X0
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5459,c_4359])).

cnf(c_9077,plain,
    ( u1_struct_0(sK3(sK4,sK5)) = sK5
    | k1_tarski(sK0(sK5)) = sK5
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_7819,c_9072])).

cnf(c_9099,plain,
    ( v1_xboole_0(sK5)
    | u1_struct_0(sK3(sK4,sK5)) = sK5
    | k1_tarski(sK0(sK5)) = sK5 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9077])).

cnf(c_9317,plain,
    ( k1_tarski(sK0(sK5)) = sK5
    | u1_struct_0(sK3(sK4,sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9077,c_38,c_9099])).

cnf(c_9318,plain,
    ( u1_struct_0(sK3(sK4,sK5)) = sK5
    | k1_tarski(sK0(sK5)) = sK5 ),
    inference(renaming,[status(thm)],[c_9317])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK2(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_4350,plain,
    ( u1_struct_0(sK2(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_9326,plain,
    ( u1_struct_0(sK2(sK3(sK4,sK5),X0)) = X0
    | k1_tarski(sK0(sK5)) = sK5
    | m1_subset_1(X0,k1_zfmisc_1(sK5)) != iProver_top
    | v2_struct_0(sK3(sK4,sK5)) = iProver_top
    | l1_pre_topc(sK3(sK4,sK5)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9318,c_4350])).

cnf(c_23,plain,
    ( ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_21,plain,
    ( ~ v2_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_239,plain,
    ( ~ v2_tdlat_3(X0)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_21])).

cnf(c_240,plain,
    ( ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X0)
    | v2_struct_0(X0)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_239])).

cnf(c_16,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_18,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_534,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_16,c_18])).

cnf(c_552,plain,
    ( ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X0)
    | v2_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_240,c_534])).

cnf(c_4333,plain,
    ( v1_tdlat_3(X0) != iProver_top
    | v2_tdlat_3(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_552])).

cnf(c_9321,plain,
    ( k1_tarski(sK0(sK5)) = sK5
    | v1_tdlat_3(sK3(sK4,sK5)) != iProver_top
    | v2_tdlat_3(sK3(sK4,sK5)) != iProver_top
    | v2_struct_0(sK3(sK4,sK5)) = iProver_top
    | v1_zfmisc_1(sK5) = iProver_top
    | l1_pre_topc(sK3(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9318,c_4333])).

cnf(c_49,plain,
    ( v2_tex_2(sK5,sK4) = iProver_top
    | v1_zfmisc_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_33,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK3(X1,X0))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_318,plain,
    ( v1_zfmisc_1(sK5)
    | v2_tex_2(sK5,sK4) ),
    inference(prop_impl,[status(thm)],[c_36])).

cnf(c_319,plain,
    ( v2_tex_2(sK5,sK4)
    | v1_zfmisc_1(sK5) ),
    inference(renaming,[status(thm)],[c_318])).

cnf(c_1323,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK3(X1,X0))
    | v1_zfmisc_1(sK5)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_319])).

cnf(c_1324,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_pre_topc(sK4)
    | ~ v2_struct_0(sK3(sK4,sK5))
    | v2_struct_0(sK4)
    | v1_zfmisc_1(sK5)
    | ~ l1_pre_topc(sK4)
    | v1_xboole_0(sK5) ),
    inference(unflattening,[status(thm)],[c_1323])).

cnf(c_1326,plain,
    ( ~ v2_struct_0(sK3(sK4,sK5))
    | v1_zfmisc_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1324,c_42,c_41,c_39,c_38,c_37])).

cnf(c_1328,plain,
    ( v2_struct_0(sK3(sK4,sK5)) != iProver_top
    | v1_zfmisc_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1326])).

cnf(c_32,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tdlat_3(sK3(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1337,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tdlat_3(sK3(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v1_zfmisc_1(sK5)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_319])).

cnf(c_1338,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_tdlat_3(sK3(sK4,sK5))
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | v1_zfmisc_1(sK5)
    | ~ l1_pre_topc(sK4)
    | v1_xboole_0(sK5) ),
    inference(unflattening,[status(thm)],[c_1337])).

cnf(c_1340,plain,
    ( v1_tdlat_3(sK3(sK4,sK5))
    | v1_zfmisc_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1338,c_42,c_41,c_39,c_38,c_37])).

cnf(c_1342,plain,
    ( v1_tdlat_3(sK3(sK4,sK5)) = iProver_top
    | v1_zfmisc_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1340])).

cnf(c_31,plain,
    ( ~ v2_tex_2(X0,X1)
    | m1_pre_topc(sK3(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_4345,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | m1_pre_topc(sK3(X1,X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_8277,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top
    | m1_pre_topc(sK3(sK4,sK5),sK4) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4339,c_4345])).

cnf(c_8577,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top
    | m1_pre_topc(sK3(sK4,sK5),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8277,c_43,c_44,c_46,c_47,c_48,c_4837])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_4354,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_8583,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top
    | l1_pre_topc(sK3(sK4,sK5)) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8577,c_4354])).

cnf(c_25,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_tdlat_3(X1)
    | v2_tdlat_3(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1567,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_tdlat_3(X2)
    | ~ v2_tdlat_3(X1)
    | v2_tdlat_3(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_25])).

cnf(c_1568,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_tdlat_3(X1)
    | v2_tdlat_3(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_1567])).

cnf(c_4326,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | v2_tdlat_3(X1) != iProver_top
    | v2_tdlat_3(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1568])).

cnf(c_8584,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top
    | v2_tdlat_3(sK3(sK4,sK5)) = iProver_top
    | v2_tdlat_3(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8577,c_4326])).

cnf(c_40,negated_conjecture,
    ( v2_tdlat_3(sK4) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_45,plain,
    ( v2_tdlat_3(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_8652,plain,
    ( v2_tdlat_3(sK3(sK4,sK5)) = iProver_top
    | v2_tex_2(sK5,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8584,c_43,c_45,c_46])).

cnf(c_8653,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top
    | v2_tdlat_3(sK3(sK4,sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_8652])).

cnf(c_10887,plain,
    ( v1_zfmisc_1(sK5) = iProver_top
    | k1_tarski(sK0(sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9321,c_43,c_45,c_46,c_49,c_1328,c_1342,c_8583,c_8584])).

cnf(c_10888,plain,
    ( k1_tarski(sK0(sK5)) = sK5
    | v1_zfmisc_1(sK5) = iProver_top ),
    inference(renaming,[status(thm)],[c_10887])).

cnf(c_10893,plain,
    ( k1_tarski(sK0(sK5)) = sK5
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_10888,c_9072])).

cnf(c_12419,plain,
    ( k1_tarski(sK0(sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9326,c_47,c_10893])).

cnf(c_7,plain,
    ( r1_tarski(k1_xboole_0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_4357,plain,
    ( r1_tarski(k1_xboole_0,k1_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_12472,plain,
    ( r1_tarski(k1_xboole_0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_12419,c_4357])).

cnf(c_12874,plain,
    ( sK5 = k1_xboole_0
    | v1_zfmisc_1(sK5) != iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_12472,c_4347])).

cnf(c_35,negated_conjecture,
    ( ~ v2_tex_2(sK5,sK4)
    | ~ v1_zfmisc_1(sK5) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_50,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top
    | v1_zfmisc_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_27,plain,
    ( m1_pre_topc(sK2(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_4349,plain,
    ( m1_pre_topc(sK2(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_6015,plain,
    ( m1_pre_topc(sK2(sK4,sK5),sK4) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4339,c_4349])).

cnf(c_48,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_4781,plain,
    ( m1_pre_topc(sK2(X0,sK5),X0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_4782,plain,
    ( m1_pre_topc(sK2(X0,sK5),X0) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4781])).

cnf(c_4784,plain,
    ( m1_pre_topc(sK2(sK4,sK5),sK4) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4782])).

cnf(c_6277,plain,
    ( m1_pre_topc(sK2(sK4,sK5),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6015,c_43,c_46,c_47,c_48,c_4784])).

cnf(c_5869,plain,
    ( u1_struct_0(sK2(sK4,sK5)) = sK5
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4339,c_4350])).

cnf(c_4771,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(sK5)
    | u1_struct_0(sK2(X0,sK5)) = sK5 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_4773,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | v1_xboole_0(sK5)
    | u1_struct_0(sK2(sK4,sK5)) = sK5 ),
    inference(instantiation,[status(thm)],[c_4771])).

cnf(c_6110,plain,
    ( u1_struct_0(sK2(sK4,sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5869,c_42,c_39,c_38,c_37,c_4773])).

cnf(c_11,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_785,plain,
    ( m1_subset_1(X0,X1)
    | v1_xboole_0(X2)
    | X1 != X2
    | sK0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_11])).

cnf(c_786,plain,
    ( m1_subset_1(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_785])).

cnf(c_4328,plain,
    ( m1_subset_1(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_786])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_4353,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7001,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(X0)),u1_struct_0(X1)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4328,c_4353])).

cnf(c_11440,plain,
    ( m1_pre_topc(sK2(sK4,sK5),X0) != iProver_top
    | m1_subset_1(sK0(sK5),u1_struct_0(X0)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2(sK4,sK5)) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2(sK4,sK5))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6110,c_7001])).

cnf(c_11526,plain,
    ( m1_pre_topc(sK2(sK4,sK5),X0) != iProver_top
    | m1_subset_1(sK0(sK5),u1_struct_0(X0)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2(sK4,sK5)) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11440,c_6110])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK2(X1,X0))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_4751,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK2(X0,sK5))
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_4752,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2(X0,sK5)) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4751])).

cnf(c_4754,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v2_struct_0(sK2(sK4,sK5)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4752])).

cnf(c_11623,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(sK2(sK4,sK5),X0) != iProver_top
    | m1_subset_1(sK0(sK5),u1_struct_0(X0)) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11526,c_43,c_46,c_47,c_48,c_4754])).

cnf(c_11624,plain,
    ( m1_pre_topc(sK2(sK4,sK5),X0) != iProver_top
    | m1_subset_1(sK0(sK5),u1_struct_0(X0)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_11623])).

cnf(c_11633,plain,
    ( m1_subset_1(sK0(sK5),u1_struct_0(sK4)) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6277,c_11624])).

cnf(c_4674,plain,
    ( m1_subset_1(sK0(sK5),sK5)
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_786])).

cnf(c_4675,plain,
    ( m1_subset_1(sK0(sK5),sK5) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4674])).

cnf(c_3481,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4874,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK0(sK5),sK5)
    | X0 != sK0(sK5)
    | X1 != sK5 ),
    inference(instantiation,[status(thm)],[c_3481])).

cnf(c_5129,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2(X1,sK5)))
    | ~ m1_subset_1(sK0(sK5),sK5)
    | X0 != sK0(sK5)
    | u1_struct_0(sK2(X1,sK5)) != sK5 ),
    inference(instantiation,[status(thm)],[c_4874])).

cnf(c_5718,plain,
    ( m1_subset_1(sK0(sK5),u1_struct_0(sK2(X0,sK5)))
    | ~ m1_subset_1(sK0(sK5),sK5)
    | u1_struct_0(sK2(X0,sK5)) != sK5
    | sK0(sK5) != sK0(sK5) ),
    inference(instantiation,[status(thm)],[c_5129])).

cnf(c_5720,plain,
    ( u1_struct_0(sK2(X0,sK5)) != sK5
    | sK0(sK5) != sK0(sK5)
    | m1_subset_1(sK0(sK5),u1_struct_0(sK2(X0,sK5))) = iProver_top
    | m1_subset_1(sK0(sK5),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5718])).

cnf(c_5722,plain,
    ( u1_struct_0(sK2(sK4,sK5)) != sK5
    | sK0(sK5) != sK0(sK5)
    | m1_subset_1(sK0(sK5),u1_struct_0(sK2(sK4,sK5))) = iProver_top
    | m1_subset_1(sK0(sK5),sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5720])).

cnf(c_3474,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_5719,plain,
    ( sK0(sK5) = sK0(sK5) ),
    inference(instantiation,[status(thm)],[c_3474])).

cnf(c_4939,plain,
    ( ~ m1_pre_topc(sK2(X0,sK5),X0)
    | m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK2(X0,sK5)))
    | v2_struct_0(X0)
    | v2_struct_0(sK2(X0,sK5))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_8008,plain,
    ( ~ m1_pre_topc(sK2(X0,sK5),X0)
    | m1_subset_1(sK0(sK5),u1_struct_0(X0))
    | ~ m1_subset_1(sK0(sK5),u1_struct_0(sK2(X0,sK5)))
    | v2_struct_0(X0)
    | v2_struct_0(sK2(X0,sK5))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_4939])).

cnf(c_8009,plain,
    ( m1_pre_topc(sK2(X0,sK5),X0) != iProver_top
    | m1_subset_1(sK0(sK5),u1_struct_0(X0)) = iProver_top
    | m1_subset_1(sK0(sK5),u1_struct_0(sK2(X0,sK5))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2(X0,sK5)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8008])).

cnf(c_8011,plain,
    ( m1_pre_topc(sK2(sK4,sK5),sK4) != iProver_top
    | m1_subset_1(sK0(sK5),u1_struct_0(sK2(sK4,sK5))) != iProver_top
    | m1_subset_1(sK0(sK5),u1_struct_0(sK4)) = iProver_top
    | v2_struct_0(sK2(sK4,sK5)) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8009])).

cnf(c_11669,plain,
    ( m1_subset_1(sK0(sK5),u1_struct_0(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11633,c_42,c_43,c_39,c_46,c_38,c_47,c_37,c_48,c_4675,c_4754,c_4773,c_4784,c_5722,c_5719,c_8011])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_4352,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_11676,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK0(sK5)) = k1_tarski(sK0(sK5))
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11669,c_4352])).

cnf(c_7002,plain,
    ( m1_pre_topc(sK2(sK4,sK5),X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) = iProver_top
    | m1_subset_1(X1,sK5) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2(sK4,sK5)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6110,c_4353])).

cnf(c_8020,plain,
    ( v2_struct_0(X0) = iProver_top
    | m1_subset_1(X1,sK5) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) = iProver_top
    | m1_pre_topc(sK2(sK4,sK5),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7002,c_43,c_46,c_47,c_48,c_4754])).

cnf(c_8021,plain,
    ( m1_pre_topc(sK2(sK4,sK5),X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) = iProver_top
    | m1_subset_1(X1,sK5) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8020])).

cnf(c_8031,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(X0,sK5) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6277,c_8021])).

cnf(c_8136,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8031,c_43,c_46])).

cnf(c_8145,plain,
    ( k6_domain_1(u1_struct_0(sK4),X0) = k1_tarski(X0)
    | m1_subset_1(X0,sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8136,c_4352])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_4690,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_4888,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_xboole_0(u1_struct_0(sK4))
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_4690])).

cnf(c_4889,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4888])).

cnf(c_8993,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | k6_domain_1(u1_struct_0(sK4),X0) = k1_tarski(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8145,c_47,c_48,c_4889])).

cnf(c_8994,plain,
    ( k6_domain_1(u1_struct_0(sK4),X0) = k1_tarski(X0)
    | m1_subset_1(X0,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_8993])).

cnf(c_9002,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK0(sK5)) = k1_tarski(sK0(sK5))
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4328,c_8994])).

cnf(c_11921,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK0(sK5)) = k1_tarski(sK0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11676,c_47,c_9002])).

cnf(c_34,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_4342,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_11924,plain,
    ( v2_tex_2(k1_tarski(sK0(sK5)),sK4) = iProver_top
    | m1_subset_1(sK0(sK5),u1_struct_0(sK4)) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_11921,c_4342])).

cnf(c_12128,plain,
    ( v2_tex_2(k1_tarski(sK0(sK5)),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11924,c_42,c_43,c_44,c_39,c_46,c_38,c_47,c_37,c_48,c_4675,c_4754,c_4773,c_4784,c_5722,c_5719,c_8011])).

cnf(c_12424,plain,
    ( v2_tex_2(sK5,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12419,c_12128])).

cnf(c_13384,plain,
    ( v1_zfmisc_1(sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12874,c_50,c_12424])).

cnf(c_13389,plain,
    ( u1_struct_0(sK3(sK4,sK5)) = sK5 ),
    inference(superposition,[status(thm)],[c_7819,c_13384])).

cnf(c_13880,plain,
    ( v1_tdlat_3(sK3(sK4,sK5)) != iProver_top
    | v2_tdlat_3(sK3(sK4,sK5)) != iProver_top
    | v2_struct_0(sK3(sK4,sK5)) = iProver_top
    | v1_zfmisc_1(sK5) = iProver_top
    | l1_pre_topc(sK3(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13389,c_4333])).

cnf(c_4343,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK3(X1,X0)) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_7678,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK3(sK4,sK5)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4339,c_4343])).

cnf(c_7893,plain,
    ( v2_struct_0(sK3(sK4,sK5)) != iProver_top
    | v2_tex_2(sK5,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7678,c_43,c_44,c_46,c_47])).

cnf(c_7894,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top
    | v2_struct_0(sK3(sK4,sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7893])).

cnf(c_4344,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v1_tdlat_3(sK3(X1,X0)) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_7267,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top
    | v1_tdlat_3(sK3(sK4,sK5)) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4339,c_4344])).

cnf(c_7749,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top
    | v1_tdlat_3(sK3(sK4,sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7267,c_43,c_44,c_46,c_47])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13880,c_12424,c_8653,c_8583,c_7894,c_7749,c_50,c_46])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:21:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.51/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.51/0.99  
% 3.51/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.51/0.99  
% 3.51/0.99  ------  iProver source info
% 3.51/0.99  
% 3.51/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.51/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.51/0.99  git: non_committed_changes: false
% 3.51/0.99  git: last_make_outside_of_git: false
% 3.51/0.99  
% 3.51/0.99  ------ 
% 3.51/0.99  
% 3.51/0.99  ------ Input Options
% 3.51/0.99  
% 3.51/0.99  --out_options                           all
% 3.51/0.99  --tptp_safe_out                         true
% 3.51/0.99  --problem_path                          ""
% 3.51/0.99  --include_path                          ""
% 3.51/0.99  --clausifier                            res/vclausify_rel
% 3.51/0.99  --clausifier_options                    --mode clausify
% 3.51/0.99  --stdin                                 false
% 3.51/0.99  --stats_out                             all
% 3.51/0.99  
% 3.51/0.99  ------ General Options
% 3.51/0.99  
% 3.51/0.99  --fof                                   false
% 3.51/0.99  --time_out_real                         305.
% 3.51/0.99  --time_out_virtual                      -1.
% 3.51/0.99  --symbol_type_check                     false
% 3.51/0.99  --clausify_out                          false
% 3.51/0.99  --sig_cnt_out                           false
% 3.51/0.99  --trig_cnt_out                          false
% 3.51/0.99  --trig_cnt_out_tolerance                1.
% 3.51/0.99  --trig_cnt_out_sk_spl                   false
% 3.51/0.99  --abstr_cl_out                          false
% 3.51/0.99  
% 3.51/0.99  ------ Global Options
% 3.51/0.99  
% 3.51/0.99  --schedule                              default
% 3.51/0.99  --add_important_lit                     false
% 3.51/0.99  --prop_solver_per_cl                    1000
% 3.51/0.99  --min_unsat_core                        false
% 3.51/0.99  --soft_assumptions                      false
% 3.51/0.99  --soft_lemma_size                       3
% 3.51/0.99  --prop_impl_unit_size                   0
% 3.51/0.99  --prop_impl_unit                        []
% 3.51/0.99  --share_sel_clauses                     true
% 3.51/0.99  --reset_solvers                         false
% 3.51/0.99  --bc_imp_inh                            [conj_cone]
% 3.51/0.99  --conj_cone_tolerance                   3.
% 3.51/0.99  --extra_neg_conj                        none
% 3.51/0.99  --large_theory_mode                     true
% 3.51/0.99  --prolific_symb_bound                   200
% 3.51/0.99  --lt_threshold                          2000
% 3.51/0.99  --clause_weak_htbl                      true
% 3.51/0.99  --gc_record_bc_elim                     false
% 3.51/0.99  
% 3.51/0.99  ------ Preprocessing Options
% 3.51/0.99  
% 3.51/0.99  --preprocessing_flag                    true
% 3.51/0.99  --time_out_prep_mult                    0.1
% 3.51/0.99  --splitting_mode                        input
% 3.51/0.99  --splitting_grd                         true
% 3.51/0.99  --splitting_cvd                         false
% 3.51/0.99  --splitting_cvd_svl                     false
% 3.51/0.99  --splitting_nvd                         32
% 3.51/0.99  --sub_typing                            true
% 3.51/0.99  --prep_gs_sim                           true
% 3.51/0.99  --prep_unflatten                        true
% 3.51/0.99  --prep_res_sim                          true
% 3.51/0.99  --prep_upred                            true
% 3.51/0.99  --prep_sem_filter                       exhaustive
% 3.51/0.99  --prep_sem_filter_out                   false
% 3.51/0.99  --pred_elim                             true
% 3.51/0.99  --res_sim_input                         true
% 3.51/0.99  --eq_ax_congr_red                       true
% 3.51/0.99  --pure_diseq_elim                       true
% 3.51/0.99  --brand_transform                       false
% 3.51/0.99  --non_eq_to_eq                          false
% 3.51/0.99  --prep_def_merge                        true
% 3.51/0.99  --prep_def_merge_prop_impl              false
% 3.51/0.99  --prep_def_merge_mbd                    true
% 3.51/0.99  --prep_def_merge_tr_red                 false
% 3.51/0.99  --prep_def_merge_tr_cl                  false
% 3.51/0.99  --smt_preprocessing                     true
% 3.51/0.99  --smt_ac_axioms                         fast
% 3.51/0.99  --preprocessed_out                      false
% 3.51/0.99  --preprocessed_stats                    false
% 3.51/0.99  
% 3.51/0.99  ------ Abstraction refinement Options
% 3.51/0.99  
% 3.51/0.99  --abstr_ref                             []
% 3.51/0.99  --abstr_ref_prep                        false
% 3.51/0.99  --abstr_ref_until_sat                   false
% 3.51/0.99  --abstr_ref_sig_restrict                funpre
% 3.51/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.51/0.99  --abstr_ref_under                       []
% 3.51/0.99  
% 3.51/0.99  ------ SAT Options
% 3.51/0.99  
% 3.51/0.99  --sat_mode                              false
% 3.51/0.99  --sat_fm_restart_options                ""
% 3.51/0.99  --sat_gr_def                            false
% 3.51/0.99  --sat_epr_types                         true
% 3.51/0.99  --sat_non_cyclic_types                  false
% 3.51/0.99  --sat_finite_models                     false
% 3.51/0.99  --sat_fm_lemmas                         false
% 3.51/0.99  --sat_fm_prep                           false
% 3.51/0.99  --sat_fm_uc_incr                        true
% 3.51/0.99  --sat_out_model                         small
% 3.51/0.99  --sat_out_clauses                       false
% 3.51/0.99  
% 3.51/0.99  ------ QBF Options
% 3.51/0.99  
% 3.51/0.99  --qbf_mode                              false
% 3.51/0.99  --qbf_elim_univ                         false
% 3.51/0.99  --qbf_dom_inst                          none
% 3.51/0.99  --qbf_dom_pre_inst                      false
% 3.51/0.99  --qbf_sk_in                             false
% 3.51/0.99  --qbf_pred_elim                         true
% 3.51/0.99  --qbf_split                             512
% 3.51/0.99  
% 3.51/0.99  ------ BMC1 Options
% 3.51/0.99  
% 3.51/0.99  --bmc1_incremental                      false
% 3.51/0.99  --bmc1_axioms                           reachable_all
% 3.51/0.99  --bmc1_min_bound                        0
% 3.51/0.99  --bmc1_max_bound                        -1
% 3.51/0.99  --bmc1_max_bound_default                -1
% 3.51/0.99  --bmc1_symbol_reachability              true
% 3.51/0.99  --bmc1_property_lemmas                  false
% 3.51/0.99  --bmc1_k_induction                      false
% 3.51/0.99  --bmc1_non_equiv_states                 false
% 3.51/0.99  --bmc1_deadlock                         false
% 3.51/0.99  --bmc1_ucm                              false
% 3.51/0.99  --bmc1_add_unsat_core                   none
% 3.51/0.99  --bmc1_unsat_core_children              false
% 3.51/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.51/0.99  --bmc1_out_stat                         full
% 3.51/0.99  --bmc1_ground_init                      false
% 3.51/0.99  --bmc1_pre_inst_next_state              false
% 3.51/0.99  --bmc1_pre_inst_state                   false
% 3.51/0.99  --bmc1_pre_inst_reach_state             false
% 3.51/0.99  --bmc1_out_unsat_core                   false
% 3.51/0.99  --bmc1_aig_witness_out                  false
% 3.51/0.99  --bmc1_verbose                          false
% 3.51/0.99  --bmc1_dump_clauses_tptp                false
% 3.51/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.51/0.99  --bmc1_dump_file                        -
% 3.51/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.51/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.51/0.99  --bmc1_ucm_extend_mode                  1
% 3.51/0.99  --bmc1_ucm_init_mode                    2
% 3.51/0.99  --bmc1_ucm_cone_mode                    none
% 3.51/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.51/0.99  --bmc1_ucm_relax_model                  4
% 3.51/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.51/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.51/0.99  --bmc1_ucm_layered_model                none
% 3.51/0.99  --bmc1_ucm_max_lemma_size               10
% 3.51/0.99  
% 3.51/0.99  ------ AIG Options
% 3.51/0.99  
% 3.51/0.99  --aig_mode                              false
% 3.51/0.99  
% 3.51/0.99  ------ Instantiation Options
% 3.51/0.99  
% 3.51/0.99  --instantiation_flag                    true
% 3.51/0.99  --inst_sos_flag                         false
% 3.51/0.99  --inst_sos_phase                        true
% 3.51/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.51/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.51/0.99  --inst_lit_sel_side                     num_symb
% 3.51/0.99  --inst_solver_per_active                1400
% 3.51/0.99  --inst_solver_calls_frac                1.
% 3.51/0.99  --inst_passive_queue_type               priority_queues
% 3.51/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.51/0.99  --inst_passive_queues_freq              [25;2]
% 3.51/0.99  --inst_dismatching                      true
% 3.51/0.99  --inst_eager_unprocessed_to_passive     true
% 3.51/0.99  --inst_prop_sim_given                   true
% 3.51/0.99  --inst_prop_sim_new                     false
% 3.51/0.99  --inst_subs_new                         false
% 3.51/0.99  --inst_eq_res_simp                      false
% 3.51/0.99  --inst_subs_given                       false
% 3.51/0.99  --inst_orphan_elimination               true
% 3.51/0.99  --inst_learning_loop_flag               true
% 3.51/0.99  --inst_learning_start                   3000
% 3.51/0.99  --inst_learning_factor                  2
% 3.51/0.99  --inst_start_prop_sim_after_learn       3
% 3.51/0.99  --inst_sel_renew                        solver
% 3.51/0.99  --inst_lit_activity_flag                true
% 3.51/0.99  --inst_restr_to_given                   false
% 3.51/0.99  --inst_activity_threshold               500
% 3.51/0.99  --inst_out_proof                        true
% 3.51/0.99  
% 3.51/0.99  ------ Resolution Options
% 3.51/0.99  
% 3.51/0.99  --resolution_flag                       true
% 3.51/0.99  --res_lit_sel                           adaptive
% 3.51/0.99  --res_lit_sel_side                      none
% 3.51/0.99  --res_ordering                          kbo
% 3.51/0.99  --res_to_prop_solver                    active
% 3.51/0.99  --res_prop_simpl_new                    false
% 3.51/0.99  --res_prop_simpl_given                  true
% 3.51/0.99  --res_passive_queue_type                priority_queues
% 3.51/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.51/0.99  --res_passive_queues_freq               [15;5]
% 3.51/0.99  --res_forward_subs                      full
% 3.51/0.99  --res_backward_subs                     full
% 3.51/0.99  --res_forward_subs_resolution           true
% 3.51/0.99  --res_backward_subs_resolution          true
% 3.51/0.99  --res_orphan_elimination                true
% 3.51/0.99  --res_time_limit                        2.
% 3.51/0.99  --res_out_proof                         true
% 3.51/0.99  
% 3.51/0.99  ------ Superposition Options
% 3.51/0.99  
% 3.51/0.99  --superposition_flag                    true
% 3.51/0.99  --sup_passive_queue_type                priority_queues
% 3.51/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.51/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.51/0.99  --demod_completeness_check              fast
% 3.51/0.99  --demod_use_ground                      true
% 3.51/0.99  --sup_to_prop_solver                    passive
% 3.51/0.99  --sup_prop_simpl_new                    true
% 3.51/0.99  --sup_prop_simpl_given                  true
% 3.51/0.99  --sup_fun_splitting                     false
% 3.51/0.99  --sup_smt_interval                      50000
% 3.51/0.99  
% 3.51/0.99  ------ Superposition Simplification Setup
% 3.51/0.99  
% 3.51/0.99  --sup_indices_passive                   []
% 3.51/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.51/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.99  --sup_full_bw                           [BwDemod]
% 3.51/0.99  --sup_immed_triv                        [TrivRules]
% 3.51/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.51/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.99  --sup_immed_bw_main                     []
% 3.51/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.51/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.51/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.51/0.99  
% 3.51/0.99  ------ Combination Options
% 3.51/0.99  
% 3.51/0.99  --comb_res_mult                         3
% 3.51/0.99  --comb_sup_mult                         2
% 3.51/0.99  --comb_inst_mult                        10
% 3.51/0.99  
% 3.51/0.99  ------ Debug Options
% 3.51/0.99  
% 3.51/0.99  --dbg_backtrace                         false
% 3.51/0.99  --dbg_dump_prop_clauses                 false
% 3.51/0.99  --dbg_dump_prop_clauses_file            -
% 3.51/0.99  --dbg_out_stat                          false
% 3.51/0.99  ------ Parsing...
% 3.51/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.51/0.99  
% 3.51/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.51/0.99  
% 3.51/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.51/0.99  
% 3.51/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.51/0.99  ------ Proving...
% 3.51/0.99  ------ Problem Properties 
% 3.51/0.99  
% 3.51/0.99  
% 3.51/0.99  clauses                                 36
% 3.51/0.99  conjectures                             8
% 3.51/0.99  EPR                                     11
% 3.51/0.99  Horn                                    17
% 3.51/0.99  unary                                   11
% 3.51/0.99  binary                                  6
% 3.51/0.99  lits                                    113
% 3.51/0.99  lits eq                                 8
% 3.51/0.99  fd_pure                                 0
% 3.51/0.99  fd_pseudo                               0
% 3.51/0.99  fd_cond                                 0
% 3.51/0.99  fd_pseudo_cond                          2
% 3.51/0.99  AC symbols                              0
% 3.51/0.99  
% 3.51/0.99  ------ Schedule dynamic 5 is on 
% 3.51/0.99  
% 3.51/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.51/0.99  
% 3.51/0.99  
% 3.51/0.99  ------ 
% 3.51/0.99  Current options:
% 3.51/0.99  ------ 
% 3.51/0.99  
% 3.51/0.99  ------ Input Options
% 3.51/0.99  
% 3.51/0.99  --out_options                           all
% 3.51/0.99  --tptp_safe_out                         true
% 3.51/0.99  --problem_path                          ""
% 3.51/0.99  --include_path                          ""
% 3.51/0.99  --clausifier                            res/vclausify_rel
% 3.51/0.99  --clausifier_options                    --mode clausify
% 3.51/0.99  --stdin                                 false
% 3.51/0.99  --stats_out                             all
% 3.51/0.99  
% 3.51/0.99  ------ General Options
% 3.51/0.99  
% 3.51/0.99  --fof                                   false
% 3.51/0.99  --time_out_real                         305.
% 3.51/0.99  --time_out_virtual                      -1.
% 3.51/0.99  --symbol_type_check                     false
% 3.51/0.99  --clausify_out                          false
% 3.51/0.99  --sig_cnt_out                           false
% 3.51/0.99  --trig_cnt_out                          false
% 3.51/0.99  --trig_cnt_out_tolerance                1.
% 3.51/0.99  --trig_cnt_out_sk_spl                   false
% 3.51/0.99  --abstr_cl_out                          false
% 3.51/0.99  
% 3.51/0.99  ------ Global Options
% 3.51/0.99  
% 3.51/0.99  --schedule                              default
% 3.51/0.99  --add_important_lit                     false
% 3.51/0.99  --prop_solver_per_cl                    1000
% 3.51/0.99  --min_unsat_core                        false
% 3.51/0.99  --soft_assumptions                      false
% 3.51/0.99  --soft_lemma_size                       3
% 3.51/0.99  --prop_impl_unit_size                   0
% 3.51/0.99  --prop_impl_unit                        []
% 3.51/0.99  --share_sel_clauses                     true
% 3.51/0.99  --reset_solvers                         false
% 3.51/0.99  --bc_imp_inh                            [conj_cone]
% 3.51/0.99  --conj_cone_tolerance                   3.
% 3.51/0.99  --extra_neg_conj                        none
% 3.51/0.99  --large_theory_mode                     true
% 3.51/0.99  --prolific_symb_bound                   200
% 3.51/0.99  --lt_threshold                          2000
% 3.51/0.99  --clause_weak_htbl                      true
% 3.51/0.99  --gc_record_bc_elim                     false
% 3.51/0.99  
% 3.51/0.99  ------ Preprocessing Options
% 3.51/0.99  
% 3.51/0.99  --preprocessing_flag                    true
% 3.51/0.99  --time_out_prep_mult                    0.1
% 3.51/0.99  --splitting_mode                        input
% 3.51/0.99  --splitting_grd                         true
% 3.51/0.99  --splitting_cvd                         false
% 3.51/0.99  --splitting_cvd_svl                     false
% 3.51/0.99  --splitting_nvd                         32
% 3.51/0.99  --sub_typing                            true
% 3.51/0.99  --prep_gs_sim                           true
% 3.51/0.99  --prep_unflatten                        true
% 3.51/0.99  --prep_res_sim                          true
% 3.51/0.99  --prep_upred                            true
% 3.51/0.99  --prep_sem_filter                       exhaustive
% 3.51/0.99  --prep_sem_filter_out                   false
% 3.51/0.99  --pred_elim                             true
% 3.51/0.99  --res_sim_input                         true
% 3.51/0.99  --eq_ax_congr_red                       true
% 3.51/0.99  --pure_diseq_elim                       true
% 3.51/0.99  --brand_transform                       false
% 3.51/0.99  --non_eq_to_eq                          false
% 3.51/0.99  --prep_def_merge                        true
% 3.51/0.99  --prep_def_merge_prop_impl              false
% 3.51/0.99  --prep_def_merge_mbd                    true
% 3.51/0.99  --prep_def_merge_tr_red                 false
% 3.51/0.99  --prep_def_merge_tr_cl                  false
% 3.51/0.99  --smt_preprocessing                     true
% 3.51/0.99  --smt_ac_axioms                         fast
% 3.51/0.99  --preprocessed_out                      false
% 3.51/0.99  --preprocessed_stats                    false
% 3.51/0.99  
% 3.51/0.99  ------ Abstraction refinement Options
% 3.51/0.99  
% 3.51/0.99  --abstr_ref                             []
% 3.51/0.99  --abstr_ref_prep                        false
% 3.51/0.99  --abstr_ref_until_sat                   false
% 3.51/0.99  --abstr_ref_sig_restrict                funpre
% 3.51/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.51/0.99  --abstr_ref_under                       []
% 3.51/0.99  
% 3.51/0.99  ------ SAT Options
% 3.51/0.99  
% 3.51/0.99  --sat_mode                              false
% 3.51/0.99  --sat_fm_restart_options                ""
% 3.51/0.99  --sat_gr_def                            false
% 3.51/0.99  --sat_epr_types                         true
% 3.51/0.99  --sat_non_cyclic_types                  false
% 3.51/0.99  --sat_finite_models                     false
% 3.51/0.99  --sat_fm_lemmas                         false
% 3.51/0.99  --sat_fm_prep                           false
% 3.51/0.99  --sat_fm_uc_incr                        true
% 3.51/0.99  --sat_out_model                         small
% 3.51/0.99  --sat_out_clauses                       false
% 3.51/0.99  
% 3.51/0.99  ------ QBF Options
% 3.51/0.99  
% 3.51/0.99  --qbf_mode                              false
% 3.51/0.99  --qbf_elim_univ                         false
% 3.51/0.99  --qbf_dom_inst                          none
% 3.51/0.99  --qbf_dom_pre_inst                      false
% 3.51/0.99  --qbf_sk_in                             false
% 3.51/0.99  --qbf_pred_elim                         true
% 3.51/0.99  --qbf_split                             512
% 3.51/0.99  
% 3.51/0.99  ------ BMC1 Options
% 3.51/0.99  
% 3.51/0.99  --bmc1_incremental                      false
% 3.51/0.99  --bmc1_axioms                           reachable_all
% 3.51/0.99  --bmc1_min_bound                        0
% 3.51/0.99  --bmc1_max_bound                        -1
% 3.51/0.99  --bmc1_max_bound_default                -1
% 3.51/0.99  --bmc1_symbol_reachability              true
% 3.51/0.99  --bmc1_property_lemmas                  false
% 3.51/0.99  --bmc1_k_induction                      false
% 3.51/0.99  --bmc1_non_equiv_states                 false
% 3.51/0.99  --bmc1_deadlock                         false
% 3.51/0.99  --bmc1_ucm                              false
% 3.51/0.99  --bmc1_add_unsat_core                   none
% 3.51/0.99  --bmc1_unsat_core_children              false
% 3.51/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.51/0.99  --bmc1_out_stat                         full
% 3.51/0.99  --bmc1_ground_init                      false
% 3.51/0.99  --bmc1_pre_inst_next_state              false
% 3.51/0.99  --bmc1_pre_inst_state                   false
% 3.51/0.99  --bmc1_pre_inst_reach_state             false
% 3.51/0.99  --bmc1_out_unsat_core                   false
% 3.51/0.99  --bmc1_aig_witness_out                  false
% 3.51/0.99  --bmc1_verbose                          false
% 3.51/0.99  --bmc1_dump_clauses_tptp                false
% 3.51/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.51/0.99  --bmc1_dump_file                        -
% 3.51/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.51/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.51/0.99  --bmc1_ucm_extend_mode                  1
% 3.51/0.99  --bmc1_ucm_init_mode                    2
% 3.51/0.99  --bmc1_ucm_cone_mode                    none
% 3.51/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.51/0.99  --bmc1_ucm_relax_model                  4
% 3.51/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.51/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.51/0.99  --bmc1_ucm_layered_model                none
% 3.51/0.99  --bmc1_ucm_max_lemma_size               10
% 3.51/0.99  
% 3.51/0.99  ------ AIG Options
% 3.51/0.99  
% 3.51/0.99  --aig_mode                              false
% 3.51/0.99  
% 3.51/0.99  ------ Instantiation Options
% 3.51/0.99  
% 3.51/0.99  --instantiation_flag                    true
% 3.51/0.99  --inst_sos_flag                         false
% 3.51/0.99  --inst_sos_phase                        true
% 3.51/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.51/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.51/0.99  --inst_lit_sel_side                     none
% 3.51/0.99  --inst_solver_per_active                1400
% 3.51/0.99  --inst_solver_calls_frac                1.
% 3.51/0.99  --inst_passive_queue_type               priority_queues
% 3.51/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.51/0.99  --inst_passive_queues_freq              [25;2]
% 3.51/0.99  --inst_dismatching                      true
% 3.51/0.99  --inst_eager_unprocessed_to_passive     true
% 3.51/0.99  --inst_prop_sim_given                   true
% 3.51/0.99  --inst_prop_sim_new                     false
% 3.51/0.99  --inst_subs_new                         false
% 3.51/0.99  --inst_eq_res_simp                      false
% 3.51/0.99  --inst_subs_given                       false
% 3.51/0.99  --inst_orphan_elimination               true
% 3.51/0.99  --inst_learning_loop_flag               true
% 3.51/0.99  --inst_learning_start                   3000
% 3.51/0.99  --inst_learning_factor                  2
% 3.51/0.99  --inst_start_prop_sim_after_learn       3
% 3.51/0.99  --inst_sel_renew                        solver
% 3.51/0.99  --inst_lit_activity_flag                true
% 3.51/0.99  --inst_restr_to_given                   false
% 3.51/0.99  --inst_activity_threshold               500
% 3.51/0.99  --inst_out_proof                        true
% 3.51/0.99  
% 3.51/0.99  ------ Resolution Options
% 3.51/0.99  
% 3.51/0.99  --resolution_flag                       false
% 3.51/0.99  --res_lit_sel                           adaptive
% 3.51/0.99  --res_lit_sel_side                      none
% 3.51/0.99  --res_ordering                          kbo
% 3.51/0.99  --res_to_prop_solver                    active
% 3.51/0.99  --res_prop_simpl_new                    false
% 3.51/0.99  --res_prop_simpl_given                  true
% 3.51/0.99  --res_passive_queue_type                priority_queues
% 3.51/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.51/0.99  --res_passive_queues_freq               [15;5]
% 3.51/0.99  --res_forward_subs                      full
% 3.51/0.99  --res_backward_subs                     full
% 3.51/0.99  --res_forward_subs_resolution           true
% 3.51/0.99  --res_backward_subs_resolution          true
% 3.51/0.99  --res_orphan_elimination                true
% 3.51/0.99  --res_time_limit                        2.
% 3.51/0.99  --res_out_proof                         true
% 3.51/0.99  
% 3.51/0.99  ------ Superposition Options
% 3.51/0.99  
% 3.51/0.99  --superposition_flag                    true
% 3.51/0.99  --sup_passive_queue_type                priority_queues
% 3.51/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.51/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.51/0.99  --demod_completeness_check              fast
% 3.51/0.99  --demod_use_ground                      true
% 3.51/0.99  --sup_to_prop_solver                    passive
% 3.51/0.99  --sup_prop_simpl_new                    true
% 3.51/0.99  --sup_prop_simpl_given                  true
% 3.51/0.99  --sup_fun_splitting                     false
% 3.51/0.99  --sup_smt_interval                      50000
% 3.51/0.99  
% 3.51/0.99  ------ Superposition Simplification Setup
% 3.51/0.99  
% 3.51/0.99  --sup_indices_passive                   []
% 3.51/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.51/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.99  --sup_full_bw                           [BwDemod]
% 3.51/0.99  --sup_immed_triv                        [TrivRules]
% 3.51/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.51/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.99  --sup_immed_bw_main                     []
% 3.51/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.51/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.51/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.51/0.99  
% 3.51/0.99  ------ Combination Options
% 3.51/0.99  
% 3.51/0.99  --comb_res_mult                         3
% 3.51/0.99  --comb_sup_mult                         2
% 3.51/0.99  --comb_inst_mult                        10
% 3.51/0.99  
% 3.51/0.99  ------ Debug Options
% 3.51/0.99  
% 3.51/0.99  --dbg_backtrace                         false
% 3.51/0.99  --dbg_dump_prop_clauses                 false
% 3.51/0.99  --dbg_dump_prop_clauses_file            -
% 3.51/0.99  --dbg_out_stat                          false
% 3.51/0.99  
% 3.51/0.99  
% 3.51/0.99  
% 3.51/0.99  
% 3.51/0.99  ------ Proving...
% 3.51/0.99  
% 3.51/0.99  
% 3.51/0.99  % SZS status Theorem for theBenchmark.p
% 3.51/0.99  
% 3.51/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.51/0.99  
% 3.51/0.99  fof(f24,conjecture,(
% 3.51/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 3.51/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f25,negated_conjecture,(
% 3.51/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 3.51/0.99    inference(negated_conjecture,[],[f24])).
% 3.51/0.99  
% 3.51/0.99  fof(f58,plain,(
% 3.51/0.99    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.51/0.99    inference(ennf_transformation,[],[f25])).
% 3.51/0.99  
% 3.51/0.99  fof(f59,plain,(
% 3.51/0.99    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.51/0.99    inference(flattening,[],[f58])).
% 3.51/0.99  
% 3.51/0.99  fof(f74,plain,(
% 3.51/0.99    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.51/0.99    inference(nnf_transformation,[],[f59])).
% 3.51/0.99  
% 3.51/0.99  fof(f75,plain,(
% 3.51/0.99    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.51/0.99    inference(flattening,[],[f74])).
% 3.51/0.99  
% 3.51/0.99  fof(f77,plain,(
% 3.51/0.99    ( ! [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK5) | ~v2_tex_2(sK5,X0)) & (v1_zfmisc_1(sK5) | v2_tex_2(sK5,X0)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK5))) )),
% 3.51/0.99    introduced(choice_axiom,[])).
% 3.51/0.99  
% 3.51/0.99  fof(f76,plain,(
% 3.51/0.99    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK4)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK4)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK4) & v2_tdlat_3(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 3.51/0.99    introduced(choice_axiom,[])).
% 3.51/0.99  
% 3.51/0.99  fof(f78,plain,(
% 3.51/0.99    ((~v1_zfmisc_1(sK5) | ~v2_tex_2(sK5,sK4)) & (v1_zfmisc_1(sK5) | v2_tex_2(sK5,sK4)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) & ~v1_xboole_0(sK5)) & l1_pre_topc(sK4) & v2_tdlat_3(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 3.51/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f75,f77,f76])).
% 3.51/0.99  
% 3.51/0.99  fof(f120,plain,(
% 3.51/0.99    v1_zfmisc_1(sK5) | v2_tex_2(sK5,sK4)),
% 3.51/0.99    inference(cnf_transformation,[],[f78])).
% 3.51/0.99  
% 3.51/0.99  fof(f119,plain,(
% 3.51/0.99    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 3.51/0.99    inference(cnf_transformation,[],[f78])).
% 3.51/0.99  
% 3.51/0.99  fof(f22,axiom,(
% 3.51/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 3.51/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f26,plain,(
% 3.51/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 3.51/0.99    inference(pure_predicate_removal,[],[f22])).
% 3.51/0.99  
% 3.51/0.99  fof(f54,plain,(
% 3.51/0.99    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.51/0.99    inference(ennf_transformation,[],[f26])).
% 3.51/0.99  
% 3.51/0.99  fof(f55,plain,(
% 3.51/0.99    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.51/0.99    inference(flattening,[],[f54])).
% 3.51/0.99  
% 3.51/0.99  fof(f72,plain,(
% 3.51/0.99    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK3(X0,X1)) = X1 & m1_pre_topc(sK3(X0,X1),X0) & v1_tdlat_3(sK3(X0,X1)) & ~v2_struct_0(sK3(X0,X1))))),
% 3.51/0.99    introduced(choice_axiom,[])).
% 3.51/0.99  
% 3.51/0.99  fof(f73,plain,(
% 3.51/0.99    ! [X0] : (! [X1] : ((u1_struct_0(sK3(X0,X1)) = X1 & m1_pre_topc(sK3(X0,X1),X0) & v1_tdlat_3(sK3(X0,X1)) & ~v2_struct_0(sK3(X0,X1))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.51/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f55,f72])).
% 3.51/0.99  
% 3.51/0.99  fof(f112,plain,(
% 3.51/0.99    ( ! [X0,X1] : (u1_struct_0(sK3(X0,X1)) = X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f73])).
% 3.51/0.99  
% 3.51/0.99  fof(f114,plain,(
% 3.51/0.99    ~v2_struct_0(sK4)),
% 3.51/0.99    inference(cnf_transformation,[],[f78])).
% 3.51/0.99  
% 3.51/0.99  fof(f115,plain,(
% 3.51/0.99    v2_pre_topc(sK4)),
% 3.51/0.99    inference(cnf_transformation,[],[f78])).
% 3.51/0.99  
% 3.51/0.99  fof(f117,plain,(
% 3.51/0.99    l1_pre_topc(sK4)),
% 3.51/0.99    inference(cnf_transformation,[],[f78])).
% 3.51/0.99  
% 3.51/0.99  fof(f118,plain,(
% 3.51/0.99    ~v1_xboole_0(sK5)),
% 3.51/0.99    inference(cnf_transformation,[],[f78])).
% 3.51/0.99  
% 3.51/0.99  fof(f1,axiom,(
% 3.51/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.51/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f60,plain,(
% 3.51/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.51/0.99    inference(nnf_transformation,[],[f1])).
% 3.51/0.99  
% 3.51/0.99  fof(f61,plain,(
% 3.51/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.51/0.99    inference(rectify,[],[f60])).
% 3.51/0.99  
% 3.51/0.99  fof(f62,plain,(
% 3.51/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.51/0.99    introduced(choice_axiom,[])).
% 3.51/0.99  
% 3.51/0.99  fof(f63,plain,(
% 3.51/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.51/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f61,f62])).
% 3.51/0.99  
% 3.51/0.99  fof(f80,plain,(
% 3.51/0.99    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f63])).
% 3.51/0.99  
% 3.51/0.99  fof(f4,axiom,(
% 3.51/0.99    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.51/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f64,plain,(
% 3.51/0.99    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 3.51/0.99    inference(nnf_transformation,[],[f4])).
% 3.51/0.99  
% 3.51/0.99  fof(f84,plain,(
% 3.51/0.99    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f64])).
% 3.51/0.99  
% 3.51/0.99  fof(f21,axiom,(
% 3.51/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 3.51/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f52,plain,(
% 3.51/0.99    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 3.51/0.99    inference(ennf_transformation,[],[f21])).
% 3.51/0.99  
% 3.51/0.99  fof(f53,plain,(
% 3.51/0.99    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.51/0.99    inference(flattening,[],[f52])).
% 3.51/0.99  
% 3.51/0.99  fof(f108,plain,(
% 3.51/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f53])).
% 3.51/0.99  
% 3.51/0.99  fof(f3,axiom,(
% 3.51/0.99    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 3.51/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f82,plain,(
% 3.51/0.99    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 3.51/0.99    inference(cnf_transformation,[],[f3])).
% 3.51/0.99  
% 3.51/0.99  fof(f20,axiom,(
% 3.51/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 3.51/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f27,plain,(
% 3.51/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2))))),
% 3.51/0.99    inference(pure_predicate_removal,[],[f20])).
% 3.51/0.99  
% 3.51/0.99  fof(f50,plain,(
% 3.51/0.99    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.51/0.99    inference(ennf_transformation,[],[f27])).
% 3.51/0.99  
% 3.51/0.99  fof(f51,plain,(
% 3.51/0.99    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.51/0.99    inference(flattening,[],[f50])).
% 3.51/0.99  
% 3.51/0.99  fof(f70,plain,(
% 3.51/0.99    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & ~v2_struct_0(sK2(X0,X1))))),
% 3.51/0.99    introduced(choice_axiom,[])).
% 3.51/0.99  
% 3.51/0.99  fof(f71,plain,(
% 3.51/0.99    ! [X0] : (! [X1] : ((u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & ~v2_struct_0(sK2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.51/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f51,f70])).
% 3.51/0.99  
% 3.51/0.99  fof(f107,plain,(
% 3.51/0.99    ( ! [X0,X1] : (u1_struct_0(sK2(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f71])).
% 3.51/0.99  
% 3.51/0.99  fof(f18,axiom,(
% 3.51/0.99    ! [X0] : (l1_pre_topc(X0) => ((v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0))))),
% 3.51/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f46,plain,(
% 3.51/0.99    ! [X0] : (((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | (~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.51/0.99    inference(ennf_transformation,[],[f18])).
% 3.51/0.99  
% 3.51/0.99  fof(f47,plain,(
% 3.51/0.99    ! [X0] : ((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.51/0.99    inference(flattening,[],[f46])).
% 3.51/0.99  
% 3.51/0.99  fof(f102,plain,(
% 3.51/0.99    ( ! [X0] : (v7_struct_0(X0) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f47])).
% 3.51/0.99  
% 3.51/0.99  fof(f17,axiom,(
% 3.51/0.99    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 3.51/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f44,plain,(
% 3.51/0.99    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 3.51/0.99    inference(ennf_transformation,[],[f17])).
% 3.51/0.99  
% 3.51/0.99  fof(f45,plain,(
% 3.51/0.99    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 3.51/0.99    inference(flattening,[],[f44])).
% 3.51/0.99  
% 3.51/0.99  fof(f100,plain,(
% 3.51/0.99    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f45])).
% 3.51/0.99  
% 3.51/0.99  fof(f12,axiom,(
% 3.51/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.51/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f36,plain,(
% 3.51/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.51/0.99    inference(ennf_transformation,[],[f12])).
% 3.51/0.99  
% 3.51/0.99  fof(f95,plain,(
% 3.51/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f36])).
% 3.51/0.99  
% 3.51/0.99  fof(f14,axiom,(
% 3.51/0.99    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 3.51/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f38,plain,(
% 3.51/0.99    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 3.51/0.99    inference(ennf_transformation,[],[f14])).
% 3.51/0.99  
% 3.51/0.99  fof(f39,plain,(
% 3.51/0.99    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 3.51/0.99    inference(flattening,[],[f38])).
% 3.51/0.99  
% 3.51/0.99  fof(f97,plain,(
% 3.51/0.99    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f39])).
% 3.51/0.99  
% 3.51/0.99  fof(f109,plain,(
% 3.51/0.99    ( ! [X0,X1] : (~v2_struct_0(sK3(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f73])).
% 3.51/0.99  
% 3.51/0.99  fof(f110,plain,(
% 3.51/0.99    ( ! [X0,X1] : (v1_tdlat_3(sK3(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f73])).
% 3.51/0.99  
% 3.51/0.99  fof(f111,plain,(
% 3.51/0.99    ( ! [X0,X1] : (m1_pre_topc(sK3(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f73])).
% 3.51/0.99  
% 3.51/0.99  fof(f13,axiom,(
% 3.51/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.51/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f37,plain,(
% 3.51/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.51/0.99    inference(ennf_transformation,[],[f13])).
% 3.51/0.99  
% 3.51/0.99  fof(f96,plain,(
% 3.51/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f37])).
% 3.51/0.99  
% 3.51/0.99  fof(f19,axiom,(
% 3.51/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_tdlat_3(X1)))),
% 3.51/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f48,plain,(
% 3.51/0.99    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.51/0.99    inference(ennf_transformation,[],[f19])).
% 3.51/0.99  
% 3.51/0.99  fof(f49,plain,(
% 3.51/0.99    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.51/0.99    inference(flattening,[],[f48])).
% 3.51/0.99  
% 3.51/0.99  fof(f104,plain,(
% 3.51/0.99    ( ! [X0,X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f49])).
% 3.51/0.99  
% 3.51/0.99  fof(f116,plain,(
% 3.51/0.99    v2_tdlat_3(sK4)),
% 3.51/0.99    inference(cnf_transformation,[],[f78])).
% 3.51/0.99  
% 3.51/0.99  fof(f5,axiom,(
% 3.51/0.99    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.51/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f65,plain,(
% 3.51/0.99    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.51/0.99    inference(nnf_transformation,[],[f5])).
% 3.51/0.99  
% 3.51/0.99  fof(f66,plain,(
% 3.51/0.99    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.51/0.99    inference(flattening,[],[f65])).
% 3.51/0.99  
% 3.51/0.99  fof(f86,plain,(
% 3.51/0.99    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 != X0) )),
% 3.51/0.99    inference(cnf_transformation,[],[f66])).
% 3.51/0.99  
% 3.51/0.99  fof(f123,plain,(
% 3.51/0.99    ( ! [X1] : (r1_tarski(k1_xboole_0,k1_tarski(X1))) )),
% 3.51/0.99    inference(equality_resolution,[],[f86])).
% 3.51/0.99  
% 3.51/0.99  fof(f121,plain,(
% 3.51/0.99    ~v1_zfmisc_1(sK5) | ~v2_tex_2(sK5,sK4)),
% 3.51/0.99    inference(cnf_transformation,[],[f78])).
% 3.51/0.99  
% 3.51/0.99  fof(f106,plain,(
% 3.51/0.99    ( ! [X0,X1] : (m1_pre_topc(sK2(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f71])).
% 3.51/0.99  
% 3.51/0.99  fof(f8,axiom,(
% 3.51/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.51/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f29,plain,(
% 3.51/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.51/0.99    inference(ennf_transformation,[],[f8])).
% 3.51/0.99  
% 3.51/0.99  fof(f90,plain,(
% 3.51/0.99    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f29])).
% 3.51/0.99  
% 3.51/0.99  fof(f15,axiom,(
% 3.51/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 3.51/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f40,plain,(
% 3.51/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.51/0.99    inference(ennf_transformation,[],[f15])).
% 3.51/0.99  
% 3.51/0.99  fof(f41,plain,(
% 3.51/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.51/0.99    inference(flattening,[],[f40])).
% 3.51/0.99  
% 3.51/0.99  fof(f98,plain,(
% 3.51/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f41])).
% 3.51/0.99  
% 3.51/0.99  fof(f105,plain,(
% 3.51/0.99    ( ! [X0,X1] : (~v2_struct_0(sK2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f71])).
% 3.51/0.99  
% 3.51/0.99  fof(f16,axiom,(
% 3.51/0.99    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 3.51/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f42,plain,(
% 3.51/0.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.51/0.99    inference(ennf_transformation,[],[f16])).
% 3.51/0.99  
% 3.51/0.99  fof(f43,plain,(
% 3.51/0.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.51/0.99    inference(flattening,[],[f42])).
% 3.51/0.99  
% 3.51/0.99  fof(f99,plain,(
% 3.51/0.99    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f43])).
% 3.51/0.99  
% 3.51/0.99  fof(f7,axiom,(
% 3.51/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.51/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f28,plain,(
% 3.51/0.99    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.51/0.99    inference(ennf_transformation,[],[f7])).
% 3.51/0.99  
% 3.51/0.99  fof(f89,plain,(
% 3.51/0.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f28])).
% 3.51/0.99  
% 3.51/0.99  fof(f23,axiom,(
% 3.51/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 3.51/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f56,plain,(
% 3.51/0.99    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.51/0.99    inference(ennf_transformation,[],[f23])).
% 3.51/0.99  
% 3.51/0.99  fof(f57,plain,(
% 3.51/0.99    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.51/0.99    inference(flattening,[],[f56])).
% 3.51/0.99  
% 3.51/0.99  fof(f113,plain,(
% 3.51/0.99    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f57])).
% 3.51/0.99  
% 3.51/0.99  cnf(c_36,negated_conjecture,
% 3.51/0.99      ( v2_tex_2(sK5,sK4) | v1_zfmisc_1(sK5) ),
% 3.51/0.99      inference(cnf_transformation,[],[f120]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4340,plain,
% 3.51/0.99      ( v2_tex_2(sK5,sK4) = iProver_top
% 3.51/0.99      | v1_zfmisc_1(sK5) = iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_37,negated_conjecture,
% 3.51/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.51/0.99      inference(cnf_transformation,[],[f119]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4339,plain,
% 3.51/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_30,plain,
% 3.51/0.99      ( ~ v2_tex_2(X0,X1)
% 3.51/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.99      | ~ v2_pre_topc(X1)
% 3.51/0.99      | v2_struct_0(X1)
% 3.51/0.99      | ~ l1_pre_topc(X1)
% 3.51/0.99      | v1_xboole_0(X0)
% 3.51/0.99      | u1_struct_0(sK3(X1,X0)) = X0 ),
% 3.51/0.99      inference(cnf_transformation,[],[f112]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4346,plain,
% 3.51/0.99      ( u1_struct_0(sK3(X0,X1)) = X1
% 3.51/0.99      | v2_tex_2(X1,X0) != iProver_top
% 3.51/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.51/0.99      | v2_pre_topc(X0) != iProver_top
% 3.51/0.99      | v2_struct_0(X0) = iProver_top
% 3.51/0.99      | l1_pre_topc(X0) != iProver_top
% 3.51/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_7345,plain,
% 3.51/0.99      ( u1_struct_0(sK3(sK4,sK5)) = sK5
% 3.51/0.99      | v2_tex_2(sK5,sK4) != iProver_top
% 3.51/0.99      | v2_pre_topc(sK4) != iProver_top
% 3.51/0.99      | v2_struct_0(sK4) = iProver_top
% 3.51/0.99      | l1_pre_topc(sK4) != iProver_top
% 3.51/0.99      | v1_xboole_0(sK5) = iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_4339,c_4346]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_42,negated_conjecture,
% 3.51/0.99      ( ~ v2_struct_0(sK4) ),
% 3.51/0.99      inference(cnf_transformation,[],[f114]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_43,plain,
% 3.51/0.99      ( v2_struct_0(sK4) != iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_41,negated_conjecture,
% 3.51/0.99      ( v2_pre_topc(sK4) ),
% 3.51/0.99      inference(cnf_transformation,[],[f115]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_44,plain,
% 3.51/0.99      ( v2_pre_topc(sK4) = iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_39,negated_conjecture,
% 3.51/0.99      ( l1_pre_topc(sK4) ),
% 3.51/0.99      inference(cnf_transformation,[],[f117]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_46,plain,
% 3.51/0.99      ( l1_pre_topc(sK4) = iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_38,negated_conjecture,
% 3.51/0.99      ( ~ v1_xboole_0(sK5) ),
% 3.51/0.99      inference(cnf_transformation,[],[f118]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_47,plain,
% 3.51/0.99      ( v1_xboole_0(sK5) != iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_7813,plain,
% 3.51/0.99      ( u1_struct_0(sK3(sK4,sK5)) = sK5
% 3.51/0.99      | v2_tex_2(sK5,sK4) != iProver_top ),
% 3.51/0.99      inference(global_propositional_subsumption,
% 3.51/0.99                [status(thm)],
% 3.51/0.99                [c_7345,c_43,c_44,c_46,c_47]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_7819,plain,
% 3.51/0.99      ( u1_struct_0(sK3(sK4,sK5)) = sK5
% 3.51/0.99      | v1_zfmisc_1(sK5) = iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_4340,c_7813]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_0,plain,
% 3.51/0.99      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.51/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4,plain,
% 3.51/0.99      ( r1_tarski(k1_tarski(X0),X1) | ~ r2_hidden(X0,X1) ),
% 3.51/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_314,plain,
% 3.51/0.99      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1) ),
% 3.51/0.99      inference(prop_impl,[status(thm)],[c_4]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_315,plain,
% 3.51/0.99      ( r1_tarski(k1_tarski(X0),X1) | ~ r2_hidden(X0,X1) ),
% 3.51/0.99      inference(renaming,[status(thm)],[c_314]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_797,plain,
% 3.51/0.99      ( r1_tarski(k1_tarski(X0),X1)
% 3.51/0.99      | v1_xboole_0(X2)
% 3.51/0.99      | X1 != X2
% 3.51/0.99      | sK0(X2) != X0 ),
% 3.51/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_315]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_798,plain,
% 3.51/0.99      ( r1_tarski(k1_tarski(sK0(X0)),X0) | v1_xboole_0(X0) ),
% 3.51/0.99      inference(unflattening,[status(thm)],[c_797]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4327,plain,
% 3.51/0.99      ( r1_tarski(k1_tarski(sK0(X0)),X0) = iProver_top
% 3.51/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_798]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_29,plain,
% 3.51/0.99      ( ~ r1_tarski(X0,X1)
% 3.51/0.99      | ~ v1_zfmisc_1(X1)
% 3.51/0.99      | v1_xboole_0(X0)
% 3.51/0.99      | v1_xboole_0(X1)
% 3.51/0.99      | X1 = X0 ),
% 3.51/0.99      inference(cnf_transformation,[],[f108]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4347,plain,
% 3.51/0.99      ( X0 = X1
% 3.51/0.99      | r1_tarski(X1,X0) != iProver_top
% 3.51/0.99      | v1_zfmisc_1(X0) != iProver_top
% 3.51/0.99      | v1_xboole_0(X1) = iProver_top
% 3.51/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_5459,plain,
% 3.51/0.99      ( k1_tarski(sK0(X0)) = X0
% 3.51/0.99      | v1_zfmisc_1(X0) != iProver_top
% 3.51/0.99      | v1_xboole_0(X0) = iProver_top
% 3.51/0.99      | v1_xboole_0(k1_tarski(sK0(X0))) = iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_4327,c_4347]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_3,plain,
% 3.51/0.99      ( ~ v1_xboole_0(k1_tarski(X0)) ),
% 3.51/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4359,plain,
% 3.51/0.99      ( v1_xboole_0(k1_tarski(X0)) != iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_9072,plain,
% 3.51/0.99      ( k1_tarski(sK0(X0)) = X0
% 3.51/0.99      | v1_zfmisc_1(X0) != iProver_top
% 3.51/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.51/0.99      inference(forward_subsumption_resolution,
% 3.51/0.99                [status(thm)],
% 3.51/0.99                [c_5459,c_4359]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_9077,plain,
% 3.51/0.99      ( u1_struct_0(sK3(sK4,sK5)) = sK5
% 3.51/0.99      | k1_tarski(sK0(sK5)) = sK5
% 3.51/0.99      | v1_xboole_0(sK5) = iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_7819,c_9072]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_9099,plain,
% 3.51/0.99      ( v1_xboole_0(sK5)
% 3.51/0.99      | u1_struct_0(sK3(sK4,sK5)) = sK5
% 3.51/0.99      | k1_tarski(sK0(sK5)) = sK5 ),
% 3.51/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_9077]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_9317,plain,
% 3.51/0.99      ( k1_tarski(sK0(sK5)) = sK5 | u1_struct_0(sK3(sK4,sK5)) = sK5 ),
% 3.51/0.99      inference(global_propositional_subsumption,
% 3.51/0.99                [status(thm)],
% 3.51/0.99                [c_9077,c_38,c_9099]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_9318,plain,
% 3.51/0.99      ( u1_struct_0(sK3(sK4,sK5)) = sK5 | k1_tarski(sK0(sK5)) = sK5 ),
% 3.51/0.99      inference(renaming,[status(thm)],[c_9317]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_26,plain,
% 3.51/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.99      | v2_struct_0(X1)
% 3.51/0.99      | ~ l1_pre_topc(X1)
% 3.51/0.99      | v1_xboole_0(X0)
% 3.51/0.99      | u1_struct_0(sK2(X1,X0)) = X0 ),
% 3.51/0.99      inference(cnf_transformation,[],[f107]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4350,plain,
% 3.51/0.99      ( u1_struct_0(sK2(X0,X1)) = X1
% 3.51/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.51/0.99      | v2_struct_0(X0) = iProver_top
% 3.51/0.99      | l1_pre_topc(X0) != iProver_top
% 3.51/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_9326,plain,
% 3.51/0.99      ( u1_struct_0(sK2(sK3(sK4,sK5),X0)) = X0
% 3.51/0.99      | k1_tarski(sK0(sK5)) = sK5
% 3.51/0.99      | m1_subset_1(X0,k1_zfmisc_1(sK5)) != iProver_top
% 3.51/0.99      | v2_struct_0(sK3(sK4,sK5)) = iProver_top
% 3.51/0.99      | l1_pre_topc(sK3(sK4,sK5)) != iProver_top
% 3.51/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_9318,c_4350]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_23,plain,
% 3.51/0.99      ( ~ v1_tdlat_3(X0)
% 3.51/0.99      | ~ v2_tdlat_3(X0)
% 3.51/0.99      | ~ v2_pre_topc(X0)
% 3.51/0.99      | v2_struct_0(X0)
% 3.51/0.99      | v7_struct_0(X0)
% 3.51/0.99      | ~ l1_pre_topc(X0) ),
% 3.51/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_21,plain,
% 3.51/0.99      ( ~ v2_tdlat_3(X0) | v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 3.51/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_239,plain,
% 3.51/0.99      ( ~ v2_tdlat_3(X0)
% 3.51/0.99      | ~ v1_tdlat_3(X0)
% 3.51/0.99      | v2_struct_0(X0)
% 3.51/0.99      | v7_struct_0(X0)
% 3.51/0.99      | ~ l1_pre_topc(X0) ),
% 3.51/0.99      inference(global_propositional_subsumption,
% 3.51/0.99                [status(thm)],
% 3.51/0.99                [c_23,c_21]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_240,plain,
% 3.51/0.99      ( ~ v1_tdlat_3(X0)
% 3.51/0.99      | ~ v2_tdlat_3(X0)
% 3.51/0.99      | v2_struct_0(X0)
% 3.51/0.99      | v7_struct_0(X0)
% 3.51/0.99      | ~ l1_pre_topc(X0) ),
% 3.51/0.99      inference(renaming,[status(thm)],[c_239]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_16,plain,
% 3.51/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.51/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_18,plain,
% 3.51/0.99      ( ~ v7_struct_0(X0)
% 3.51/0.99      | v1_zfmisc_1(u1_struct_0(X0))
% 3.51/0.99      | ~ l1_struct_0(X0) ),
% 3.51/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_534,plain,
% 3.51/0.99      ( ~ v7_struct_0(X0)
% 3.51/0.99      | v1_zfmisc_1(u1_struct_0(X0))
% 3.51/0.99      | ~ l1_pre_topc(X0) ),
% 3.51/0.99      inference(resolution,[status(thm)],[c_16,c_18]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_552,plain,
% 3.51/0.99      ( ~ v1_tdlat_3(X0)
% 3.51/0.99      | ~ v2_tdlat_3(X0)
% 3.51/0.99      | v2_struct_0(X0)
% 3.51/0.99      | v1_zfmisc_1(u1_struct_0(X0))
% 3.51/0.99      | ~ l1_pre_topc(X0) ),
% 3.51/0.99      inference(resolution,[status(thm)],[c_240,c_534]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4333,plain,
% 3.51/0.99      ( v1_tdlat_3(X0) != iProver_top
% 3.51/0.99      | v2_tdlat_3(X0) != iProver_top
% 3.51/0.99      | v2_struct_0(X0) = iProver_top
% 3.51/0.99      | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top
% 3.51/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_552]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_9321,plain,
% 3.51/0.99      ( k1_tarski(sK0(sK5)) = sK5
% 3.51/0.99      | v1_tdlat_3(sK3(sK4,sK5)) != iProver_top
% 3.51/0.99      | v2_tdlat_3(sK3(sK4,sK5)) != iProver_top
% 3.51/0.99      | v2_struct_0(sK3(sK4,sK5)) = iProver_top
% 3.51/0.99      | v1_zfmisc_1(sK5) = iProver_top
% 3.51/0.99      | l1_pre_topc(sK3(sK4,sK5)) != iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_9318,c_4333]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_49,plain,
% 3.51/0.99      ( v2_tex_2(sK5,sK4) = iProver_top
% 3.51/0.99      | v1_zfmisc_1(sK5) = iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_33,plain,
% 3.51/0.99      ( ~ v2_tex_2(X0,X1)
% 3.51/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.99      | ~ v2_pre_topc(X1)
% 3.51/0.99      | v2_struct_0(X1)
% 3.51/0.99      | ~ v2_struct_0(sK3(X1,X0))
% 3.51/0.99      | ~ l1_pre_topc(X1)
% 3.51/0.99      | v1_xboole_0(X0) ),
% 3.51/0.99      inference(cnf_transformation,[],[f109]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_318,plain,
% 3.51/0.99      ( v1_zfmisc_1(sK5) | v2_tex_2(sK5,sK4) ),
% 3.51/0.99      inference(prop_impl,[status(thm)],[c_36]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_319,plain,
% 3.51/0.99      ( v2_tex_2(sK5,sK4) | v1_zfmisc_1(sK5) ),
% 3.51/0.99      inference(renaming,[status(thm)],[c_318]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_1323,plain,
% 3.51/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.99      | ~ v2_pre_topc(X1)
% 3.51/0.99      | v2_struct_0(X1)
% 3.51/0.99      | ~ v2_struct_0(sK3(X1,X0))
% 3.51/0.99      | v1_zfmisc_1(sK5)
% 3.51/0.99      | ~ l1_pre_topc(X1)
% 3.51/0.99      | v1_xboole_0(X0)
% 3.51/0.99      | sK4 != X1
% 3.51/0.99      | sK5 != X0 ),
% 3.51/0.99      inference(resolution_lifted,[status(thm)],[c_33,c_319]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_1324,plain,
% 3.51/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.51/0.99      | ~ v2_pre_topc(sK4)
% 3.51/0.99      | ~ v2_struct_0(sK3(sK4,sK5))
% 3.51/0.99      | v2_struct_0(sK4)
% 3.51/0.99      | v1_zfmisc_1(sK5)
% 3.51/0.99      | ~ l1_pre_topc(sK4)
% 3.51/0.99      | v1_xboole_0(sK5) ),
% 3.51/0.99      inference(unflattening,[status(thm)],[c_1323]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_1326,plain,
% 3.51/0.99      ( ~ v2_struct_0(sK3(sK4,sK5)) | v1_zfmisc_1(sK5) ),
% 3.51/0.99      inference(global_propositional_subsumption,
% 3.51/0.99                [status(thm)],
% 3.51/0.99                [c_1324,c_42,c_41,c_39,c_38,c_37]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_1328,plain,
% 3.51/0.99      ( v2_struct_0(sK3(sK4,sK5)) != iProver_top
% 3.51/0.99      | v1_zfmisc_1(sK5) = iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_1326]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_32,plain,
% 3.51/0.99      ( ~ v2_tex_2(X0,X1)
% 3.51/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.99      | v1_tdlat_3(sK3(X1,X0))
% 3.51/0.99      | ~ v2_pre_topc(X1)
% 3.51/0.99      | v2_struct_0(X1)
% 3.51/0.99      | ~ l1_pre_topc(X1)
% 3.51/0.99      | v1_xboole_0(X0) ),
% 3.51/0.99      inference(cnf_transformation,[],[f110]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_1337,plain,
% 3.51/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.99      | v1_tdlat_3(sK3(X1,X0))
% 3.51/0.99      | ~ v2_pre_topc(X1)
% 3.51/0.99      | v2_struct_0(X1)
% 3.51/0.99      | v1_zfmisc_1(sK5)
% 3.51/0.99      | ~ l1_pre_topc(X1)
% 3.51/0.99      | v1_xboole_0(X0)
% 3.51/0.99      | sK4 != X1
% 3.51/0.99      | sK5 != X0 ),
% 3.51/0.99      inference(resolution_lifted,[status(thm)],[c_32,c_319]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_1338,plain,
% 3.51/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.51/0.99      | v1_tdlat_3(sK3(sK4,sK5))
% 3.51/0.99      | ~ v2_pre_topc(sK4)
% 3.51/0.99      | v2_struct_0(sK4)
% 3.51/0.99      | v1_zfmisc_1(sK5)
% 3.51/0.99      | ~ l1_pre_topc(sK4)
% 3.51/0.99      | v1_xboole_0(sK5) ),
% 3.51/0.99      inference(unflattening,[status(thm)],[c_1337]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_1340,plain,
% 3.51/0.99      ( v1_tdlat_3(sK3(sK4,sK5)) | v1_zfmisc_1(sK5) ),
% 3.51/0.99      inference(global_propositional_subsumption,
% 3.51/0.99                [status(thm)],
% 3.51/0.99                [c_1338,c_42,c_41,c_39,c_38,c_37]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_1342,plain,
% 3.51/0.99      ( v1_tdlat_3(sK3(sK4,sK5)) = iProver_top
% 3.51/0.99      | v1_zfmisc_1(sK5) = iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_1340]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_31,plain,
% 3.51/0.99      ( ~ v2_tex_2(X0,X1)
% 3.51/0.99      | m1_pre_topc(sK3(X1,X0),X1)
% 3.51/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.99      | ~ v2_pre_topc(X1)
% 3.51/0.99      | v2_struct_0(X1)
% 3.51/0.99      | ~ l1_pre_topc(X1)
% 3.51/0.99      | v1_xboole_0(X0) ),
% 3.51/0.99      inference(cnf_transformation,[],[f111]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4345,plain,
% 3.51/0.99      ( v2_tex_2(X0,X1) != iProver_top
% 3.51/0.99      | m1_pre_topc(sK3(X1,X0),X1) = iProver_top
% 3.51/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.51/0.99      | v2_pre_topc(X1) != iProver_top
% 3.51/0.99      | v2_struct_0(X1) = iProver_top
% 3.51/0.99      | l1_pre_topc(X1) != iProver_top
% 3.51/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_8277,plain,
% 3.51/0.99      ( v2_tex_2(sK5,sK4) != iProver_top
% 3.51/0.99      | m1_pre_topc(sK3(sK4,sK5),sK4) = iProver_top
% 3.51/0.99      | v2_pre_topc(sK4) != iProver_top
% 3.51/0.99      | v2_struct_0(sK4) = iProver_top
% 3.51/0.99      | l1_pre_topc(sK4) != iProver_top
% 3.51/0.99      | v1_xboole_0(sK5) = iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_4339,c_4345]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_8577,plain,
% 3.51/0.99      ( v2_tex_2(sK5,sK4) != iProver_top
% 3.51/0.99      | m1_pre_topc(sK3(sK4,sK5),sK4) = iProver_top ),
% 3.51/0.99      inference(global_propositional_subsumption,
% 3.51/0.99                [status(thm)],
% 3.51/0.99                [c_8277,c_43,c_44,c_46,c_47,c_48,c_4837]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_17,plain,
% 3.51/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.51/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4354,plain,
% 3.51/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.51/0.99      | l1_pre_topc(X1) != iProver_top
% 3.51/0.99      | l1_pre_topc(X0) = iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_8583,plain,
% 3.51/0.99      ( v2_tex_2(sK5,sK4) != iProver_top
% 3.51/0.99      | l1_pre_topc(sK3(sK4,sK5)) = iProver_top
% 3.51/0.99      | l1_pre_topc(sK4) != iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_8577,c_4354]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_25,plain,
% 3.51/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.51/0.99      | ~ v2_tdlat_3(X1)
% 3.51/0.99      | v2_tdlat_3(X0)
% 3.51/0.99      | ~ v2_pre_topc(X1)
% 3.51/0.99      | v2_struct_0(X1)
% 3.51/0.99      | ~ l1_pre_topc(X1) ),
% 3.51/0.99      inference(cnf_transformation,[],[f104]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_1567,plain,
% 3.51/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.51/0.99      | ~ v2_tdlat_3(X2)
% 3.51/0.99      | ~ v2_tdlat_3(X1)
% 3.51/0.99      | v2_tdlat_3(X0)
% 3.51/0.99      | v2_struct_0(X1)
% 3.51/0.99      | ~ l1_pre_topc(X2)
% 3.51/0.99      | ~ l1_pre_topc(X1)
% 3.51/0.99      | X1 != X2 ),
% 3.51/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_25]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_1568,plain,
% 3.51/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.51/0.99      | ~ v2_tdlat_3(X1)
% 3.51/0.99      | v2_tdlat_3(X0)
% 3.51/0.99      | v2_struct_0(X1)
% 3.51/0.99      | ~ l1_pre_topc(X1) ),
% 3.51/0.99      inference(unflattening,[status(thm)],[c_1567]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4326,plain,
% 3.51/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.51/0.99      | v2_tdlat_3(X1) != iProver_top
% 3.51/0.99      | v2_tdlat_3(X0) = iProver_top
% 3.51/0.99      | v2_struct_0(X1) = iProver_top
% 3.51/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_1568]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_8584,plain,
% 3.51/0.99      ( v2_tex_2(sK5,sK4) != iProver_top
% 3.51/0.99      | v2_tdlat_3(sK3(sK4,sK5)) = iProver_top
% 3.51/0.99      | v2_tdlat_3(sK4) != iProver_top
% 3.51/0.99      | v2_struct_0(sK4) = iProver_top
% 3.51/0.99      | l1_pre_topc(sK4) != iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_8577,c_4326]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_40,negated_conjecture,
% 3.51/0.99      ( v2_tdlat_3(sK4) ),
% 3.51/0.99      inference(cnf_transformation,[],[f116]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_45,plain,
% 3.51/0.99      ( v2_tdlat_3(sK4) = iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_8652,plain,
% 3.51/0.99      ( v2_tdlat_3(sK3(sK4,sK5)) = iProver_top
% 3.51/0.99      | v2_tex_2(sK5,sK4) != iProver_top ),
% 3.51/0.99      inference(global_propositional_subsumption,
% 3.51/0.99                [status(thm)],
% 3.51/0.99                [c_8584,c_43,c_45,c_46]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_8653,plain,
% 3.51/0.99      ( v2_tex_2(sK5,sK4) != iProver_top
% 3.51/0.99      | v2_tdlat_3(sK3(sK4,sK5)) = iProver_top ),
% 3.51/0.99      inference(renaming,[status(thm)],[c_8652]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_10887,plain,
% 3.51/0.99      ( v1_zfmisc_1(sK5) = iProver_top | k1_tarski(sK0(sK5)) = sK5 ),
% 3.51/0.99      inference(global_propositional_subsumption,
% 3.51/0.99                [status(thm)],
% 3.51/0.99                [c_9321,c_43,c_45,c_46,c_49,c_1328,c_1342,c_8583,c_8584]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_10888,plain,
% 3.51/0.99      ( k1_tarski(sK0(sK5)) = sK5 | v1_zfmisc_1(sK5) = iProver_top ),
% 3.51/0.99      inference(renaming,[status(thm)],[c_10887]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_10893,plain,
% 3.51/0.99      ( k1_tarski(sK0(sK5)) = sK5 | v1_xboole_0(sK5) = iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_10888,c_9072]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_12419,plain,
% 3.51/0.99      ( k1_tarski(sK0(sK5)) = sK5 ),
% 3.51/0.99      inference(global_propositional_subsumption,
% 3.51/0.99                [status(thm)],
% 3.51/0.99                [c_9326,c_47,c_10893]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_7,plain,
% 3.51/0.99      ( r1_tarski(k1_xboole_0,k1_tarski(X0)) ),
% 3.51/0.99      inference(cnf_transformation,[],[f123]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4357,plain,
% 3.51/0.99      ( r1_tarski(k1_xboole_0,k1_tarski(X0)) = iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_12472,plain,
% 3.51/0.99      ( r1_tarski(k1_xboole_0,sK5) = iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_12419,c_4357]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_12874,plain,
% 3.51/0.99      ( sK5 = k1_xboole_0
% 3.51/0.99      | v1_zfmisc_1(sK5) != iProver_top
% 3.51/0.99      | v1_xboole_0(sK5) = iProver_top
% 3.51/0.99      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_12472,c_4347]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_35,negated_conjecture,
% 3.51/0.99      ( ~ v2_tex_2(sK5,sK4) | ~ v1_zfmisc_1(sK5) ),
% 3.51/0.99      inference(cnf_transformation,[],[f121]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_50,plain,
% 3.51/0.99      ( v2_tex_2(sK5,sK4) != iProver_top
% 3.51/0.99      | v1_zfmisc_1(sK5) != iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_27,plain,
% 3.51/0.99      ( m1_pre_topc(sK2(X0,X1),X0)
% 3.51/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.51/0.99      | v2_struct_0(X0)
% 3.51/0.99      | ~ l1_pre_topc(X0)
% 3.51/0.99      | v1_xboole_0(X1) ),
% 3.51/0.99      inference(cnf_transformation,[],[f106]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4349,plain,
% 3.51/0.99      ( m1_pre_topc(sK2(X0,X1),X0) = iProver_top
% 3.51/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.51/0.99      | v2_struct_0(X0) = iProver_top
% 3.51/0.99      | l1_pre_topc(X0) != iProver_top
% 3.51/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_6015,plain,
% 3.51/0.99      ( m1_pre_topc(sK2(sK4,sK5),sK4) = iProver_top
% 3.51/0.99      | v2_struct_0(sK4) = iProver_top
% 3.51/0.99      | l1_pre_topc(sK4) != iProver_top
% 3.51/0.99      | v1_xboole_0(sK5) = iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_4339,c_4349]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_48,plain,
% 3.51/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4781,plain,
% 3.51/0.99      ( m1_pre_topc(sK2(X0,sK5),X0)
% 3.51/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 3.51/0.99      | v2_struct_0(X0)
% 3.51/0.99      | ~ l1_pre_topc(X0)
% 3.51/0.99      | v1_xboole_0(sK5) ),
% 3.51/0.99      inference(instantiation,[status(thm)],[c_27]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4782,plain,
% 3.51/0.99      ( m1_pre_topc(sK2(X0,sK5),X0) = iProver_top
% 3.51/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.51/0.99      | v2_struct_0(X0) = iProver_top
% 3.51/0.99      | l1_pre_topc(X0) != iProver_top
% 3.51/0.99      | v1_xboole_0(sK5) = iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_4781]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4784,plain,
% 3.51/0.99      ( m1_pre_topc(sK2(sK4,sK5),sK4) = iProver_top
% 3.51/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.51/0.99      | v2_struct_0(sK4) = iProver_top
% 3.51/0.99      | l1_pre_topc(sK4) != iProver_top
% 3.51/0.99      | v1_xboole_0(sK5) = iProver_top ),
% 3.51/0.99      inference(instantiation,[status(thm)],[c_4782]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_6277,plain,
% 3.51/0.99      ( m1_pre_topc(sK2(sK4,sK5),sK4) = iProver_top ),
% 3.51/0.99      inference(global_propositional_subsumption,
% 3.51/0.99                [status(thm)],
% 3.51/0.99                [c_6015,c_43,c_46,c_47,c_48,c_4784]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_5869,plain,
% 3.51/0.99      ( u1_struct_0(sK2(sK4,sK5)) = sK5
% 3.51/0.99      | v2_struct_0(sK4) = iProver_top
% 3.51/0.99      | l1_pre_topc(sK4) != iProver_top
% 3.51/0.99      | v1_xboole_0(sK5) = iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_4339,c_4350]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4771,plain,
% 3.51/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 3.51/0.99      | v2_struct_0(X0)
% 3.51/0.99      | ~ l1_pre_topc(X0)
% 3.51/0.99      | v1_xboole_0(sK5)
% 3.51/0.99      | u1_struct_0(sK2(X0,sK5)) = sK5 ),
% 3.51/0.99      inference(instantiation,[status(thm)],[c_26]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4773,plain,
% 3.51/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.51/0.99      | v2_struct_0(sK4)
% 3.51/0.99      | ~ l1_pre_topc(sK4)
% 3.51/0.99      | v1_xboole_0(sK5)
% 3.51/0.99      | u1_struct_0(sK2(sK4,sK5)) = sK5 ),
% 3.51/0.99      inference(instantiation,[status(thm)],[c_4771]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_6110,plain,
% 3.51/0.99      ( u1_struct_0(sK2(sK4,sK5)) = sK5 ),
% 3.51/0.99      inference(global_propositional_subsumption,
% 3.51/0.99                [status(thm)],
% 3.51/0.99                [c_5869,c_42,c_39,c_38,c_37,c_4773]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_11,plain,
% 3.51/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.51/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_785,plain,
% 3.51/0.99      ( m1_subset_1(X0,X1) | v1_xboole_0(X2) | X1 != X2 | sK0(X2) != X0 ),
% 3.51/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_11]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_786,plain,
% 3.51/0.99      ( m1_subset_1(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.51/0.99      inference(unflattening,[status(thm)],[c_785]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4328,plain,
% 3.51/0.99      ( m1_subset_1(sK0(X0),X0) = iProver_top
% 3.51/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_786]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_19,plain,
% 3.51/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.51/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.51/0.99      | m1_subset_1(X2,u1_struct_0(X1))
% 3.51/0.99      | v2_struct_0(X1)
% 3.51/0.99      | v2_struct_0(X0)
% 3.51/0.99      | ~ l1_pre_topc(X1) ),
% 3.51/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4353,plain,
% 3.51/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.51/0.99      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.51/0.99      | m1_subset_1(X2,u1_struct_0(X1)) = iProver_top
% 3.51/0.99      | v2_struct_0(X0) = iProver_top
% 3.51/0.99      | v2_struct_0(X1) = iProver_top
% 3.51/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_7001,plain,
% 3.51/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.51/0.99      | m1_subset_1(sK0(u1_struct_0(X0)),u1_struct_0(X1)) = iProver_top
% 3.51/0.99      | v2_struct_0(X0) = iProver_top
% 3.51/0.99      | v2_struct_0(X1) = iProver_top
% 3.51/0.99      | l1_pre_topc(X1) != iProver_top
% 3.51/0.99      | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_4328,c_4353]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_11440,plain,
% 3.51/0.99      ( m1_pre_topc(sK2(sK4,sK5),X0) != iProver_top
% 3.51/0.99      | m1_subset_1(sK0(sK5),u1_struct_0(X0)) = iProver_top
% 3.51/0.99      | v2_struct_0(X0) = iProver_top
% 3.51/0.99      | v2_struct_0(sK2(sK4,sK5)) = iProver_top
% 3.51/0.99      | l1_pre_topc(X0) != iProver_top
% 3.51/0.99      | v1_xboole_0(u1_struct_0(sK2(sK4,sK5))) = iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_6110,c_7001]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_11526,plain,
% 3.51/0.99      ( m1_pre_topc(sK2(sK4,sK5),X0) != iProver_top
% 3.51/0.99      | m1_subset_1(sK0(sK5),u1_struct_0(X0)) = iProver_top
% 3.51/0.99      | v2_struct_0(X0) = iProver_top
% 3.51/0.99      | v2_struct_0(sK2(sK4,sK5)) = iProver_top
% 3.51/0.99      | l1_pre_topc(X0) != iProver_top
% 3.51/0.99      | v1_xboole_0(sK5) = iProver_top ),
% 3.51/0.99      inference(light_normalisation,[status(thm)],[c_11440,c_6110]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_28,plain,
% 3.51/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.99      | v2_struct_0(X1)
% 3.51/0.99      | ~ v2_struct_0(sK2(X1,X0))
% 3.51/0.99      | ~ l1_pre_topc(X1)
% 3.51/0.99      | v1_xboole_0(X0) ),
% 3.51/0.99      inference(cnf_transformation,[],[f105]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4751,plain,
% 3.51/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 3.51/0.99      | v2_struct_0(X0)
% 3.51/0.99      | ~ v2_struct_0(sK2(X0,sK5))
% 3.51/0.99      | ~ l1_pre_topc(X0)
% 3.51/0.99      | v1_xboole_0(sK5) ),
% 3.51/0.99      inference(instantiation,[status(thm)],[c_28]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4752,plain,
% 3.51/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.51/0.99      | v2_struct_0(X0) = iProver_top
% 3.51/0.99      | v2_struct_0(sK2(X0,sK5)) != iProver_top
% 3.51/0.99      | l1_pre_topc(X0) != iProver_top
% 3.51/0.99      | v1_xboole_0(sK5) = iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_4751]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4754,plain,
% 3.51/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.51/0.99      | v2_struct_0(sK2(sK4,sK5)) != iProver_top
% 3.51/0.99      | v2_struct_0(sK4) = iProver_top
% 3.51/0.99      | l1_pre_topc(sK4) != iProver_top
% 3.51/0.99      | v1_xboole_0(sK5) = iProver_top ),
% 3.51/0.99      inference(instantiation,[status(thm)],[c_4752]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_11623,plain,
% 3.51/0.99      ( l1_pre_topc(X0) != iProver_top
% 3.51/0.99      | m1_pre_topc(sK2(sK4,sK5),X0) != iProver_top
% 3.51/0.99      | m1_subset_1(sK0(sK5),u1_struct_0(X0)) = iProver_top
% 3.51/0.99      | v2_struct_0(X0) = iProver_top ),
% 3.51/0.99      inference(global_propositional_subsumption,
% 3.51/0.99                [status(thm)],
% 3.51/0.99                [c_11526,c_43,c_46,c_47,c_48,c_4754]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_11624,plain,
% 3.51/0.99      ( m1_pre_topc(sK2(sK4,sK5),X0) != iProver_top
% 3.51/0.99      | m1_subset_1(sK0(sK5),u1_struct_0(X0)) = iProver_top
% 3.51/0.99      | v2_struct_0(X0) = iProver_top
% 3.51/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.51/0.99      inference(renaming,[status(thm)],[c_11623]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_11633,plain,
% 3.51/0.99      ( m1_subset_1(sK0(sK5),u1_struct_0(sK4)) = iProver_top
% 3.51/0.99      | v2_struct_0(sK4) = iProver_top
% 3.51/0.99      | l1_pre_topc(sK4) != iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_6277,c_11624]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4674,plain,
% 3.51/0.99      ( m1_subset_1(sK0(sK5),sK5) | v1_xboole_0(sK5) ),
% 3.51/0.99      inference(instantiation,[status(thm)],[c_786]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4675,plain,
% 3.51/0.99      ( m1_subset_1(sK0(sK5),sK5) = iProver_top
% 3.51/0.99      | v1_xboole_0(sK5) = iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_4674]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_3481,plain,
% 3.51/0.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.51/0.99      theory(equality) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4874,plain,
% 3.51/0.99      ( m1_subset_1(X0,X1)
% 3.51/0.99      | ~ m1_subset_1(sK0(sK5),sK5)
% 3.51/0.99      | X0 != sK0(sK5)
% 3.51/0.99      | X1 != sK5 ),
% 3.51/0.99      inference(instantiation,[status(thm)],[c_3481]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_5129,plain,
% 3.51/0.99      ( m1_subset_1(X0,u1_struct_0(sK2(X1,sK5)))
% 3.51/0.99      | ~ m1_subset_1(sK0(sK5),sK5)
% 3.51/0.99      | X0 != sK0(sK5)
% 3.51/0.99      | u1_struct_0(sK2(X1,sK5)) != sK5 ),
% 3.51/0.99      inference(instantiation,[status(thm)],[c_4874]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_5718,plain,
% 3.51/0.99      ( m1_subset_1(sK0(sK5),u1_struct_0(sK2(X0,sK5)))
% 3.51/0.99      | ~ m1_subset_1(sK0(sK5),sK5)
% 3.51/0.99      | u1_struct_0(sK2(X0,sK5)) != sK5
% 3.51/0.99      | sK0(sK5) != sK0(sK5) ),
% 3.51/0.99      inference(instantiation,[status(thm)],[c_5129]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_5720,plain,
% 3.51/0.99      ( u1_struct_0(sK2(X0,sK5)) != sK5
% 3.51/0.99      | sK0(sK5) != sK0(sK5)
% 3.51/0.99      | m1_subset_1(sK0(sK5),u1_struct_0(sK2(X0,sK5))) = iProver_top
% 3.51/0.99      | m1_subset_1(sK0(sK5),sK5) != iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_5718]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_5722,plain,
% 3.51/0.99      ( u1_struct_0(sK2(sK4,sK5)) != sK5
% 3.51/0.99      | sK0(sK5) != sK0(sK5)
% 3.51/0.99      | m1_subset_1(sK0(sK5),u1_struct_0(sK2(sK4,sK5))) = iProver_top
% 3.51/0.99      | m1_subset_1(sK0(sK5),sK5) != iProver_top ),
% 3.51/0.99      inference(instantiation,[status(thm)],[c_5720]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_3474,plain,( X0 = X0 ),theory(equality) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_5719,plain,
% 3.51/0.99      ( sK0(sK5) = sK0(sK5) ),
% 3.51/0.99      inference(instantiation,[status(thm)],[c_3474]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4939,plain,
% 3.51/0.99      ( ~ m1_pre_topc(sK2(X0,sK5),X0)
% 3.51/0.99      | m1_subset_1(X1,u1_struct_0(X0))
% 3.51/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2(X0,sK5)))
% 3.51/0.99      | v2_struct_0(X0)
% 3.51/0.99      | v2_struct_0(sK2(X0,sK5))
% 3.51/0.99      | ~ l1_pre_topc(X0) ),
% 3.51/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_8008,plain,
% 3.51/0.99      ( ~ m1_pre_topc(sK2(X0,sK5),X0)
% 3.51/0.99      | m1_subset_1(sK0(sK5),u1_struct_0(X0))
% 3.51/0.99      | ~ m1_subset_1(sK0(sK5),u1_struct_0(sK2(X0,sK5)))
% 3.51/0.99      | v2_struct_0(X0)
% 3.51/0.99      | v2_struct_0(sK2(X0,sK5))
% 3.51/0.99      | ~ l1_pre_topc(X0) ),
% 3.51/0.99      inference(instantiation,[status(thm)],[c_4939]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_8009,plain,
% 3.51/0.99      ( m1_pre_topc(sK2(X0,sK5),X0) != iProver_top
% 3.51/0.99      | m1_subset_1(sK0(sK5),u1_struct_0(X0)) = iProver_top
% 3.51/0.99      | m1_subset_1(sK0(sK5),u1_struct_0(sK2(X0,sK5))) != iProver_top
% 3.51/0.99      | v2_struct_0(X0) = iProver_top
% 3.51/0.99      | v2_struct_0(sK2(X0,sK5)) = iProver_top
% 3.51/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_8008]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_8011,plain,
% 3.51/0.99      ( m1_pre_topc(sK2(sK4,sK5),sK4) != iProver_top
% 3.51/0.99      | m1_subset_1(sK0(sK5),u1_struct_0(sK2(sK4,sK5))) != iProver_top
% 3.51/0.99      | m1_subset_1(sK0(sK5),u1_struct_0(sK4)) = iProver_top
% 3.51/0.99      | v2_struct_0(sK2(sK4,sK5)) = iProver_top
% 3.51/0.99      | v2_struct_0(sK4) = iProver_top
% 3.51/0.99      | l1_pre_topc(sK4) != iProver_top ),
% 3.51/0.99      inference(instantiation,[status(thm)],[c_8009]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_11669,plain,
% 3.51/0.99      ( m1_subset_1(sK0(sK5),u1_struct_0(sK4)) = iProver_top ),
% 3.51/0.99      inference(global_propositional_subsumption,
% 3.51/0.99                [status(thm)],
% 3.51/0.99                [c_11633,c_42,c_43,c_39,c_46,c_38,c_47,c_37,c_48,c_4675,
% 3.51/0.99                 c_4754,c_4773,c_4784,c_5722,c_5719,c_8011]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_20,plain,
% 3.51/0.99      ( ~ m1_subset_1(X0,X1)
% 3.51/0.99      | v1_xboole_0(X1)
% 3.51/0.99      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 3.51/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4352,plain,
% 3.51/0.99      ( k6_domain_1(X0,X1) = k1_tarski(X1)
% 3.51/0.99      | m1_subset_1(X1,X0) != iProver_top
% 3.51/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_11676,plain,
% 3.51/0.99      ( k6_domain_1(u1_struct_0(sK4),sK0(sK5)) = k1_tarski(sK0(sK5))
% 3.51/0.99      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_11669,c_4352]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_7002,plain,
% 3.51/0.99      ( m1_pre_topc(sK2(sK4,sK5),X0) != iProver_top
% 3.51/0.99      | m1_subset_1(X1,u1_struct_0(X0)) = iProver_top
% 3.51/0.99      | m1_subset_1(X1,sK5) != iProver_top
% 3.51/0.99      | v2_struct_0(X0) = iProver_top
% 3.51/0.99      | v2_struct_0(sK2(sK4,sK5)) = iProver_top
% 3.51/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_6110,c_4353]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_8020,plain,
% 3.51/0.99      ( v2_struct_0(X0) = iProver_top
% 3.51/0.99      | m1_subset_1(X1,sK5) != iProver_top
% 3.51/0.99      | m1_subset_1(X1,u1_struct_0(X0)) = iProver_top
% 3.51/0.99      | m1_pre_topc(sK2(sK4,sK5),X0) != iProver_top
% 3.51/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.51/0.99      inference(global_propositional_subsumption,
% 3.51/0.99                [status(thm)],
% 3.51/0.99                [c_7002,c_43,c_46,c_47,c_48,c_4754]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_8021,plain,
% 3.51/0.99      ( m1_pre_topc(sK2(sK4,sK5),X0) != iProver_top
% 3.51/0.99      | m1_subset_1(X1,u1_struct_0(X0)) = iProver_top
% 3.51/0.99      | m1_subset_1(X1,sK5) != iProver_top
% 3.51/0.99      | v2_struct_0(X0) = iProver_top
% 3.51/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.51/0.99      inference(renaming,[status(thm)],[c_8020]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_8031,plain,
% 3.51/0.99      ( m1_subset_1(X0,u1_struct_0(sK4)) = iProver_top
% 3.51/0.99      | m1_subset_1(X0,sK5) != iProver_top
% 3.51/0.99      | v2_struct_0(sK4) = iProver_top
% 3.51/0.99      | l1_pre_topc(sK4) != iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_6277,c_8021]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_8136,plain,
% 3.51/0.99      ( m1_subset_1(X0,u1_struct_0(sK4)) = iProver_top
% 3.51/0.99      | m1_subset_1(X0,sK5) != iProver_top ),
% 3.51/0.99      inference(global_propositional_subsumption,
% 3.51/0.99                [status(thm)],
% 3.51/0.99                [c_8031,c_43,c_46]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_8145,plain,
% 3.51/0.99      ( k6_domain_1(u1_struct_0(sK4),X0) = k1_tarski(X0)
% 3.51/0.99      | m1_subset_1(X0,sK5) != iProver_top
% 3.51/0.99      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_8136,c_4352]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_10,plain,
% 3.51/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.51/0.99      | ~ v1_xboole_0(X1)
% 3.51/0.99      | v1_xboole_0(X0) ),
% 3.51/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4690,plain,
% 3.51/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
% 3.51/0.99      | ~ v1_xboole_0(X0)
% 3.51/0.99      | v1_xboole_0(sK5) ),
% 3.51/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4888,plain,
% 3.51/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.51/0.99      | ~ v1_xboole_0(u1_struct_0(sK4))
% 3.51/0.99      | v1_xboole_0(sK5) ),
% 3.51/0.99      inference(instantiation,[status(thm)],[c_4690]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4889,plain,
% 3.51/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.51/0.99      | v1_xboole_0(u1_struct_0(sK4)) != iProver_top
% 3.51/0.99      | v1_xboole_0(sK5) = iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_4888]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_8993,plain,
% 3.51/0.99      ( m1_subset_1(X0,sK5) != iProver_top
% 3.51/0.99      | k6_domain_1(u1_struct_0(sK4),X0) = k1_tarski(X0) ),
% 3.51/0.99      inference(global_propositional_subsumption,
% 3.51/0.99                [status(thm)],
% 3.51/0.99                [c_8145,c_47,c_48,c_4889]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_8994,plain,
% 3.51/0.99      ( k6_domain_1(u1_struct_0(sK4),X0) = k1_tarski(X0)
% 3.51/0.99      | m1_subset_1(X0,sK5) != iProver_top ),
% 3.51/0.99      inference(renaming,[status(thm)],[c_8993]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_9002,plain,
% 3.51/0.99      ( k6_domain_1(u1_struct_0(sK4),sK0(sK5)) = k1_tarski(sK0(sK5))
% 3.51/0.99      | v1_xboole_0(sK5) = iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_4328,c_8994]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_11921,plain,
% 3.51/0.99      ( k6_domain_1(u1_struct_0(sK4),sK0(sK5)) = k1_tarski(sK0(sK5)) ),
% 3.51/0.99      inference(global_propositional_subsumption,
% 3.51/0.99                [status(thm)],
% 3.51/0.99                [c_11676,c_47,c_9002]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_34,plain,
% 3.51/0.99      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 3.51/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.51/0.99      | ~ v2_pre_topc(X0)
% 3.51/0.99      | v2_struct_0(X0)
% 3.51/0.99      | ~ l1_pre_topc(X0) ),
% 3.51/0.99      inference(cnf_transformation,[],[f113]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4342,plain,
% 3.51/0.99      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) = iProver_top
% 3.51/0.99      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.51/0.99      | v2_pre_topc(X0) != iProver_top
% 3.51/0.99      | v2_struct_0(X0) = iProver_top
% 3.51/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_11924,plain,
% 3.51/0.99      ( v2_tex_2(k1_tarski(sK0(sK5)),sK4) = iProver_top
% 3.51/0.99      | m1_subset_1(sK0(sK5),u1_struct_0(sK4)) != iProver_top
% 3.51/0.99      | v2_pre_topc(sK4) != iProver_top
% 3.51/0.99      | v2_struct_0(sK4) = iProver_top
% 3.51/0.99      | l1_pre_topc(sK4) != iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_11921,c_4342]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_12128,plain,
% 3.51/0.99      ( v2_tex_2(k1_tarski(sK0(sK5)),sK4) = iProver_top ),
% 3.51/0.99      inference(global_propositional_subsumption,
% 3.51/0.99                [status(thm)],
% 3.51/0.99                [c_11924,c_42,c_43,c_44,c_39,c_46,c_38,c_47,c_37,c_48,
% 3.51/0.99                 c_4675,c_4754,c_4773,c_4784,c_5722,c_5719,c_8011]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_12424,plain,
% 3.51/0.99      ( v2_tex_2(sK5,sK4) = iProver_top ),
% 3.51/0.99      inference(demodulation,[status(thm)],[c_12419,c_12128]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_13384,plain,
% 3.51/0.99      ( v1_zfmisc_1(sK5) != iProver_top ),
% 3.51/0.99      inference(global_propositional_subsumption,
% 3.51/0.99                [status(thm)],
% 3.51/0.99                [c_12874,c_50,c_12424]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_13389,plain,
% 3.51/0.99      ( u1_struct_0(sK3(sK4,sK5)) = sK5 ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_7819,c_13384]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_13880,plain,
% 3.51/0.99      ( v1_tdlat_3(sK3(sK4,sK5)) != iProver_top
% 3.51/0.99      | v2_tdlat_3(sK3(sK4,sK5)) != iProver_top
% 3.51/0.99      | v2_struct_0(sK3(sK4,sK5)) = iProver_top
% 3.51/0.99      | v1_zfmisc_1(sK5) = iProver_top
% 3.51/0.99      | l1_pre_topc(sK3(sK4,sK5)) != iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_13389,c_4333]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4343,plain,
% 3.51/0.99      ( v2_tex_2(X0,X1) != iProver_top
% 3.51/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.51/0.99      | v2_pre_topc(X1) != iProver_top
% 3.51/0.99      | v2_struct_0(X1) = iProver_top
% 3.51/0.99      | v2_struct_0(sK3(X1,X0)) != iProver_top
% 3.51/0.99      | l1_pre_topc(X1) != iProver_top
% 3.51/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_7678,plain,
% 3.51/0.99      ( v2_tex_2(sK5,sK4) != iProver_top
% 3.51/0.99      | v2_pre_topc(sK4) != iProver_top
% 3.51/0.99      | v2_struct_0(sK3(sK4,sK5)) != iProver_top
% 3.51/0.99      | v2_struct_0(sK4) = iProver_top
% 3.51/0.99      | l1_pre_topc(sK4) != iProver_top
% 3.51/0.99      | v1_xboole_0(sK5) = iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_4339,c_4343]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_7893,plain,
% 3.51/0.99      ( v2_struct_0(sK3(sK4,sK5)) != iProver_top
% 3.51/0.99      | v2_tex_2(sK5,sK4) != iProver_top ),
% 3.51/0.99      inference(global_propositional_subsumption,
% 3.51/0.99                [status(thm)],
% 3.51/0.99                [c_7678,c_43,c_44,c_46,c_47]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_7894,plain,
% 3.51/0.99      ( v2_tex_2(sK5,sK4) != iProver_top
% 3.51/0.99      | v2_struct_0(sK3(sK4,sK5)) != iProver_top ),
% 3.51/0.99      inference(renaming,[status(thm)],[c_7893]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_4344,plain,
% 3.51/0.99      ( v2_tex_2(X0,X1) != iProver_top
% 3.51/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.51/0.99      | v1_tdlat_3(sK3(X1,X0)) = iProver_top
% 3.51/0.99      | v2_pre_topc(X1) != iProver_top
% 3.51/0.99      | v2_struct_0(X1) = iProver_top
% 3.51/0.99      | l1_pre_topc(X1) != iProver_top
% 3.51/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_7267,plain,
% 3.51/0.99      ( v2_tex_2(sK5,sK4) != iProver_top
% 3.51/0.99      | v1_tdlat_3(sK3(sK4,sK5)) = iProver_top
% 3.51/0.99      | v2_pre_topc(sK4) != iProver_top
% 3.51/0.99      | v2_struct_0(sK4) = iProver_top
% 3.51/0.99      | l1_pre_topc(sK4) != iProver_top
% 3.51/0.99      | v1_xboole_0(sK5) = iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_4339,c_4344]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_7749,plain,
% 3.51/0.99      ( v2_tex_2(sK5,sK4) != iProver_top
% 3.51/0.99      | v1_tdlat_3(sK3(sK4,sK5)) = iProver_top ),
% 3.51/0.99      inference(global_propositional_subsumption,
% 3.51/0.99                [status(thm)],
% 3.51/0.99                [c_7267,c_43,c_44,c_46,c_47]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(contradiction,plain,
% 3.51/0.99      ( $false ),
% 3.51/0.99      inference(minisat,
% 3.51/0.99                [status(thm)],
% 3.51/0.99                [c_13880,c_12424,c_8653,c_8583,c_7894,c_7749,c_50,c_46]) ).
% 3.51/0.99  
% 3.51/0.99  
% 3.51/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.51/0.99  
% 3.51/0.99  ------                               Statistics
% 3.51/0.99  
% 3.51/0.99  ------ General
% 3.51/0.99  
% 3.51/0.99  abstr_ref_over_cycles:                  0
% 3.51/0.99  abstr_ref_under_cycles:                 0
% 3.51/0.99  gc_basic_clause_elim:                   0
% 3.51/0.99  forced_gc_time:                         0
% 3.51/0.99  parsing_time:                           0.01
% 3.51/0.99  unif_index_cands_time:                  0.
% 3.51/0.99  unif_index_add_time:                    0.
% 3.51/0.99  orderings_time:                         0.
% 3.51/0.99  out_proof_time:                         0.018
% 3.51/0.99  total_time:                             0.353
% 3.51/0.99  num_of_symbols:                         58
% 3.51/0.99  num_of_terms:                           9094
% 3.51/0.99  
% 3.51/0.99  ------ Preprocessing
% 3.51/0.99  
% 3.51/0.99  num_of_splits:                          0
% 3.51/0.99  num_of_split_atoms:                     0
% 3.51/0.99  num_of_reused_defs:                     0
% 3.51/0.99  num_eq_ax_congr_red:                    33
% 3.51/0.99  num_of_sem_filtered_clauses:            1
% 3.51/0.99  num_of_subtypes:                        0
% 3.51/0.99  monotx_restored_types:                  0
% 3.51/0.99  sat_num_of_epr_types:                   0
% 3.51/0.99  sat_num_of_non_cyclic_types:            0
% 3.51/0.99  sat_guarded_non_collapsed_types:        0
% 3.51/0.99  num_pure_diseq_elim:                    0
% 3.51/0.99  simp_replaced_by:                       0
% 3.51/0.99  res_preprocessed:                       186
% 3.51/0.99  prep_upred:                             0
% 3.51/0.99  prep_unflattend:                        154
% 3.51/0.99  smt_new_axioms:                         0
% 3.51/0.99  pred_elim_cands:                        11
% 3.51/0.99  pred_elim:                              4
% 3.51/0.99  pred_elim_cl:                           5
% 3.51/0.99  pred_elim_cycles:                       18
% 3.51/0.99  merged_defs:                            10
% 3.51/0.99  merged_defs_ncl:                        0
% 3.51/0.99  bin_hyper_res:                          10
% 3.51/0.99  prep_cycles:                            4
% 3.51/0.99  pred_elim_time:                         0.045
% 3.51/0.99  splitting_time:                         0.
% 3.51/0.99  sem_filter_time:                        0.
% 3.51/0.99  monotx_time:                            0.001
% 3.51/0.99  subtype_inf_time:                       0.
% 3.51/0.99  
% 3.51/0.99  ------ Problem properties
% 3.51/0.99  
% 3.51/0.99  clauses:                                36
% 3.51/0.99  conjectures:                            8
% 3.51/0.99  epr:                                    11
% 3.51/0.99  horn:                                   17
% 3.51/0.99  ground:                                 8
% 3.51/0.99  unary:                                  11
% 3.51/0.99  binary:                                 6
% 3.51/0.99  lits:                                   113
% 3.51/0.99  lits_eq:                                8
% 3.51/0.99  fd_pure:                                0
% 3.51/0.99  fd_pseudo:                              0
% 3.51/0.99  fd_cond:                                0
% 3.51/0.99  fd_pseudo_cond:                         2
% 3.51/0.99  ac_symbols:                             0
% 3.51/0.99  
% 3.51/0.99  ------ Propositional Solver
% 3.51/0.99  
% 3.51/0.99  prop_solver_calls:                      29
% 3.51/0.99  prop_fast_solver_calls:                 2602
% 3.51/0.99  smt_solver_calls:                       0
% 3.51/0.99  smt_fast_solver_calls:                  0
% 3.51/0.99  prop_num_of_clauses:                    4628
% 3.51/0.99  prop_preprocess_simplified:             10756
% 3.51/0.99  prop_fo_subsumed:                       242
% 3.51/0.99  prop_solver_time:                       0.
% 3.51/0.99  smt_solver_time:                        0.
% 3.51/0.99  smt_fast_solver_time:                   0.
% 3.51/0.99  prop_fast_solver_time:                  0.
% 3.51/0.99  prop_unsat_core_time:                   0.
% 3.51/0.99  
% 3.51/0.99  ------ QBF
% 3.51/0.99  
% 3.51/0.99  qbf_q_res:                              0
% 3.51/0.99  qbf_num_tautologies:                    0
% 3.51/0.99  qbf_prep_cycles:                        0
% 3.51/0.99  
% 3.51/0.99  ------ BMC1
% 3.51/0.99  
% 3.51/0.99  bmc1_current_bound:                     -1
% 3.51/0.99  bmc1_last_solved_bound:                 -1
% 3.51/0.99  bmc1_unsat_core_size:                   -1
% 3.51/0.99  bmc1_unsat_core_parents_size:           -1
% 3.51/0.99  bmc1_merge_next_fun:                    0
% 3.51/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.51/0.99  
% 3.51/0.99  ------ Instantiation
% 3.51/0.99  
% 3.51/0.99  inst_num_of_clauses:                    1210
% 3.51/0.99  inst_num_in_passive:                    295
% 3.51/0.99  inst_num_in_active:                     611
% 3.51/0.99  inst_num_in_unprocessed:                306
% 3.51/0.99  inst_num_of_loops:                      670
% 3.51/0.99  inst_num_of_learning_restarts:          0
% 3.51/0.99  inst_num_moves_active_passive:          55
% 3.51/0.99  inst_lit_activity:                      0
% 3.51/0.99  inst_lit_activity_moves:                0
% 3.51/0.99  inst_num_tautologies:                   0
% 3.51/0.99  inst_num_prop_implied:                  0
% 3.51/0.99  inst_num_existing_simplified:           0
% 3.51/0.99  inst_num_eq_res_simplified:             0
% 3.51/0.99  inst_num_child_elim:                    0
% 3.51/0.99  inst_num_of_dismatching_blockings:      369
% 3.51/0.99  inst_num_of_non_proper_insts:           1243
% 3.51/0.99  inst_num_of_duplicates:                 0
% 3.51/0.99  inst_inst_num_from_inst_to_res:         0
% 3.51/0.99  inst_dismatching_checking_time:         0.
% 3.51/0.99  
% 3.51/0.99  ------ Resolution
% 3.51/0.99  
% 3.51/0.99  res_num_of_clauses:                     0
% 3.51/0.99  res_num_in_passive:                     0
% 3.51/0.99  res_num_in_active:                      0
% 3.51/0.99  res_num_of_loops:                       190
% 3.51/0.99  res_forward_subset_subsumed:            143
% 3.51/0.99  res_backward_subset_subsumed:           4
% 3.51/0.99  res_forward_subsumed:                   0
% 3.51/0.99  res_backward_subsumed:                  1
% 3.51/0.99  res_forward_subsumption_resolution:     5
% 3.51/0.99  res_backward_subsumption_resolution:    0
% 3.51/0.99  res_clause_to_clause_subsumption:       507
% 3.51/0.99  res_orphan_elimination:                 0
% 3.51/0.99  res_tautology_del:                      148
% 3.51/0.99  res_num_eq_res_simplified:              0
% 3.51/0.99  res_num_sel_changes:                    0
% 3.51/0.99  res_moves_from_active_to_pass:          0
% 3.51/0.99  
% 3.51/0.99  ------ Superposition
% 3.51/0.99  
% 3.51/0.99  sup_time_total:                         0.
% 3.51/0.99  sup_time_generating:                    0.
% 3.51/0.99  sup_time_sim_full:                      0.
% 3.51/0.99  sup_time_sim_immed:                     0.
% 3.51/0.99  
% 3.51/0.99  sup_num_of_clauses:                     182
% 3.51/0.99  sup_num_in_active:                      120
% 3.51/0.99  sup_num_in_passive:                     62
% 3.51/0.99  sup_num_of_loops:                       132
% 3.51/0.99  sup_fw_superposition:                   101
% 3.51/0.99  sup_bw_superposition:                   136
% 3.51/0.99  sup_immediate_simplified:               40
% 3.51/0.99  sup_given_eliminated:                   0
% 3.51/0.99  comparisons_done:                       0
% 3.51/0.99  comparisons_avoided:                    0
% 3.51/0.99  
% 3.51/0.99  ------ Simplifications
% 3.51/0.99  
% 3.51/0.99  
% 3.51/0.99  sim_fw_subset_subsumed:                 10
% 3.51/0.99  sim_bw_subset_subsumed:                 24
% 3.51/0.99  sim_fw_subsumed:                        5
% 3.51/0.99  sim_bw_subsumed:                        0
% 3.51/0.99  sim_fw_subsumption_res:                 4
% 3.51/0.99  sim_bw_subsumption_res:                 0
% 3.51/0.99  sim_tautology_del:                      7
% 3.51/0.99  sim_eq_tautology_del:                   6
% 3.51/0.99  sim_eq_res_simp:                        0
% 3.51/0.99  sim_fw_demodulated:                     3
% 3.51/0.99  sim_bw_demodulated:                     8
% 3.51/0.99  sim_light_normalised:                   24
% 3.51/0.99  sim_joinable_taut:                      0
% 3.51/0.99  sim_joinable_simp:                      0
% 3.51/0.99  sim_ac_normalised:                      0
% 3.51/0.99  sim_smt_subsumption:                    0
% 3.51/0.99  
%------------------------------------------------------------------------------
