%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:12 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :  194 ( 893 expanded)
%              Number of clauses        :  106 ( 225 expanded)
%              Number of leaves         :   24 ( 202 expanded)
%              Depth                    :   25
%              Number of atoms          :  729 (5422 expanded)
%              Number of equality atoms :  152 ( 267 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

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
    inference(ennf_transformation,[],[f20])).

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

fof(f94,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f60])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK0(X0,X1),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r1_tarski(sK0(X0,X1),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f97,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f53,plain,(
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
    inference(rectify,[],[f52])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK2(X0),X0)
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK2(X0),X0)
            & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f53,f54])).

fof(f84,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f93,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f92,plain,(
    v1_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f91,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
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

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] :
          ( v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v1_tops_1(sK1(X0),X0)
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_tops_1(sK1(X0),X0)
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f48])).

fof(f78,plain,(
    ! [X0] :
      ( v1_tops_1(sK1(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f77,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f80,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | u1_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f6,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f96,plain,
    ( v1_subset_1(sK4,u1_struct_0(sK3))
    | ~ v3_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

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

fof(f87,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f18,axiom,(
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
    inference(ennf_transformation,[],[f18])).

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

fof(f89,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f79,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f90,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f95,plain,
    ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
    | v3_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f17,axiom,(
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
    inference(ennf_transformation,[],[f17])).

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

fof(f88,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2048,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2051,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2068,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2051,c_5])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2050,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2643,plain,
    ( k7_subset_1(X0,X0,X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2068,c_2050])).

cnf(c_3,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2053,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_9,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2049,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2556,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2053,c_2049])).

cnf(c_25,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1011,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_32])).

cnf(c_1012,plain,
    ( v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_tdlat_3(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1011])).

cnf(c_33,negated_conjecture,
    ( v1_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_925,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_33])).

cnf(c_926,plain,
    ( v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_925])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_930,plain,
    ( v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_926,c_34,c_32])).

cnf(c_1014,plain,
    ( v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1012,c_34,c_32,c_926])).

cnf(c_10,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
    | v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_13,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_829,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X3)
    | X2 != X1
    | X3 != X0
    | k2_pre_topc(X3,X2) = X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_13])).

cnf(c_830,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | k2_pre_topc(X0,X1) = X1 ),
    inference(unflattening,[status(thm)],[c_829])).

cnf(c_976,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k2_pre_topc(X0,X1) = X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_830,c_32])).

cnf(c_977,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK3),k2_struct_0(sK3),X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK3,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_976])).

cnf(c_1131,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | k7_subset_1(u1_struct_0(sK3),k2_struct_0(sK3),X1) != X0
    | k2_pre_topc(sK3,X1) = X1
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_1014,c_977])).

cnf(c_1132,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK3),k2_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK3,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_1131])).

cnf(c_2046,plain,
    ( k2_pre_topc(sK3,X0) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK3),k2_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1132])).

cnf(c_16,plain,
    ( v1_tops_1(sK1(X0),X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1004,plain,
    ( v1_tops_1(sK1(X0),X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_32])).

cnf(c_1005,plain,
    ( v1_tops_1(sK1(sK3),sK3) ),
    inference(unflattening,[status(thm)],[c_1004])).

cnf(c_15,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1055,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = k2_struct_0(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_32])).

cnf(c_1056,plain,
    ( ~ v1_tops_1(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK3,X0) = k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1055])).

cnf(c_1191,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK3,X0) = k2_struct_0(sK3)
    | sK1(sK3) != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_1005,c_1056])).

cnf(c_1192,plain,
    ( ~ m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK3,sK1(sK3)) = k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1191])).

cnf(c_17,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_71,plain,
    ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1194,plain,
    ( k2_pre_topc(sK3,sK1(sK3)) = k2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1192,c_32,c_71])).

cnf(c_20,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1025,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = u1_struct_0(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_32])).

cnf(c_1026,plain,
    ( ~ v1_tops_1(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK3,X0) = u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1025])).

cnf(c_1199,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK3,X0) = u1_struct_0(sK3)
    | sK1(sK3) != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_1005,c_1026])).

cnf(c_1200,plain,
    ( ~ m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK3,sK1(sK3)) = u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1199])).

cnf(c_1202,plain,
    ( k2_pre_topc(sK3,sK1(sK3)) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1200,c_32,c_71])).

cnf(c_2063,plain,
    ( k2_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(light_normalisation,[status(thm)],[c_1194,c_1202])).

cnf(c_2124,plain,
    ( k2_pre_topc(sK3,X0) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK3),u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2046,c_2063])).

cnf(c_2565,plain,
    ( k2_pre_topc(sK3,X0) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(k7_subset_1(u1_struct_0(sK3),u1_struct_0(sK3),X0),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2556,c_2124])).

cnf(c_2852,plain,
    ( k2_pre_topc(sK3,X0) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(k4_xboole_0(u1_struct_0(sK3),X0),u1_struct_0(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2643,c_2565])).

cnf(c_0,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2056,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3043,plain,
    ( k2_pre_topc(sK3,X0) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2852,c_2056])).

cnf(c_3049,plain,
    ( k2_pre_topc(sK3,sK4) = sK4 ),
    inference(superposition,[status(thm)],[c_2048,c_3043])).

cnf(c_19,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1040,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) != u1_struct_0(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_32])).

cnf(c_1041,plain,
    ( v1_tops_1(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK3,X0) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1040])).

cnf(c_8,plain,
    ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_29,negated_conjecture,
    ( ~ v3_tex_2(sK4,sK3)
    | v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_277,plain,
    ( ~ v3_tex_2(sK4,sK3)
    | v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(prop_impl,[status(thm)],[c_29])).

cnf(c_571,plain,
    ( ~ v3_tex_2(sK4,sK3)
    | u1_struct_0(sK3) != X0
    | k2_subset_1(X0) != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_277])).

cnf(c_572,plain,
    ( ~ v3_tex_2(sK4,sK3)
    | k2_subset_1(u1_struct_0(sK3)) != sK4 ),
    inference(unflattening,[status(thm)],[c_571])).

cnf(c_26,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_28,plain,
    ( v3_tex_2(X0,X1)
    | ~ v2_tex_2(X0,X1)
    | ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_470,plain,
    ( v3_tex_2(X0,X1)
    | ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_26,c_28])).

cnf(c_18,plain,
    ( ~ v1_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_488,plain,
    ( v3_tex_2(X0,X1)
    | ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_470,c_18])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_505,plain,
    ( v3_tex_2(X0,X1)
    | ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_488,c_35])).

cnf(c_506,plain,
    ( v3_tex_2(X0,sK3)
    | ~ v1_tops_1(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_tdlat_3(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_505])).

cnf(c_510,plain,
    ( v3_tex_2(X0,sK3)
    | ~ v1_tops_1(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_506,c_33,c_32])).

cnf(c_800,plain,
    ( ~ v1_tops_1(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_subset_1(u1_struct_0(sK3)) != sK4
    | sK3 != sK3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_572,c_510])).

cnf(c_801,plain,
    ( ~ v1_tops_1(sK4,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_subset_1(u1_struct_0(sK3)) != sK4 ),
    inference(unflattening,[status(thm)],[c_800])).

cnf(c_803,plain,
    ( ~ v1_tops_1(sK4,sK3)
    | k2_subset_1(u1_struct_0(sK3)) != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_801,c_31])).

cnf(c_1260,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK3,X0) != u1_struct_0(sK3)
    | k2_subset_1(u1_struct_0(sK3)) != sK4
    | sK3 != sK3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1041,c_803])).

cnf(c_1261,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK3,sK4) != u1_struct_0(sK3)
    | k2_subset_1(u1_struct_0(sK3)) != sK4 ),
    inference(unflattening,[status(thm)],[c_1260])).

cnf(c_1263,plain,
    ( k2_pre_topc(sK3,sK4) != u1_struct_0(sK3)
    | k2_subset_1(u1_struct_0(sK3)) != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1261,c_31])).

cnf(c_2098,plain,
    ( k2_pre_topc(sK3,sK4) != u1_struct_0(sK3)
    | u1_struct_0(sK3) != sK4 ),
    inference(demodulation,[status(thm)],[c_1263,c_5])).

cnf(c_3066,plain,
    ( u1_struct_0(sK3) != sK4 ),
    inference(demodulation,[status(thm)],[c_3049,c_2098])).

cnf(c_21,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_30,negated_conjecture,
    ( v3_tex_2(sK4,sK3)
    | ~ v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_275,plain,
    ( v3_tex_2(sK4,sK3)
    | ~ v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(prop_impl,[status(thm)],[c_30])).

cnf(c_583,plain,
    ( v3_tex_2(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 = X0
    | u1_struct_0(sK3) != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_275])).

cnf(c_584,plain,
    ( v3_tex_2(sK4,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | u1_struct_0(sK3) = sK4 ),
    inference(unflattening,[status(thm)],[c_583])).

cnf(c_586,plain,
    ( v3_tex_2(sK4,sK3)
    | u1_struct_0(sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_584,c_31])).

cnf(c_27,plain,
    ( ~ v3_tex_2(X0,X1)
    | v1_tops_1(X0,X1)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_526,plain,
    ( ~ v3_tex_2(X0,X1)
    | v1_tops_1(X0,X1)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_35])).

cnf(c_527,plain,
    ( ~ v3_tex_2(X0,sK3)
    | v1_tops_1(X0,sK3)
    | ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_526])).

cnf(c_531,plain,
    ( ~ v3_tex_2(X0,sK3)
    | v1_tops_1(X0,sK3)
    | ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_527,c_34,c_32])).

cnf(c_766,plain,
    ( v1_tops_1(X0,sK3)
    | ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | u1_struct_0(sK3) = sK4
    | sK3 != sK3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_586,c_531])).

cnf(c_767,plain,
    ( v1_tops_1(sK4,sK3)
    | ~ v3_pre_topc(sK4,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | u1_struct_0(sK3) = sK4 ),
    inference(unflattening,[status(thm)],[c_766])).

cnf(c_769,plain,
    ( ~ v3_pre_topc(sK4,sK3)
    | v1_tops_1(sK4,sK3)
    | u1_struct_0(sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_767,c_31])).

cnf(c_770,plain,
    ( v1_tops_1(sK4,sK3)
    | ~ v3_pre_topc(sK4,sK3)
    | u1_struct_0(sK3) = sK4 ),
    inference(renaming,[status(thm)],[c_769])).

cnf(c_1117,plain,
    ( v1_tops_1(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | u1_struct_0(sK3) = sK4
    | sK3 != sK3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1014,c_770])).

cnf(c_1118,plain,
    ( v1_tops_1(sK4,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | u1_struct_0(sK3) = sK4 ),
    inference(unflattening,[status(thm)],[c_1117])).

cnf(c_1120,plain,
    ( v1_tops_1(sK4,sK3)
    | u1_struct_0(sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1118,c_31])).

cnf(c_1299,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK3,X0) = u1_struct_0(sK3)
    | u1_struct_0(sK3) = sK4
    | sK3 != sK3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1026,c_1120])).

cnf(c_1300,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK3,sK4) = u1_struct_0(sK3)
    | u1_struct_0(sK3) = sK4 ),
    inference(unflattening,[status(thm)],[c_1299])).

cnf(c_1302,plain,
    ( k2_pre_topc(sK3,sK4) = u1_struct_0(sK3)
    | u1_struct_0(sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1300,c_31])).

cnf(c_3067,plain,
    ( u1_struct_0(sK3) = sK4 ),
    inference(demodulation,[status(thm)],[c_3049,c_1302])).

cnf(c_3070,plain,
    ( sK4 != sK4 ),
    inference(light_normalisation,[status(thm)],[c_3066,c_3067])).

cnf(c_3071,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_3070])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:20:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.30/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/0.98  
% 2.30/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.30/0.98  
% 2.30/0.98  ------  iProver source info
% 2.30/0.98  
% 2.30/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.30/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.30/0.98  git: non_committed_changes: false
% 2.30/0.98  git: last_make_outside_of_git: false
% 2.30/0.98  
% 2.30/0.98  ------ 
% 2.30/0.98  
% 2.30/0.98  ------ Input Options
% 2.30/0.98  
% 2.30/0.98  --out_options                           all
% 2.30/0.98  --tptp_safe_out                         true
% 2.30/0.98  --problem_path                          ""
% 2.30/0.98  --include_path                          ""
% 2.30/0.98  --clausifier                            res/vclausify_rel
% 2.30/0.98  --clausifier_options                    --mode clausify
% 2.30/0.98  --stdin                                 false
% 2.30/0.98  --stats_out                             all
% 2.30/0.98  
% 2.30/0.98  ------ General Options
% 2.30/0.98  
% 2.30/0.98  --fof                                   false
% 2.30/0.98  --time_out_real                         305.
% 2.30/0.98  --time_out_virtual                      -1.
% 2.30/0.98  --symbol_type_check                     false
% 2.30/0.98  --clausify_out                          false
% 2.30/0.98  --sig_cnt_out                           false
% 2.30/0.98  --trig_cnt_out                          false
% 2.30/0.98  --trig_cnt_out_tolerance                1.
% 2.30/0.98  --trig_cnt_out_sk_spl                   false
% 2.30/0.98  --abstr_cl_out                          false
% 2.30/0.98  
% 2.30/0.98  ------ Global Options
% 2.30/0.98  
% 2.30/0.98  --schedule                              default
% 2.30/0.98  --add_important_lit                     false
% 2.30/0.98  --prop_solver_per_cl                    1000
% 2.30/0.98  --min_unsat_core                        false
% 2.30/0.98  --soft_assumptions                      false
% 2.30/0.98  --soft_lemma_size                       3
% 2.30/0.98  --prop_impl_unit_size                   0
% 2.30/0.98  --prop_impl_unit                        []
% 2.30/0.98  --share_sel_clauses                     true
% 2.30/0.98  --reset_solvers                         false
% 2.30/0.98  --bc_imp_inh                            [conj_cone]
% 2.30/0.98  --conj_cone_tolerance                   3.
% 2.30/0.98  --extra_neg_conj                        none
% 2.30/0.98  --large_theory_mode                     true
% 2.30/0.98  --prolific_symb_bound                   200
% 2.30/0.98  --lt_threshold                          2000
% 2.30/0.98  --clause_weak_htbl                      true
% 2.30/0.98  --gc_record_bc_elim                     false
% 2.30/0.98  
% 2.30/0.98  ------ Preprocessing Options
% 2.30/0.98  
% 2.30/0.98  --preprocessing_flag                    true
% 2.30/0.98  --time_out_prep_mult                    0.1
% 2.30/0.98  --splitting_mode                        input
% 2.30/0.98  --splitting_grd                         true
% 2.30/0.98  --splitting_cvd                         false
% 2.30/0.98  --splitting_cvd_svl                     false
% 2.30/0.98  --splitting_nvd                         32
% 2.30/0.98  --sub_typing                            true
% 2.30/0.98  --prep_gs_sim                           true
% 2.30/0.98  --prep_unflatten                        true
% 2.30/0.98  --prep_res_sim                          true
% 2.30/0.98  --prep_upred                            true
% 2.30/0.98  --prep_sem_filter                       exhaustive
% 2.30/0.98  --prep_sem_filter_out                   false
% 2.30/0.98  --pred_elim                             true
% 2.30/0.98  --res_sim_input                         true
% 2.30/0.98  --eq_ax_congr_red                       true
% 2.30/0.98  --pure_diseq_elim                       true
% 2.30/0.98  --brand_transform                       false
% 2.30/0.98  --non_eq_to_eq                          false
% 2.30/0.98  --prep_def_merge                        true
% 2.30/0.98  --prep_def_merge_prop_impl              false
% 2.30/0.98  --prep_def_merge_mbd                    true
% 2.30/0.98  --prep_def_merge_tr_red                 false
% 2.30/0.98  --prep_def_merge_tr_cl                  false
% 2.30/0.98  --smt_preprocessing                     true
% 2.30/0.98  --smt_ac_axioms                         fast
% 2.30/0.98  --preprocessed_out                      false
% 2.30/0.98  --preprocessed_stats                    false
% 2.30/0.98  
% 2.30/0.98  ------ Abstraction refinement Options
% 2.30/0.98  
% 2.30/0.98  --abstr_ref                             []
% 2.30/0.98  --abstr_ref_prep                        false
% 2.30/0.98  --abstr_ref_until_sat                   false
% 2.30/0.98  --abstr_ref_sig_restrict                funpre
% 2.30/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.30/0.98  --abstr_ref_under                       []
% 2.30/0.98  
% 2.30/0.98  ------ SAT Options
% 2.30/0.98  
% 2.30/0.98  --sat_mode                              false
% 2.30/0.98  --sat_fm_restart_options                ""
% 2.30/0.98  --sat_gr_def                            false
% 2.30/0.98  --sat_epr_types                         true
% 2.30/0.98  --sat_non_cyclic_types                  false
% 2.30/0.98  --sat_finite_models                     false
% 2.30/0.98  --sat_fm_lemmas                         false
% 2.30/0.98  --sat_fm_prep                           false
% 2.30/0.98  --sat_fm_uc_incr                        true
% 2.30/0.98  --sat_out_model                         small
% 2.30/0.98  --sat_out_clauses                       false
% 2.30/0.98  
% 2.30/0.98  ------ QBF Options
% 2.30/0.98  
% 2.30/0.98  --qbf_mode                              false
% 2.30/0.98  --qbf_elim_univ                         false
% 2.30/0.98  --qbf_dom_inst                          none
% 2.30/0.98  --qbf_dom_pre_inst                      false
% 2.30/0.98  --qbf_sk_in                             false
% 2.30/0.98  --qbf_pred_elim                         true
% 2.30/0.98  --qbf_split                             512
% 2.30/0.98  
% 2.30/0.98  ------ BMC1 Options
% 2.30/0.98  
% 2.30/0.98  --bmc1_incremental                      false
% 2.30/0.98  --bmc1_axioms                           reachable_all
% 2.30/0.98  --bmc1_min_bound                        0
% 2.30/0.98  --bmc1_max_bound                        -1
% 2.30/0.98  --bmc1_max_bound_default                -1
% 2.30/0.98  --bmc1_symbol_reachability              true
% 2.30/0.98  --bmc1_property_lemmas                  false
% 2.30/0.98  --bmc1_k_induction                      false
% 2.30/0.98  --bmc1_non_equiv_states                 false
% 2.30/0.98  --bmc1_deadlock                         false
% 2.30/0.98  --bmc1_ucm                              false
% 2.30/0.98  --bmc1_add_unsat_core                   none
% 2.30/0.98  --bmc1_unsat_core_children              false
% 2.30/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.30/0.98  --bmc1_out_stat                         full
% 2.30/0.98  --bmc1_ground_init                      false
% 2.30/0.98  --bmc1_pre_inst_next_state              false
% 2.30/0.98  --bmc1_pre_inst_state                   false
% 2.30/0.98  --bmc1_pre_inst_reach_state             false
% 2.30/0.98  --bmc1_out_unsat_core                   false
% 2.30/0.98  --bmc1_aig_witness_out                  false
% 2.30/0.98  --bmc1_verbose                          false
% 2.30/0.98  --bmc1_dump_clauses_tptp                false
% 2.30/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.30/0.98  --bmc1_dump_file                        -
% 2.30/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.30/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.30/0.98  --bmc1_ucm_extend_mode                  1
% 2.30/0.98  --bmc1_ucm_init_mode                    2
% 2.30/0.98  --bmc1_ucm_cone_mode                    none
% 2.30/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.30/0.98  --bmc1_ucm_relax_model                  4
% 2.30/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.30/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.30/0.98  --bmc1_ucm_layered_model                none
% 2.30/0.98  --bmc1_ucm_max_lemma_size               10
% 2.30/0.98  
% 2.30/0.98  ------ AIG Options
% 2.30/0.98  
% 2.30/0.98  --aig_mode                              false
% 2.30/0.98  
% 2.30/0.98  ------ Instantiation Options
% 2.30/0.98  
% 2.30/0.98  --instantiation_flag                    true
% 2.30/0.98  --inst_sos_flag                         false
% 2.30/0.98  --inst_sos_phase                        true
% 2.30/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.30/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.30/0.98  --inst_lit_sel_side                     num_symb
% 2.30/0.98  --inst_solver_per_active                1400
% 2.30/0.98  --inst_solver_calls_frac                1.
% 2.30/0.98  --inst_passive_queue_type               priority_queues
% 2.30/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.30/0.98  --inst_passive_queues_freq              [25;2]
% 2.30/0.98  --inst_dismatching                      true
% 2.30/0.98  --inst_eager_unprocessed_to_passive     true
% 2.30/0.98  --inst_prop_sim_given                   true
% 2.30/0.98  --inst_prop_sim_new                     false
% 2.30/0.98  --inst_subs_new                         false
% 2.30/0.98  --inst_eq_res_simp                      false
% 2.30/0.98  --inst_subs_given                       false
% 2.30/0.98  --inst_orphan_elimination               true
% 2.30/0.98  --inst_learning_loop_flag               true
% 2.30/0.98  --inst_learning_start                   3000
% 2.30/0.98  --inst_learning_factor                  2
% 2.30/0.98  --inst_start_prop_sim_after_learn       3
% 2.30/0.98  --inst_sel_renew                        solver
% 2.30/0.98  --inst_lit_activity_flag                true
% 2.30/0.98  --inst_restr_to_given                   false
% 2.30/0.98  --inst_activity_threshold               500
% 2.30/0.98  --inst_out_proof                        true
% 2.30/0.98  
% 2.30/0.98  ------ Resolution Options
% 2.30/0.98  
% 2.30/0.98  --resolution_flag                       true
% 2.30/0.98  --res_lit_sel                           adaptive
% 2.30/0.98  --res_lit_sel_side                      none
% 2.30/0.98  --res_ordering                          kbo
% 2.30/0.98  --res_to_prop_solver                    active
% 2.30/0.98  --res_prop_simpl_new                    false
% 2.30/0.98  --res_prop_simpl_given                  true
% 2.30/0.98  --res_passive_queue_type                priority_queues
% 2.30/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.30/0.98  --res_passive_queues_freq               [15;5]
% 2.30/0.98  --res_forward_subs                      full
% 2.30/0.98  --res_backward_subs                     full
% 2.30/0.98  --res_forward_subs_resolution           true
% 2.30/0.98  --res_backward_subs_resolution          true
% 2.30/0.98  --res_orphan_elimination                true
% 2.30/0.98  --res_time_limit                        2.
% 2.30/0.98  --res_out_proof                         true
% 2.30/0.98  
% 2.30/0.98  ------ Superposition Options
% 2.30/0.98  
% 2.30/0.98  --superposition_flag                    true
% 2.30/0.98  --sup_passive_queue_type                priority_queues
% 2.30/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.30/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.30/0.98  --demod_completeness_check              fast
% 2.30/0.98  --demod_use_ground                      true
% 2.30/0.98  --sup_to_prop_solver                    passive
% 2.30/0.98  --sup_prop_simpl_new                    true
% 2.30/0.98  --sup_prop_simpl_given                  true
% 2.30/0.98  --sup_fun_splitting                     false
% 2.30/0.98  --sup_smt_interval                      50000
% 2.30/0.98  
% 2.30/0.98  ------ Superposition Simplification Setup
% 2.30/0.98  
% 2.30/0.98  --sup_indices_passive                   []
% 2.30/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.30/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.30/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.30/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.30/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.30/0.98  --sup_full_bw                           [BwDemod]
% 2.30/0.98  --sup_immed_triv                        [TrivRules]
% 2.30/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.30/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.30/0.98  --sup_immed_bw_main                     []
% 2.30/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.30/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.30/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.30/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.30/0.98  
% 2.30/0.98  ------ Combination Options
% 2.30/0.98  
% 2.30/0.98  --comb_res_mult                         3
% 2.30/0.98  --comb_sup_mult                         2
% 2.30/0.98  --comb_inst_mult                        10
% 2.30/0.98  
% 2.30/0.98  ------ Debug Options
% 2.30/0.98  
% 2.30/0.98  --dbg_backtrace                         false
% 2.30/0.98  --dbg_dump_prop_clauses                 false
% 2.30/0.98  --dbg_dump_prop_clauses_file            -
% 2.30/0.98  --dbg_out_stat                          false
% 2.30/0.98  ------ Parsing...
% 2.30/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.30/0.98  
% 2.30/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 2.30/0.98  
% 2.30/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.30/0.98  
% 2.30/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.30/0.98  ------ Proving...
% 2.30/0.98  ------ Problem Properties 
% 2.30/0.98  
% 2.30/0.98  
% 2.30/0.98  clauses                                 26
% 2.30/0.98  conjectures                             1
% 2.30/0.98  EPR                                     1
% 2.30/0.98  Horn                                    23
% 2.30/0.98  unary                                   8
% 2.30/0.98  binary                                  10
% 2.30/0.98  lits                                    52
% 2.30/0.98  lits eq                                 30
% 2.30/0.98  fd_pure                                 0
% 2.30/0.98  fd_pseudo                               0
% 2.30/0.98  fd_cond                                 0
% 2.30/0.98  fd_pseudo_cond                          2
% 2.30/0.98  AC symbols                              0
% 2.30/0.98  
% 2.30/0.98  ------ Schedule dynamic 5 is on 
% 2.30/0.98  
% 2.30/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.30/0.98  
% 2.30/0.98  
% 2.30/0.98  ------ 
% 2.30/0.98  Current options:
% 2.30/0.98  ------ 
% 2.30/0.98  
% 2.30/0.98  ------ Input Options
% 2.30/0.98  
% 2.30/0.98  --out_options                           all
% 2.30/0.98  --tptp_safe_out                         true
% 2.30/0.98  --problem_path                          ""
% 2.30/0.98  --include_path                          ""
% 2.30/0.98  --clausifier                            res/vclausify_rel
% 2.30/0.98  --clausifier_options                    --mode clausify
% 2.30/0.98  --stdin                                 false
% 2.30/0.98  --stats_out                             all
% 2.30/0.98  
% 2.30/0.98  ------ General Options
% 2.30/0.98  
% 2.30/0.98  --fof                                   false
% 2.30/0.98  --time_out_real                         305.
% 2.30/0.98  --time_out_virtual                      -1.
% 2.30/0.98  --symbol_type_check                     false
% 2.30/0.98  --clausify_out                          false
% 2.30/0.98  --sig_cnt_out                           false
% 2.30/0.98  --trig_cnt_out                          false
% 2.30/0.98  --trig_cnt_out_tolerance                1.
% 2.30/0.98  --trig_cnt_out_sk_spl                   false
% 2.30/0.98  --abstr_cl_out                          false
% 2.30/0.98  
% 2.30/0.98  ------ Global Options
% 2.30/0.98  
% 2.30/0.98  --schedule                              default
% 2.30/0.98  --add_important_lit                     false
% 2.30/0.98  --prop_solver_per_cl                    1000
% 2.30/0.98  --min_unsat_core                        false
% 2.30/0.98  --soft_assumptions                      false
% 2.30/0.98  --soft_lemma_size                       3
% 2.30/0.98  --prop_impl_unit_size                   0
% 2.30/0.98  --prop_impl_unit                        []
% 2.30/0.98  --share_sel_clauses                     true
% 2.30/0.98  --reset_solvers                         false
% 2.30/0.98  --bc_imp_inh                            [conj_cone]
% 2.30/0.98  --conj_cone_tolerance                   3.
% 2.30/0.98  --extra_neg_conj                        none
% 2.30/0.98  --large_theory_mode                     true
% 2.30/0.98  --prolific_symb_bound                   200
% 2.30/0.98  --lt_threshold                          2000
% 2.30/0.98  --clause_weak_htbl                      true
% 2.30/0.98  --gc_record_bc_elim                     false
% 2.30/0.98  
% 2.30/0.98  ------ Preprocessing Options
% 2.30/0.98  
% 2.30/0.98  --preprocessing_flag                    true
% 2.30/0.98  --time_out_prep_mult                    0.1
% 2.30/0.98  --splitting_mode                        input
% 2.30/0.98  --splitting_grd                         true
% 2.30/0.98  --splitting_cvd                         false
% 2.30/0.98  --splitting_cvd_svl                     false
% 2.30/0.98  --splitting_nvd                         32
% 2.30/0.98  --sub_typing                            true
% 2.30/0.98  --prep_gs_sim                           true
% 2.30/0.98  --prep_unflatten                        true
% 2.30/0.98  --prep_res_sim                          true
% 2.30/0.98  --prep_upred                            true
% 2.30/0.98  --prep_sem_filter                       exhaustive
% 2.30/0.98  --prep_sem_filter_out                   false
% 2.30/0.98  --pred_elim                             true
% 2.30/0.98  --res_sim_input                         true
% 2.30/0.98  --eq_ax_congr_red                       true
% 2.30/0.98  --pure_diseq_elim                       true
% 2.30/0.98  --brand_transform                       false
% 2.30/0.98  --non_eq_to_eq                          false
% 2.30/0.98  --prep_def_merge                        true
% 2.30/0.98  --prep_def_merge_prop_impl              false
% 2.30/0.98  --prep_def_merge_mbd                    true
% 2.30/0.98  --prep_def_merge_tr_red                 false
% 2.30/0.98  --prep_def_merge_tr_cl                  false
% 2.30/0.98  --smt_preprocessing                     true
% 2.30/0.98  --smt_ac_axioms                         fast
% 2.30/0.98  --preprocessed_out                      false
% 2.30/0.98  --preprocessed_stats                    false
% 2.30/0.98  
% 2.30/0.98  ------ Abstraction refinement Options
% 2.30/0.98  
% 2.30/0.98  --abstr_ref                             []
% 2.30/0.98  --abstr_ref_prep                        false
% 2.30/0.98  --abstr_ref_until_sat                   false
% 2.30/0.98  --abstr_ref_sig_restrict                funpre
% 2.30/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.30/0.98  --abstr_ref_under                       []
% 2.30/0.98  
% 2.30/0.98  ------ SAT Options
% 2.30/0.98  
% 2.30/0.98  --sat_mode                              false
% 2.30/0.98  --sat_fm_restart_options                ""
% 2.30/0.98  --sat_gr_def                            false
% 2.30/0.98  --sat_epr_types                         true
% 2.30/0.98  --sat_non_cyclic_types                  false
% 2.30/0.98  --sat_finite_models                     false
% 2.30/0.98  --sat_fm_lemmas                         false
% 2.30/0.98  --sat_fm_prep                           false
% 2.30/0.98  --sat_fm_uc_incr                        true
% 2.30/0.98  --sat_out_model                         small
% 2.30/0.98  --sat_out_clauses                       false
% 2.30/0.98  
% 2.30/0.98  ------ QBF Options
% 2.30/0.98  
% 2.30/0.98  --qbf_mode                              false
% 2.30/0.98  --qbf_elim_univ                         false
% 2.30/0.98  --qbf_dom_inst                          none
% 2.30/0.98  --qbf_dom_pre_inst                      false
% 2.30/0.98  --qbf_sk_in                             false
% 2.30/0.98  --qbf_pred_elim                         true
% 2.30/0.98  --qbf_split                             512
% 2.30/0.98  
% 2.30/0.98  ------ BMC1 Options
% 2.30/0.98  
% 2.30/0.98  --bmc1_incremental                      false
% 2.30/0.98  --bmc1_axioms                           reachable_all
% 2.30/0.98  --bmc1_min_bound                        0
% 2.30/0.98  --bmc1_max_bound                        -1
% 2.30/0.98  --bmc1_max_bound_default                -1
% 2.30/0.98  --bmc1_symbol_reachability              true
% 2.30/0.98  --bmc1_property_lemmas                  false
% 2.30/0.98  --bmc1_k_induction                      false
% 2.30/0.98  --bmc1_non_equiv_states                 false
% 2.30/0.98  --bmc1_deadlock                         false
% 2.30/0.98  --bmc1_ucm                              false
% 2.30/0.98  --bmc1_add_unsat_core                   none
% 2.30/0.98  --bmc1_unsat_core_children              false
% 2.30/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.30/0.98  --bmc1_out_stat                         full
% 2.30/0.98  --bmc1_ground_init                      false
% 2.30/0.98  --bmc1_pre_inst_next_state              false
% 2.30/0.98  --bmc1_pre_inst_state                   false
% 2.30/0.98  --bmc1_pre_inst_reach_state             false
% 2.30/0.98  --bmc1_out_unsat_core                   false
% 2.30/0.98  --bmc1_aig_witness_out                  false
% 2.30/0.98  --bmc1_verbose                          false
% 2.30/0.98  --bmc1_dump_clauses_tptp                false
% 2.30/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.30/0.98  --bmc1_dump_file                        -
% 2.30/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.30/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.30/0.98  --bmc1_ucm_extend_mode                  1
% 2.30/0.98  --bmc1_ucm_init_mode                    2
% 2.30/0.98  --bmc1_ucm_cone_mode                    none
% 2.30/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.30/0.98  --bmc1_ucm_relax_model                  4
% 2.30/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.30/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.30/0.98  --bmc1_ucm_layered_model                none
% 2.30/0.98  --bmc1_ucm_max_lemma_size               10
% 2.30/0.98  
% 2.30/0.98  ------ AIG Options
% 2.30/0.98  
% 2.30/0.98  --aig_mode                              false
% 2.30/0.98  
% 2.30/0.98  ------ Instantiation Options
% 2.30/0.98  
% 2.30/0.98  --instantiation_flag                    true
% 2.30/0.98  --inst_sos_flag                         false
% 2.30/0.98  --inst_sos_phase                        true
% 2.30/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.30/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.30/0.98  --inst_lit_sel_side                     none
% 2.30/0.98  --inst_solver_per_active                1400
% 2.30/0.98  --inst_solver_calls_frac                1.
% 2.30/0.98  --inst_passive_queue_type               priority_queues
% 2.30/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.30/0.98  --inst_passive_queues_freq              [25;2]
% 2.30/0.98  --inst_dismatching                      true
% 2.30/0.98  --inst_eager_unprocessed_to_passive     true
% 2.30/0.98  --inst_prop_sim_given                   true
% 2.30/0.98  --inst_prop_sim_new                     false
% 2.30/0.98  --inst_subs_new                         false
% 2.30/0.98  --inst_eq_res_simp                      false
% 2.30/0.98  --inst_subs_given                       false
% 2.30/0.98  --inst_orphan_elimination               true
% 2.30/0.98  --inst_learning_loop_flag               true
% 2.30/0.98  --inst_learning_start                   3000
% 2.30/0.98  --inst_learning_factor                  2
% 2.30/0.98  --inst_start_prop_sim_after_learn       3
% 2.30/0.98  --inst_sel_renew                        solver
% 2.30/0.98  --inst_lit_activity_flag                true
% 2.30/0.98  --inst_restr_to_given                   false
% 2.30/0.98  --inst_activity_threshold               500
% 2.30/0.98  --inst_out_proof                        true
% 2.30/0.98  
% 2.30/0.98  ------ Resolution Options
% 2.30/0.98  
% 2.30/0.98  --resolution_flag                       false
% 2.30/0.98  --res_lit_sel                           adaptive
% 2.30/0.98  --res_lit_sel_side                      none
% 2.30/0.98  --res_ordering                          kbo
% 2.30/0.98  --res_to_prop_solver                    active
% 2.30/0.98  --res_prop_simpl_new                    false
% 2.30/0.98  --res_prop_simpl_given                  true
% 2.30/0.98  --res_passive_queue_type                priority_queues
% 2.30/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.30/0.98  --res_passive_queues_freq               [15;5]
% 2.30/0.98  --res_forward_subs                      full
% 2.30/0.98  --res_backward_subs                     full
% 2.30/0.98  --res_forward_subs_resolution           true
% 2.30/0.98  --res_backward_subs_resolution          true
% 2.30/0.98  --res_orphan_elimination                true
% 2.30/0.98  --res_time_limit                        2.
% 2.30/0.98  --res_out_proof                         true
% 2.30/0.98  
% 2.30/0.98  ------ Superposition Options
% 2.30/0.98  
% 2.30/0.98  --superposition_flag                    true
% 2.30/0.98  --sup_passive_queue_type                priority_queues
% 2.30/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.30/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.30/0.98  --demod_completeness_check              fast
% 2.30/0.98  --demod_use_ground                      true
% 2.30/0.98  --sup_to_prop_solver                    passive
% 2.30/0.98  --sup_prop_simpl_new                    true
% 2.30/0.98  --sup_prop_simpl_given                  true
% 2.30/0.98  --sup_fun_splitting                     false
% 2.30/0.98  --sup_smt_interval                      50000
% 2.30/0.98  
% 2.30/0.98  ------ Superposition Simplification Setup
% 2.30/0.98  
% 2.30/0.98  --sup_indices_passive                   []
% 2.30/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.30/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.30/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.30/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.30/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.30/0.98  --sup_full_bw                           [BwDemod]
% 2.30/0.98  --sup_immed_triv                        [TrivRules]
% 2.30/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.30/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.30/0.98  --sup_immed_bw_main                     []
% 2.30/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.30/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.30/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.30/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.30/0.98  
% 2.30/0.98  ------ Combination Options
% 2.30/0.98  
% 2.30/0.98  --comb_res_mult                         3
% 2.30/0.98  --comb_sup_mult                         2
% 2.30/0.98  --comb_inst_mult                        10
% 2.30/0.98  
% 2.30/0.98  ------ Debug Options
% 2.30/0.98  
% 2.30/0.98  --dbg_backtrace                         false
% 2.30/0.98  --dbg_dump_prop_clauses                 false
% 2.30/0.98  --dbg_dump_prop_clauses_file            -
% 2.30/0.98  --dbg_out_stat                          false
% 2.30/0.98  
% 2.30/0.98  
% 2.30/0.98  
% 2.30/0.98  
% 2.30/0.98  ------ Proving...
% 2.30/0.98  
% 2.30/0.98  
% 2.30/0.98  % SZS status Theorem for theBenchmark.p
% 2.30/0.98  
% 2.30/0.98   Resolution empty clause
% 2.30/0.98  
% 2.30/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.30/0.98  
% 2.30/0.98  fof(f19,conjecture,(
% 2.30/0.98    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 2.30/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.30/0.98  
% 2.30/0.98  fof(f20,negated_conjecture,(
% 2.30/0.98    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 2.30/0.98    inference(negated_conjecture,[],[f19])).
% 2.30/0.98  
% 2.30/0.98  fof(f40,plain,(
% 2.30/0.98    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.30/0.98    inference(ennf_transformation,[],[f20])).
% 2.30/0.98  
% 2.30/0.98  fof(f41,plain,(
% 2.30/0.98    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.30/0.98    inference(flattening,[],[f40])).
% 2.30/0.98  
% 2.30/0.98  fof(f56,plain,(
% 2.30/0.98    ? [X0] : (? [X1] : (((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.30/0.98    inference(nnf_transformation,[],[f41])).
% 2.30/0.98  
% 2.30/0.98  fof(f57,plain,(
% 2.30/0.98    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.30/0.98    inference(flattening,[],[f56])).
% 2.30/0.98  
% 2.30/0.98  fof(f59,plain,(
% 2.30/0.98    ( ! [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_subset_1(sK4,u1_struct_0(X0)) | ~v3_tex_2(sK4,X0)) & (~v1_subset_1(sK4,u1_struct_0(X0)) | v3_tex_2(sK4,X0)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.30/0.98    introduced(choice_axiom,[])).
% 2.30/0.98  
% 2.30/0.98  fof(f58,plain,(
% 2.30/0.98    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((v1_subset_1(X1,u1_struct_0(sK3)) | ~v3_tex_2(X1,sK3)) & (~v1_subset_1(X1,u1_struct_0(sK3)) | v3_tex_2(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v1_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 2.30/0.98    introduced(choice_axiom,[])).
% 2.30/0.98  
% 2.30/0.98  fof(f60,plain,(
% 2.30/0.98    ((v1_subset_1(sK4,u1_struct_0(sK3)) | ~v3_tex_2(sK4,sK3)) & (~v1_subset_1(sK4,u1_struct_0(sK3)) | v3_tex_2(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v1_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 2.30/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f57,f59,f58])).
% 2.30/0.98  
% 2.30/0.98  fof(f94,plain,(
% 2.30/0.98    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 2.30/0.98    inference(cnf_transformation,[],[f60])).
% 2.30/0.98  
% 2.30/0.98  fof(f4,axiom,(
% 2.30/0.98    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.30/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.30/0.98  
% 2.30/0.98  fof(f67,plain,(
% 2.30/0.98    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.30/0.98    inference(cnf_transformation,[],[f4])).
% 2.30/0.98  
% 2.30/0.98  fof(f3,axiom,(
% 2.30/0.98    ! [X0] : k2_subset_1(X0) = X0),
% 2.30/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.30/0.98  
% 2.30/0.98  fof(f66,plain,(
% 2.30/0.98    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.30/0.98    inference(cnf_transformation,[],[f3])).
% 2.30/0.98  
% 2.30/0.98  fof(f5,axiom,(
% 2.30/0.98    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 2.30/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.30/0.98  
% 2.30/0.98  fof(f21,plain,(
% 2.30/0.98    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.30/0.98    inference(ennf_transformation,[],[f5])).
% 2.30/0.98  
% 2.30/0.98  fof(f68,plain,(
% 2.30/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.30/0.98    inference(cnf_transformation,[],[f21])).
% 2.30/0.98  
% 2.30/0.98  fof(f2,axiom,(
% 2.30/0.98    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.30/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.30/0.98  
% 2.30/0.98  fof(f42,plain,(
% 2.30/0.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.30/0.98    inference(nnf_transformation,[],[f2])).
% 2.30/0.98  
% 2.30/0.98  fof(f43,plain,(
% 2.30/0.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.30/0.98    inference(rectify,[],[f42])).
% 2.30/0.98  
% 2.30/0.98  fof(f44,plain,(
% 2.30/0.98    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 2.30/0.98    introduced(choice_axiom,[])).
% 2.30/0.98  
% 2.30/0.98  fof(f45,plain,(
% 2.30/0.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.30/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).
% 2.30/0.98  
% 2.30/0.98  fof(f63,plain,(
% 2.30/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 2.30/0.98    inference(cnf_transformation,[],[f45])).
% 2.30/0.98  
% 2.30/0.98  fof(f97,plain,(
% 2.30/0.98    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 2.30/0.98    inference(equality_resolution,[],[f63])).
% 2.30/0.98  
% 2.30/0.98  fof(f7,axiom,(
% 2.30/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.30/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.30/0.98  
% 2.30/0.98  fof(f22,plain,(
% 2.30/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.30/0.98    inference(ennf_transformation,[],[f7])).
% 2.30/0.98  
% 2.30/0.98  fof(f70,plain,(
% 2.30/0.98    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.30/0.98    inference(cnf_transformation,[],[f22])).
% 2.30/0.98  
% 2.30/0.98  fof(f15,axiom,(
% 2.30/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 2.30/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.30/0.98  
% 2.30/0.98  fof(f32,plain,(
% 2.30/0.98    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.30/0.98    inference(ennf_transformation,[],[f15])).
% 2.30/0.98  
% 2.30/0.98  fof(f33,plain,(
% 2.30/0.98    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.30/0.98    inference(flattening,[],[f32])).
% 2.30/0.98  
% 2.30/0.98  fof(f52,plain,(
% 2.30/0.98    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.30/0.98    inference(nnf_transformation,[],[f33])).
% 2.30/0.98  
% 2.30/0.98  fof(f53,plain,(
% 2.30/0.98    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.30/0.98    inference(rectify,[],[f52])).
% 2.30/0.98  
% 2.30/0.98  fof(f54,plain,(
% 2.30/0.98    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.30/0.98    introduced(choice_axiom,[])).
% 2.30/0.98  
% 2.30/0.98  fof(f55,plain,(
% 2.30/0.98    ! [X0] : (((v1_tdlat_3(X0) | (~v3_pre_topc(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.30/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f53,f54])).
% 2.30/0.98  
% 2.30/0.98  fof(f84,plain,(
% 2.30/0.98    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.30/0.98    inference(cnf_transformation,[],[f55])).
% 2.30/0.98  
% 2.30/0.98  fof(f93,plain,(
% 2.30/0.98    l1_pre_topc(sK3)),
% 2.30/0.98    inference(cnf_transformation,[],[f60])).
% 2.30/0.98  
% 2.30/0.98  fof(f92,plain,(
% 2.30/0.98    v1_tdlat_3(sK3)),
% 2.30/0.98    inference(cnf_transformation,[],[f60])).
% 2.30/0.98  
% 2.30/0.98  fof(f91,plain,(
% 2.30/0.98    v2_pre_topc(sK3)),
% 2.30/0.98    inference(cnf_transformation,[],[f60])).
% 2.30/0.98  
% 2.30/0.98  fof(f8,axiom,(
% 2.30/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0))))),
% 2.30/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.30/0.98  
% 2.30/0.98  fof(f23,plain,(
% 2.30/0.98    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.30/0.98    inference(ennf_transformation,[],[f8])).
% 2.30/0.98  
% 2.30/0.98  fof(f46,plain,(
% 2.30/0.98    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) & (v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.30/0.98    inference(nnf_transformation,[],[f23])).
% 2.30/0.98  
% 2.30/0.98  fof(f72,plain,(
% 2.30/0.98    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.30/0.98    inference(cnf_transformation,[],[f46])).
% 2.30/0.98  
% 2.30/0.98  fof(f9,axiom,(
% 2.30/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.30/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.30/0.98  
% 2.30/0.98  fof(f24,plain,(
% 2.30/0.98    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.30/0.98    inference(ennf_transformation,[],[f9])).
% 2.30/0.98  
% 2.30/0.98  fof(f25,plain,(
% 2.30/0.98    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.30/0.98    inference(flattening,[],[f24])).
% 2.30/0.98  
% 2.30/0.98  fof(f73,plain,(
% 2.30/0.98    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.30/0.98    inference(cnf_transformation,[],[f25])).
% 2.30/0.98  
% 2.30/0.98  fof(f11,axiom,(
% 2.30/0.98    ! [X0] : (l1_pre_topc(X0) => ? [X1] : (v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.30/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.30/0.98  
% 2.30/0.98  fof(f27,plain,(
% 2.30/0.98    ! [X0] : (? [X1] : (v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.30/0.98    inference(ennf_transformation,[],[f11])).
% 2.30/0.98  
% 2.30/0.98  fof(f48,plain,(
% 2.30/0.98    ! [X0] : (? [X1] : (v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_1(sK1(X0),X0) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.30/0.98    introduced(choice_axiom,[])).
% 2.30/0.98  
% 2.30/0.98  fof(f49,plain,(
% 2.30/0.98    ! [X0] : ((v1_tops_1(sK1(X0),X0) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.30/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f48])).
% 2.30/0.98  
% 2.30/0.98  fof(f78,plain,(
% 2.30/0.98    ( ! [X0] : (v1_tops_1(sK1(X0),X0) | ~l1_pre_topc(X0)) )),
% 2.30/0.98    inference(cnf_transformation,[],[f49])).
% 2.30/0.98  
% 2.30/0.98  fof(f10,axiom,(
% 2.30/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 2.30/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.30/0.98  
% 2.30/0.98  fof(f26,plain,(
% 2.30/0.98    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.30/0.98    inference(ennf_transformation,[],[f10])).
% 2.30/0.98  
% 2.30/0.98  fof(f47,plain,(
% 2.30/0.98    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.30/0.98    inference(nnf_transformation,[],[f26])).
% 2.30/0.98  
% 2.30/0.98  fof(f75,plain,(
% 2.30/0.98    ( ! [X0,X1] : (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.30/0.98    inference(cnf_transformation,[],[f47])).
% 2.30/0.98  
% 2.30/0.98  fof(f77,plain,(
% 2.30/0.98    ( ! [X0] : (m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.30/0.98    inference(cnf_transformation,[],[f49])).
% 2.30/0.98  
% 2.30/0.98  fof(f13,axiom,(
% 2.30/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 2.30/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.30/0.98  
% 2.30/0.98  fof(f30,plain,(
% 2.30/0.98    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.30/0.98    inference(ennf_transformation,[],[f13])).
% 2.30/0.98  
% 2.30/0.98  fof(f50,plain,(
% 2.30/0.98    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.30/0.98    inference(nnf_transformation,[],[f30])).
% 2.30/0.98  
% 2.30/0.98  fof(f80,plain,(
% 2.30/0.98    ( ! [X0,X1] : (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.30/0.98    inference(cnf_transformation,[],[f50])).
% 2.30/0.98  
% 2.30/0.98  fof(f1,axiom,(
% 2.30/0.98    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.30/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.30/0.98  
% 2.30/0.98  fof(f61,plain,(
% 2.30/0.98    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.30/0.98    inference(cnf_transformation,[],[f1])).
% 2.30/0.98  
% 2.30/0.98  fof(f81,plain,(
% 2.30/0.98    ( ! [X0,X1] : (v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.30/0.98    inference(cnf_transformation,[],[f50])).
% 2.30/0.98  
% 2.30/0.98  fof(f6,axiom,(
% 2.30/0.98    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 2.30/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.30/0.98  
% 2.30/0.98  fof(f69,plain,(
% 2.30/0.98    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 2.30/0.98    inference(cnf_transformation,[],[f6])).
% 2.30/0.98  
% 2.30/0.98  fof(f96,plain,(
% 2.30/0.98    v1_subset_1(sK4,u1_struct_0(sK3)) | ~v3_tex_2(sK4,sK3)),
% 2.30/0.98    inference(cnf_transformation,[],[f60])).
% 2.30/0.98  
% 2.30/0.98  fof(f16,axiom,(
% 2.30/0.98    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 2.30/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.30/0.98  
% 2.30/0.98  fof(f34,plain,(
% 2.30/0.98    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.30/0.98    inference(ennf_transformation,[],[f16])).
% 2.30/0.98  
% 2.30/0.98  fof(f35,plain,(
% 2.30/0.98    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.30/0.98    inference(flattening,[],[f34])).
% 2.30/0.98  
% 2.30/0.98  fof(f87,plain,(
% 2.30/0.98    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.30/0.98    inference(cnf_transformation,[],[f35])).
% 2.30/0.98  
% 2.30/0.98  fof(f18,axiom,(
% 2.30/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 2.30/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.30/0.98  
% 2.30/0.98  fof(f38,plain,(
% 2.30/0.98    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) | (~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.30/0.98    inference(ennf_transformation,[],[f18])).
% 2.30/0.98  
% 2.30/0.98  fof(f39,plain,(
% 2.30/0.98    ! [X0] : (! [X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.30/0.98    inference(flattening,[],[f38])).
% 2.30/0.98  
% 2.30/0.98  fof(f89,plain,(
% 2.30/0.98    ( ! [X0,X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.30/0.98    inference(cnf_transformation,[],[f39])).
% 2.30/0.98  
% 2.30/0.98  fof(f12,axiom,(
% 2.30/0.98    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 2.30/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.30/0.98  
% 2.30/0.98  fof(f28,plain,(
% 2.30/0.98    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 2.30/0.98    inference(ennf_transformation,[],[f12])).
% 2.30/0.98  
% 2.30/0.98  fof(f29,plain,(
% 2.30/0.98    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 2.30/0.98    inference(flattening,[],[f28])).
% 2.30/0.98  
% 2.30/0.98  fof(f79,plain,(
% 2.30/0.98    ( ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 2.30/0.98    inference(cnf_transformation,[],[f29])).
% 2.30/0.98  
% 2.30/0.98  fof(f90,plain,(
% 2.30/0.98    ~v2_struct_0(sK3)),
% 2.30/0.98    inference(cnf_transformation,[],[f60])).
% 2.30/0.98  
% 2.30/0.98  fof(f14,axiom,(
% 2.30/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 2.30/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.30/0.98  
% 2.30/0.98  fof(f31,plain,(
% 2.30/0.98    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.30/0.98    inference(ennf_transformation,[],[f14])).
% 2.30/0.98  
% 2.30/0.98  fof(f51,plain,(
% 2.30/0.98    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.30/0.98    inference(nnf_transformation,[],[f31])).
% 2.30/0.98  
% 2.30/0.98  fof(f83,plain,(
% 2.30/0.98    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.30/0.98    inference(cnf_transformation,[],[f51])).
% 2.30/0.98  
% 2.30/0.98  fof(f95,plain,(
% 2.30/0.98    ~v1_subset_1(sK4,u1_struct_0(sK3)) | v3_tex_2(sK4,sK3)),
% 2.30/0.98    inference(cnf_transformation,[],[f60])).
% 2.30/0.98  
% 2.30/0.98  fof(f17,axiom,(
% 2.30/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 2.30/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.30/0.98  
% 2.30/0.98  fof(f36,plain,(
% 2.30/0.98    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.30/0.98    inference(ennf_transformation,[],[f17])).
% 2.30/0.98  
% 2.30/0.98  fof(f37,plain,(
% 2.30/0.98    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.30/0.98    inference(flattening,[],[f36])).
% 2.30/0.98  
% 2.30/0.98  fof(f88,plain,(
% 2.30/0.98    ( ! [X0,X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.30/0.98    inference(cnf_transformation,[],[f37])).
% 2.30/0.98  
% 2.30/0.98  cnf(c_31,negated_conjecture,
% 2.30/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.30/0.98      inference(cnf_transformation,[],[f94]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_2048,plain,
% 2.30/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.30/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_6,plain,
% 2.30/0.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.30/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_2051,plain,
% 2.30/0.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.30/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_5,plain,
% 2.30/0.98      ( k2_subset_1(X0) = X0 ),
% 2.30/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_2068,plain,
% 2.30/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.30/0.98      inference(light_normalisation,[status(thm)],[c_2051,c_5]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_7,plain,
% 2.30/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.30/0.98      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 2.30/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_2050,plain,
% 2.30/0.98      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 2.30/0.98      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.30/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_2643,plain,
% 2.30/0.98      ( k7_subset_1(X0,X0,X1) = k4_xboole_0(X0,X1) ),
% 2.30/0.98      inference(superposition,[status(thm)],[c_2068,c_2050]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_3,plain,
% 2.30/0.98      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.30/0.98      inference(cnf_transformation,[],[f97]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_2053,plain,
% 2.30/0.98      ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.30/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 2.30/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_9,plain,
% 2.30/0.98      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.30/0.98      inference(cnf_transformation,[],[f70]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_2049,plain,
% 2.30/0.98      ( m1_subset_1(X0,X1) = iProver_top | r2_hidden(X0,X1) != iProver_top ),
% 2.30/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_2556,plain,
% 2.30/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.30/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 2.30/0.98      inference(superposition,[status(thm)],[c_2053,c_2049]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_25,plain,
% 2.30/0.98      ( v3_pre_topc(X0,X1)
% 2.30/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.30/0.98      | ~ v1_tdlat_3(X1)
% 2.30/0.98      | ~ v2_pre_topc(X1)
% 2.30/0.98      | ~ l1_pre_topc(X1) ),
% 2.30/0.98      inference(cnf_transformation,[],[f84]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_32,negated_conjecture,
% 2.30/0.98      ( l1_pre_topc(sK3) ),
% 2.30/0.98      inference(cnf_transformation,[],[f93]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_1011,plain,
% 2.30/0.98      ( v3_pre_topc(X0,X1)
% 2.30/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.30/0.98      | ~ v1_tdlat_3(X1)
% 2.30/0.98      | ~ v2_pre_topc(X1)
% 2.30/0.98      | sK3 != X1 ),
% 2.30/0.98      inference(resolution_lifted,[status(thm)],[c_25,c_32]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_1012,plain,
% 2.30/0.98      ( v3_pre_topc(X0,sK3)
% 2.30/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.30/0.98      | ~ v1_tdlat_3(sK3)
% 2.30/0.98      | ~ v2_pre_topc(sK3) ),
% 2.30/0.98      inference(unflattening,[status(thm)],[c_1011]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_33,negated_conjecture,
% 2.30/0.98      ( v1_tdlat_3(sK3) ),
% 2.30/0.98      inference(cnf_transformation,[],[f92]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_925,plain,
% 2.30/0.98      ( v3_pre_topc(X0,X1)
% 2.30/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.30/0.98      | ~ v2_pre_topc(X1)
% 2.30/0.98      | ~ l1_pre_topc(X1)
% 2.30/0.98      | sK3 != X1 ),
% 2.30/0.98      inference(resolution_lifted,[status(thm)],[c_25,c_33]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_926,plain,
% 2.30/0.98      ( v3_pre_topc(X0,sK3)
% 2.30/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.30/0.98      | ~ v2_pre_topc(sK3)
% 2.30/0.98      | ~ l1_pre_topc(sK3) ),
% 2.30/0.98      inference(unflattening,[status(thm)],[c_925]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_34,negated_conjecture,
% 2.30/0.98      ( v2_pre_topc(sK3) ),
% 2.30/0.98      inference(cnf_transformation,[],[f91]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_930,plain,
% 2.30/0.98      ( v3_pre_topc(X0,sK3) | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.30/0.98      inference(global_propositional_subsumption,
% 2.30/0.98                [status(thm)],
% 2.30/0.98                [c_926,c_34,c_32]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_1014,plain,
% 2.30/0.98      ( v3_pre_topc(X0,sK3) | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.30/0.98      inference(global_propositional_subsumption,
% 2.30/0.98                [status(thm)],
% 2.30/0.98                [c_1012,c_34,c_32,c_926]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_10,plain,
% 2.30/0.98      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
% 2.30/0.98      | v4_pre_topc(X1,X0)
% 2.30/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.30/0.98      | ~ l1_pre_topc(X0) ),
% 2.30/0.98      inference(cnf_transformation,[],[f72]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_13,plain,
% 2.30/0.98      ( ~ v4_pre_topc(X0,X1)
% 2.30/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.30/0.98      | ~ l1_pre_topc(X1)
% 2.30/0.98      | k2_pre_topc(X1,X0) = X0 ),
% 2.30/0.98      inference(cnf_transformation,[],[f73]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_829,plain,
% 2.30/0.98      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
% 2.30/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.30/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.30/0.98      | ~ l1_pre_topc(X0)
% 2.30/0.98      | ~ l1_pre_topc(X3)
% 2.30/0.98      | X2 != X1
% 2.30/0.98      | X3 != X0
% 2.30/0.98      | k2_pre_topc(X3,X2) = X2 ),
% 2.30/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_13]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_830,plain,
% 2.30/0.98      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
% 2.30/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.30/0.98      | ~ l1_pre_topc(X0)
% 2.30/0.98      | k2_pre_topc(X0,X1) = X1 ),
% 2.30/0.98      inference(unflattening,[status(thm)],[c_829]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_976,plain,
% 2.30/0.98      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
% 2.30/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.30/0.98      | k2_pre_topc(X0,X1) = X1
% 2.30/0.98      | sK3 != X0 ),
% 2.30/0.98      inference(resolution_lifted,[status(thm)],[c_830,c_32]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_977,plain,
% 2.30/0.98      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK3),k2_struct_0(sK3),X0),sK3)
% 2.30/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.30/0.98      | k2_pre_topc(sK3,X0) = X0 ),
% 2.30/0.98      inference(unflattening,[status(thm)],[c_976]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_1131,plain,
% 2.30/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.30/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.30/0.98      | k7_subset_1(u1_struct_0(sK3),k2_struct_0(sK3),X1) != X0
% 2.30/0.98      | k2_pre_topc(sK3,X1) = X1
% 2.30/0.98      | sK3 != sK3 ),
% 2.30/0.98      inference(resolution_lifted,[status(thm)],[c_1014,c_977]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_1132,plain,
% 2.30/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.30/0.98      | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK3),k2_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.30/0.98      | k2_pre_topc(sK3,X0) = X0 ),
% 2.30/0.98      inference(unflattening,[status(thm)],[c_1131]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_2046,plain,
% 2.30/0.98      ( k2_pre_topc(sK3,X0) = X0
% 2.30/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.30/0.98      | m1_subset_1(k7_subset_1(u1_struct_0(sK3),k2_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.30/0.98      inference(predicate_to_equality,[status(thm)],[c_1132]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_16,plain,
% 2.30/0.98      ( v1_tops_1(sK1(X0),X0) | ~ l1_pre_topc(X0) ),
% 2.30/0.98      inference(cnf_transformation,[],[f78]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_1004,plain,
% 2.30/0.98      ( v1_tops_1(sK1(X0),X0) | sK3 != X0 ),
% 2.30/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_32]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_1005,plain,
% 2.30/0.98      ( v1_tops_1(sK1(sK3),sK3) ),
% 2.30/0.98      inference(unflattening,[status(thm)],[c_1004]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_15,plain,
% 2.30/0.98      ( ~ v1_tops_1(X0,X1)
% 2.30/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.30/0.98      | ~ l1_pre_topc(X1)
% 2.30/0.98      | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
% 2.30/0.98      inference(cnf_transformation,[],[f75]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_1055,plain,
% 2.30/0.98      ( ~ v1_tops_1(X0,X1)
% 2.30/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.30/0.98      | k2_pre_topc(X1,X0) = k2_struct_0(X1)
% 2.30/0.98      | sK3 != X1 ),
% 2.30/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_32]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_1056,plain,
% 2.30/0.98      ( ~ v1_tops_1(X0,sK3)
% 2.30/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.30/0.98      | k2_pre_topc(sK3,X0) = k2_struct_0(sK3) ),
% 2.30/0.98      inference(unflattening,[status(thm)],[c_1055]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_1191,plain,
% 2.30/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.30/0.98      | k2_pre_topc(sK3,X0) = k2_struct_0(sK3)
% 2.30/0.98      | sK1(sK3) != X0
% 2.30/0.98      | sK3 != sK3 ),
% 2.30/0.98      inference(resolution_lifted,[status(thm)],[c_1005,c_1056]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_1192,plain,
% 2.30/0.98      ( ~ m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.30/0.98      | k2_pre_topc(sK3,sK1(sK3)) = k2_struct_0(sK3) ),
% 2.30/0.98      inference(unflattening,[status(thm)],[c_1191]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_17,plain,
% 2.30/0.98      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~ l1_pre_topc(X0) ),
% 2.30/0.98      inference(cnf_transformation,[],[f77]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_71,plain,
% 2.30/0.98      ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.30/0.98      | ~ l1_pre_topc(sK3) ),
% 2.30/0.98      inference(instantiation,[status(thm)],[c_17]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_1194,plain,
% 2.30/0.98      ( k2_pre_topc(sK3,sK1(sK3)) = k2_struct_0(sK3) ),
% 2.30/0.98      inference(global_propositional_subsumption,
% 2.30/0.98                [status(thm)],
% 2.30/0.98                [c_1192,c_32,c_71]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_20,plain,
% 2.30/0.98      ( ~ v1_tops_1(X0,X1)
% 2.30/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.30/0.98      | ~ l1_pre_topc(X1)
% 2.30/0.98      | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
% 2.30/0.98      inference(cnf_transformation,[],[f80]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_1025,plain,
% 2.30/0.98      ( ~ v1_tops_1(X0,X1)
% 2.30/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.30/0.98      | k2_pre_topc(X1,X0) = u1_struct_0(X1)
% 2.30/0.98      | sK3 != X1 ),
% 2.30/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_32]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_1026,plain,
% 2.30/0.98      ( ~ v1_tops_1(X0,sK3)
% 2.30/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.30/0.98      | k2_pre_topc(sK3,X0) = u1_struct_0(sK3) ),
% 2.30/0.98      inference(unflattening,[status(thm)],[c_1025]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_1199,plain,
% 2.30/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.30/0.98      | k2_pre_topc(sK3,X0) = u1_struct_0(sK3)
% 2.30/0.98      | sK1(sK3) != X0
% 2.30/0.98      | sK3 != sK3 ),
% 2.30/0.98      inference(resolution_lifted,[status(thm)],[c_1005,c_1026]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_1200,plain,
% 2.30/0.98      ( ~ m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.30/0.98      | k2_pre_topc(sK3,sK1(sK3)) = u1_struct_0(sK3) ),
% 2.30/0.98      inference(unflattening,[status(thm)],[c_1199]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_1202,plain,
% 2.30/0.98      ( k2_pre_topc(sK3,sK1(sK3)) = u1_struct_0(sK3) ),
% 2.30/0.98      inference(global_propositional_subsumption,
% 2.30/0.98                [status(thm)],
% 2.30/0.98                [c_1200,c_32,c_71]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_2063,plain,
% 2.30/0.98      ( k2_struct_0(sK3) = u1_struct_0(sK3) ),
% 2.30/0.98      inference(light_normalisation,[status(thm)],[c_1194,c_1202]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_2124,plain,
% 2.30/0.98      ( k2_pre_topc(sK3,X0) = X0
% 2.30/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.30/0.98      | m1_subset_1(k7_subset_1(u1_struct_0(sK3),u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.30/0.98      inference(light_normalisation,[status(thm)],[c_2046,c_2063]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_2565,plain,
% 2.30/0.98      ( k2_pre_topc(sK3,X0) = X0
% 2.30/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.30/0.98      | r1_tarski(k7_subset_1(u1_struct_0(sK3),u1_struct_0(sK3),X0),u1_struct_0(sK3)) != iProver_top ),
% 2.30/0.98      inference(superposition,[status(thm)],[c_2556,c_2124]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_2852,plain,
% 2.30/0.98      ( k2_pre_topc(sK3,X0) = X0
% 2.30/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.30/0.98      | r1_tarski(k4_xboole_0(u1_struct_0(sK3),X0),u1_struct_0(sK3)) != iProver_top ),
% 2.30/0.98      inference(demodulation,[status(thm)],[c_2643,c_2565]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_0,plain,
% 2.30/0.98      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 2.30/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_2056,plain,
% 2.30/0.98      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 2.30/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_3043,plain,
% 2.30/0.98      ( k2_pre_topc(sK3,X0) = X0
% 2.30/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.30/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_2852,c_2056]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_3049,plain,
% 2.30/0.98      ( k2_pre_topc(sK3,sK4) = sK4 ),
% 2.30/0.98      inference(superposition,[status(thm)],[c_2048,c_3043]) ).
% 2.30/0.98  
% 2.30/0.98  cnf(c_19,plain,
% 2.30/0.98      ( v1_tops_1(X0,X1)
% 2.30/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.30/0.98      | ~ l1_pre_topc(X1)
% 2.30/0.98      | k2_pre_topc(X1,X0) != u1_struct_0(X1) ),
% 2.30/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_1040,plain,
% 2.30/0.99      ( v1_tops_1(X0,X1)
% 2.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.30/0.99      | k2_pre_topc(X1,X0) != u1_struct_0(X1)
% 2.30/0.99      | sK3 != X1 ),
% 2.30/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_32]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_1041,plain,
% 2.30/0.99      ( v1_tops_1(X0,sK3)
% 2.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.30/0.99      | k2_pre_topc(sK3,X0) != u1_struct_0(sK3) ),
% 2.30/0.99      inference(unflattening,[status(thm)],[c_1040]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_8,plain,
% 2.30/0.99      ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
% 2.30/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_29,negated_conjecture,
% 2.30/0.99      ( ~ v3_tex_2(sK4,sK3) | v1_subset_1(sK4,u1_struct_0(sK3)) ),
% 2.30/0.99      inference(cnf_transformation,[],[f96]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_277,plain,
% 2.30/0.99      ( ~ v3_tex_2(sK4,sK3) | v1_subset_1(sK4,u1_struct_0(sK3)) ),
% 2.30/0.99      inference(prop_impl,[status(thm)],[c_29]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_571,plain,
% 2.30/0.99      ( ~ v3_tex_2(sK4,sK3) | u1_struct_0(sK3) != X0 | k2_subset_1(X0) != sK4 ),
% 2.30/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_277]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_572,plain,
% 2.30/0.99      ( ~ v3_tex_2(sK4,sK3) | k2_subset_1(u1_struct_0(sK3)) != sK4 ),
% 2.30/0.99      inference(unflattening,[status(thm)],[c_571]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_26,plain,
% 2.30/0.99      ( v2_tex_2(X0,X1)
% 2.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.30/0.99      | v2_struct_0(X1)
% 2.30/0.99      | ~ v1_tdlat_3(X1)
% 2.30/0.99      | ~ v2_pre_topc(X1)
% 2.30/0.99      | ~ l1_pre_topc(X1) ),
% 2.30/0.99      inference(cnf_transformation,[],[f87]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_28,plain,
% 2.30/0.99      ( v3_tex_2(X0,X1)
% 2.30/0.99      | ~ v2_tex_2(X0,X1)
% 2.30/0.99      | ~ v1_tops_1(X0,X1)
% 2.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.30/0.99      | v2_struct_0(X1)
% 2.30/0.99      | ~ v2_pre_topc(X1)
% 2.30/0.99      | ~ l1_pre_topc(X1) ),
% 2.30/0.99      inference(cnf_transformation,[],[f89]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_470,plain,
% 2.30/0.99      ( v3_tex_2(X0,X1)
% 2.30/0.99      | ~ v1_tops_1(X0,X1)
% 2.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.30/0.99      | v2_struct_0(X1)
% 2.30/0.99      | ~ v1_tdlat_3(X1)
% 2.30/0.99      | ~ v2_pre_topc(X1)
% 2.30/0.99      | ~ l1_pre_topc(X1) ),
% 2.30/0.99      inference(resolution,[status(thm)],[c_26,c_28]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_18,plain,
% 2.30/0.99      ( ~ v1_tdlat_3(X0) | v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 2.30/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_488,plain,
% 2.30/0.99      ( v3_tex_2(X0,X1)
% 2.30/0.99      | ~ v1_tops_1(X0,X1)
% 2.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.30/0.99      | v2_struct_0(X1)
% 2.30/0.99      | ~ v1_tdlat_3(X1)
% 2.30/0.99      | ~ l1_pre_topc(X1) ),
% 2.30/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_470,c_18]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_35,negated_conjecture,
% 2.30/0.99      ( ~ v2_struct_0(sK3) ),
% 2.30/0.99      inference(cnf_transformation,[],[f90]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_505,plain,
% 2.30/0.99      ( v3_tex_2(X0,X1)
% 2.30/0.99      | ~ v1_tops_1(X0,X1)
% 2.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.30/0.99      | ~ v1_tdlat_3(X1)
% 2.30/0.99      | ~ l1_pre_topc(X1)
% 2.30/0.99      | sK3 != X1 ),
% 2.30/0.99      inference(resolution_lifted,[status(thm)],[c_488,c_35]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_506,plain,
% 2.30/0.99      ( v3_tex_2(X0,sK3)
% 2.30/0.99      | ~ v1_tops_1(X0,sK3)
% 2.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.30/0.99      | ~ v1_tdlat_3(sK3)
% 2.30/0.99      | ~ l1_pre_topc(sK3) ),
% 2.30/0.99      inference(unflattening,[status(thm)],[c_505]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_510,plain,
% 2.30/0.99      ( v3_tex_2(X0,sK3)
% 2.30/0.99      | ~ v1_tops_1(X0,sK3)
% 2.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.30/0.99      inference(global_propositional_subsumption,
% 2.30/0.99                [status(thm)],
% 2.30/0.99                [c_506,c_33,c_32]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_800,plain,
% 2.30/0.99      ( ~ v1_tops_1(X0,sK3)
% 2.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.30/0.99      | k2_subset_1(u1_struct_0(sK3)) != sK4
% 2.30/0.99      | sK3 != sK3
% 2.30/0.99      | sK4 != X0 ),
% 2.30/0.99      inference(resolution_lifted,[status(thm)],[c_572,c_510]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_801,plain,
% 2.30/0.99      ( ~ v1_tops_1(sK4,sK3)
% 2.30/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.30/0.99      | k2_subset_1(u1_struct_0(sK3)) != sK4 ),
% 2.30/0.99      inference(unflattening,[status(thm)],[c_800]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_803,plain,
% 2.30/0.99      ( ~ v1_tops_1(sK4,sK3) | k2_subset_1(u1_struct_0(sK3)) != sK4 ),
% 2.30/0.99      inference(global_propositional_subsumption,[status(thm)],[c_801,c_31]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_1260,plain,
% 2.30/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.30/0.99      | k2_pre_topc(sK3,X0) != u1_struct_0(sK3)
% 2.30/0.99      | k2_subset_1(u1_struct_0(sK3)) != sK4
% 2.30/0.99      | sK3 != sK3
% 2.30/0.99      | sK4 != X0 ),
% 2.30/0.99      inference(resolution_lifted,[status(thm)],[c_1041,c_803]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_1261,plain,
% 2.30/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.30/0.99      | k2_pre_topc(sK3,sK4) != u1_struct_0(sK3)
% 2.30/0.99      | k2_subset_1(u1_struct_0(sK3)) != sK4 ),
% 2.30/0.99      inference(unflattening,[status(thm)],[c_1260]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_1263,plain,
% 2.30/0.99      ( k2_pre_topc(sK3,sK4) != u1_struct_0(sK3)
% 2.30/0.99      | k2_subset_1(u1_struct_0(sK3)) != sK4 ),
% 2.30/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1261,c_31]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_2098,plain,
% 2.30/0.99      ( k2_pre_topc(sK3,sK4) != u1_struct_0(sK3) | u1_struct_0(sK3) != sK4 ),
% 2.30/0.99      inference(demodulation,[status(thm)],[c_1263,c_5]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_3066,plain,
% 2.30/0.99      ( u1_struct_0(sK3) != sK4 ),
% 2.30/0.99      inference(demodulation,[status(thm)],[c_3049,c_2098]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_21,plain,
% 2.30/0.99      ( v1_subset_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | X0 = X1 ),
% 2.30/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_30,negated_conjecture,
% 2.30/0.99      ( v3_tex_2(sK4,sK3) | ~ v1_subset_1(sK4,u1_struct_0(sK3)) ),
% 2.30/0.99      inference(cnf_transformation,[],[f95]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_275,plain,
% 2.30/0.99      ( v3_tex_2(sK4,sK3) | ~ v1_subset_1(sK4,u1_struct_0(sK3)) ),
% 2.30/0.99      inference(prop_impl,[status(thm)],[c_30]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_583,plain,
% 2.30/0.99      ( v3_tex_2(sK4,sK3)
% 2.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.30/0.99      | X1 = X0
% 2.30/0.99      | u1_struct_0(sK3) != X1
% 2.30/0.99      | sK4 != X0 ),
% 2.30/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_275]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_584,plain,
% 2.30/0.99      ( v3_tex_2(sK4,sK3)
% 2.30/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.30/0.99      | u1_struct_0(sK3) = sK4 ),
% 2.30/0.99      inference(unflattening,[status(thm)],[c_583]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_586,plain,
% 2.30/0.99      ( v3_tex_2(sK4,sK3) | u1_struct_0(sK3) = sK4 ),
% 2.30/0.99      inference(global_propositional_subsumption,[status(thm)],[c_584,c_31]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_27,plain,
% 2.30/0.99      ( ~ v3_tex_2(X0,X1)
% 2.30/0.99      | v1_tops_1(X0,X1)
% 2.30/0.99      | ~ v3_pre_topc(X0,X1)
% 2.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.30/0.99      | v2_struct_0(X1)
% 2.30/0.99      | ~ v2_pre_topc(X1)
% 2.30/0.99      | ~ l1_pre_topc(X1) ),
% 2.30/0.99      inference(cnf_transformation,[],[f88]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_526,plain,
% 2.30/0.99      ( ~ v3_tex_2(X0,X1)
% 2.30/0.99      | v1_tops_1(X0,X1)
% 2.30/0.99      | ~ v3_pre_topc(X0,X1)
% 2.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.30/0.99      | ~ v2_pre_topc(X1)
% 2.30/0.99      | ~ l1_pre_topc(X1)
% 2.30/0.99      | sK3 != X1 ),
% 2.30/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_35]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_527,plain,
% 2.30/0.99      ( ~ v3_tex_2(X0,sK3)
% 2.30/0.99      | v1_tops_1(X0,sK3)
% 2.30/0.99      | ~ v3_pre_topc(X0,sK3)
% 2.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.30/0.99      | ~ v2_pre_topc(sK3)
% 2.30/0.99      | ~ l1_pre_topc(sK3) ),
% 2.30/0.99      inference(unflattening,[status(thm)],[c_526]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_531,plain,
% 2.30/0.99      ( ~ v3_tex_2(X0,sK3)
% 2.30/0.99      | v1_tops_1(X0,sK3)
% 2.30/0.99      | ~ v3_pre_topc(X0,sK3)
% 2.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.30/0.99      inference(global_propositional_subsumption,
% 2.30/0.99                [status(thm)],
% 2.30/0.99                [c_527,c_34,c_32]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_766,plain,
% 2.30/0.99      ( v1_tops_1(X0,sK3)
% 2.30/0.99      | ~ v3_pre_topc(X0,sK3)
% 2.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.30/0.99      | u1_struct_0(sK3) = sK4
% 2.30/0.99      | sK3 != sK3
% 2.30/0.99      | sK4 != X0 ),
% 2.30/0.99      inference(resolution_lifted,[status(thm)],[c_586,c_531]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_767,plain,
% 2.30/0.99      ( v1_tops_1(sK4,sK3)
% 2.30/0.99      | ~ v3_pre_topc(sK4,sK3)
% 2.30/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.30/0.99      | u1_struct_0(sK3) = sK4 ),
% 2.30/0.99      inference(unflattening,[status(thm)],[c_766]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_769,plain,
% 2.30/0.99      ( ~ v3_pre_topc(sK4,sK3) | v1_tops_1(sK4,sK3) | u1_struct_0(sK3) = sK4 ),
% 2.30/0.99      inference(global_propositional_subsumption,[status(thm)],[c_767,c_31]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_770,plain,
% 2.30/0.99      ( v1_tops_1(sK4,sK3) | ~ v3_pre_topc(sK4,sK3) | u1_struct_0(sK3) = sK4 ),
% 2.30/0.99      inference(renaming,[status(thm)],[c_769]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_1117,plain,
% 2.30/0.99      ( v1_tops_1(sK4,sK3)
% 2.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.30/0.99      | u1_struct_0(sK3) = sK4
% 2.30/0.99      | sK3 != sK3
% 2.30/0.99      | sK4 != X0 ),
% 2.30/0.99      inference(resolution_lifted,[status(thm)],[c_1014,c_770]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_1118,plain,
% 2.30/0.99      ( v1_tops_1(sK4,sK3)
% 2.30/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.30/0.99      | u1_struct_0(sK3) = sK4 ),
% 2.30/0.99      inference(unflattening,[status(thm)],[c_1117]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_1120,plain,
% 2.30/0.99      ( v1_tops_1(sK4,sK3) | u1_struct_0(sK3) = sK4 ),
% 2.30/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1118,c_31]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_1299,plain,
% 2.30/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.30/0.99      | k2_pre_topc(sK3,X0) = u1_struct_0(sK3)
% 2.30/0.99      | u1_struct_0(sK3) = sK4
% 2.30/0.99      | sK3 != sK3
% 2.30/0.99      | sK4 != X0 ),
% 2.30/0.99      inference(resolution_lifted,[status(thm)],[c_1026,c_1120]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_1300,plain,
% 2.30/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.30/0.99      | k2_pre_topc(sK3,sK4) = u1_struct_0(sK3)
% 2.30/0.99      | u1_struct_0(sK3) = sK4 ),
% 2.30/0.99      inference(unflattening,[status(thm)],[c_1299]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_1302,plain,
% 2.30/0.99      ( k2_pre_topc(sK3,sK4) = u1_struct_0(sK3) | u1_struct_0(sK3) = sK4 ),
% 2.30/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1300,c_31]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_3067,plain,
% 2.30/0.99      ( u1_struct_0(sK3) = sK4 ),
% 2.30/0.99      inference(demodulation,[status(thm)],[c_3049,c_1302]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_3070,plain,
% 2.30/0.99      ( sK4 != sK4 ),
% 2.30/0.99      inference(light_normalisation,[status(thm)],[c_3066,c_3067]) ).
% 2.30/0.99  
% 2.30/0.99  cnf(c_3071,plain,
% 2.30/0.99      ( $false ),
% 2.30/0.99      inference(equality_resolution_simp,[status(thm)],[c_3070]) ).
% 2.30/0.99  
% 2.30/0.99  
% 2.30/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.30/0.99  
% 2.30/0.99  ------                               Statistics
% 2.30/0.99  
% 2.30/0.99  ------ General
% 2.30/0.99  
% 2.30/0.99  abstr_ref_over_cycles:                  0
% 2.30/0.99  abstr_ref_under_cycles:                 0
% 2.30/0.99  gc_basic_clause_elim:                   0
% 2.30/0.99  forced_gc_time:                         0
% 2.30/0.99  parsing_time:                           0.012
% 2.30/0.99  unif_index_cands_time:                  0.
% 2.30/0.99  unif_index_add_time:                    0.
% 2.30/0.99  orderings_time:                         0.
% 2.30/0.99  out_proof_time:                         0.015
% 2.30/0.99  total_time:                             0.116
% 2.30/0.99  num_of_symbols:                         56
% 2.30/0.99  num_of_terms:                           1695
% 2.30/0.99  
% 2.30/0.99  ------ Preprocessing
% 2.30/0.99  
% 2.30/0.99  num_of_splits:                          0
% 2.30/0.99  num_of_split_atoms:                     0
% 2.30/0.99  num_of_reused_defs:                     0
% 2.30/0.99  num_eq_ax_congr_red:                    30
% 2.30/0.99  num_of_sem_filtered_clauses:            1
% 2.30/0.99  num_of_subtypes:                        0
% 2.30/0.99  monotx_restored_types:                  0
% 2.30/0.99  sat_num_of_epr_types:                   0
% 2.30/0.99  sat_num_of_non_cyclic_types:            0
% 2.30/0.99  sat_guarded_non_collapsed_types:        0
% 2.30/0.99  num_pure_diseq_elim:                    0
% 2.30/0.99  simp_replaced_by:                       0
% 2.30/0.99  res_preprocessed:                       139
% 2.30/0.99  prep_upred:                             0
% 2.30/0.99  prep_unflattend:                        73
% 2.30/0.99  smt_new_axioms:                         0
% 2.30/0.99  pred_elim_cands:                        3
% 2.30/0.99  pred_elim:                              10
% 2.30/0.99  pred_elim_cl:                           10
% 2.30/0.99  pred_elim_cycles:                       16
% 2.30/0.99  merged_defs:                            10
% 2.30/0.99  merged_defs_ncl:                        0
% 2.30/0.99  bin_hyper_res:                          10
% 2.30/0.99  prep_cycles:                            4
% 2.30/0.99  pred_elim_time:                         0.017
% 2.30/0.99  splitting_time:                         0.
% 2.30/0.99  sem_filter_time:                        0.
% 2.30/0.99  monotx_time:                            0.
% 2.30/0.99  subtype_inf_time:                       0.
% 2.30/0.99  
% 2.30/0.99  ------ Problem properties
% 2.30/0.99  
% 2.30/0.99  clauses:                                26
% 2.30/0.99  conjectures:                            1
% 2.30/0.99  epr:                                    1
% 2.30/0.99  horn:                                   23
% 2.30/0.99  ground:                                 13
% 2.30/0.99  unary:                                  8
% 2.30/0.99  binary:                                 10
% 2.30/0.99  lits:                                   52
% 2.30/0.99  lits_eq:                                30
% 2.30/0.99  fd_pure:                                0
% 2.30/0.99  fd_pseudo:                              0
% 2.30/0.99  fd_cond:                                0
% 2.30/0.99  fd_pseudo_cond:                         2
% 2.30/0.99  ac_symbols:                             0
% 2.30/0.99  
% 2.30/0.99  ------ Propositional Solver
% 2.30/0.99  
% 2.30/0.99  prop_solver_calls:                      26
% 2.30/0.99  prop_fast_solver_calls:                 924
% 2.30/0.99  smt_solver_calls:                       0
% 2.30/0.99  smt_fast_solver_calls:                  0
% 2.30/0.99  prop_num_of_clauses:                    796
% 2.30/0.99  prop_preprocess_simplified:             3954
% 2.30/0.99  prop_fo_subsumed:                       27
% 2.30/0.99  prop_solver_time:                       0.
% 2.30/0.99  smt_solver_time:                        0.
% 2.30/0.99  smt_fast_solver_time:                   0.
% 2.30/0.99  prop_fast_solver_time:                  0.
% 2.30/0.99  prop_unsat_core_time:                   0.
% 2.30/0.99  
% 2.30/0.99  ------ QBF
% 2.30/0.99  
% 2.30/0.99  qbf_q_res:                              0
% 2.30/0.99  qbf_num_tautologies:                    0
% 2.30/0.99  qbf_prep_cycles:                        0
% 2.30/0.99  
% 2.30/0.99  ------ BMC1
% 2.30/0.99  
% 2.30/0.99  bmc1_current_bound:                     -1
% 2.30/0.99  bmc1_last_solved_bound:                 -1
% 2.30/0.99  bmc1_unsat_core_size:                   -1
% 2.30/0.99  bmc1_unsat_core_parents_size:           -1
% 2.30/0.99  bmc1_merge_next_fun:                    0
% 2.30/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.30/0.99  
% 2.30/0.99  ------ Instantiation
% 2.30/0.99  
% 2.30/0.99  inst_num_of_clauses:                    213
% 2.30/0.99  inst_num_in_passive:                    43
% 2.30/0.99  inst_num_in_active:                     120
% 2.30/0.99  inst_num_in_unprocessed:                50
% 2.30/0.99  inst_num_of_loops:                      140
% 2.30/0.99  inst_num_of_learning_restarts:          0
% 2.30/0.99  inst_num_moves_active_passive:          18
% 2.30/0.99  inst_lit_activity:                      0
% 2.30/0.99  inst_lit_activity_moves:                0
% 2.30/0.99  inst_num_tautologies:                   0
% 2.30/0.99  inst_num_prop_implied:                  0
% 2.30/0.99  inst_num_existing_simplified:           0
% 2.30/0.99  inst_num_eq_res_simplified:             0
% 2.30/0.99  inst_num_child_elim:                    0
% 2.30/0.99  inst_num_of_dismatching_blockings:      19
% 2.30/0.99  inst_num_of_non_proper_insts:           136
% 2.30/0.99  inst_num_of_duplicates:                 0
% 2.30/0.99  inst_inst_num_from_inst_to_res:         0
% 2.30/0.99  inst_dismatching_checking_time:         0.
% 2.30/0.99  
% 2.30/0.99  ------ Resolution
% 2.30/0.99  
% 2.30/0.99  res_num_of_clauses:                     0
% 2.30/0.99  res_num_in_passive:                     0
% 2.30/0.99  res_num_in_active:                      0
% 2.30/0.99  res_num_of_loops:                       143
% 2.30/0.99  res_forward_subset_subsumed:            24
% 2.30/0.99  res_backward_subset_subsumed:           0
% 2.30/0.99  res_forward_subsumed:                   1
% 2.30/0.99  res_backward_subsumed:                  0
% 2.30/0.99  res_forward_subsumption_resolution:     1
% 2.30/0.99  res_backward_subsumption_resolution:    0
% 2.30/0.99  res_clause_to_clause_subsumption:       87
% 2.30/0.99  res_orphan_elimination:                 0
% 2.30/0.99  res_tautology_del:                      55
% 2.30/0.99  res_num_eq_res_simplified:              2
% 2.30/0.99  res_num_sel_changes:                    0
% 2.30/0.99  res_moves_from_active_to_pass:          0
% 2.30/0.99  
% 2.30/0.99  ------ Superposition
% 2.30/0.99  
% 2.30/0.99  sup_time_total:                         0.
% 2.30/0.99  sup_time_generating:                    0.
% 2.30/0.99  sup_time_sim_full:                      0.
% 2.30/0.99  sup_time_sim_immed:                     0.
% 2.30/0.99  
% 2.30/0.99  sup_num_of_clauses:                     31
% 2.30/0.99  sup_num_in_active:                      22
% 2.30/0.99  sup_num_in_passive:                     9
% 2.30/0.99  sup_num_of_loops:                       27
% 2.30/0.99  sup_fw_superposition:                   14
% 2.30/0.99  sup_bw_superposition:                   5
% 2.30/0.99  sup_immediate_simplified:               1
% 2.30/0.99  sup_given_eliminated:                   0
% 2.30/0.99  comparisons_done:                       0
% 2.30/0.99  comparisons_avoided:                    0
% 2.30/0.99  
% 2.30/0.99  ------ Simplifications
% 2.30/0.99  
% 2.30/0.99  
% 2.30/0.99  sim_fw_subset_subsumed:                 2
% 2.30/0.99  sim_bw_subset_subsumed:                 1
% 2.30/0.99  sim_fw_subsumed:                        1
% 2.30/0.99  sim_bw_subsumed:                        0
% 2.30/0.99  sim_fw_subsumption_res:                 1
% 2.30/0.99  sim_bw_subsumption_res:                 0
% 2.30/0.99  sim_tautology_del:                      6
% 2.30/0.99  sim_eq_tautology_del:                   0
% 2.30/0.99  sim_eq_res_simp:                        0
% 2.30/0.99  sim_fw_demodulated:                     4
% 2.30/0.99  sim_bw_demodulated:                     4
% 2.30/0.99  sim_light_normalised:                   10
% 2.30/0.99  sim_joinable_taut:                      0
% 2.30/0.99  sim_joinable_simp:                      0
% 2.30/0.99  sim_ac_normalised:                      0
% 2.30/0.99  sim_smt_subsumption:                    0
% 2.30/0.99  
%------------------------------------------------------------------------------
