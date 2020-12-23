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
% DateTime   : Thu Dec  3 12:26:53 EST 2020

% Result     : Theorem 7.54s
% Output     : CNFRefutation 7.54s
% Verified   : 
% Statistics : Number of formulae       :  271 (11721 expanded)
%              Number of clauses        :  163 (2495 expanded)
%              Number of leaves         :   24 (2705 expanded)
%              Depth                    :   29
%              Number of atoms          : 1121 (88152 expanded)
%              Number of equality atoms :  317 (5534 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
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

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f52,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f70,plain,(
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
    inference(nnf_transformation,[],[f53])).

fof(f71,plain,(
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
    inference(flattening,[],[f70])).

fof(f73,plain,(
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

fof(f72,plain,
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

fof(f74,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f71,f73,f72])).

fof(f114,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f74])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f13,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f62,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X1] :
              ( k6_domain_1(X0,X1) = X0
              & m1_subset_1(X1,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f63,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X2] :
              ( k6_domain_1(X0,X2) = X0
              & m1_subset_1(X2,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f62])).

fof(f64,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK1(X0)) = X0
        & m1_subset_1(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK1(X0)) = X0
            & m1_subset_1(sK1(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f63,f64])).

fof(f96,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0),X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f60,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f54])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f55,f56])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f115,plain,
    ( v1_zfmisc_1(sK4)
    | v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f74])).

fof(f14,axiom,(
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

fof(f22,plain,(
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
    inference(pure_predicate_removal,[],[f14])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f66,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK2(X0,X1)) = X1
        & m1_pre_topc(sK2(X0,X1),X0)
        & ~ v2_struct_0(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK2(X0,X1)) = X1
            & m1_pre_topc(sK2(X0,X1),X0)
            & ~ v2_struct_0(sK2(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f66])).

fof(f101,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK2(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f109,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f74])).

fof(f112,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f74])).

fof(f113,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f74])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_tex_2(X2,X0)
                  | ~ v1_tdlat_3(X1) )
                & ( v1_tdlat_3(X1)
                  | ~ v2_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_tex_2(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f120,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_tex_2(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f102])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f92,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f108,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f116,plain,
    ( ~ v1_zfmisc_1(sK4)
    | ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f74])).

fof(f100,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK2(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

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

fof(f37,plain,(
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

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v1_tdlat_3(X1)
      | v7_struct_0(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f88,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f90,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f89,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f93,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f111,plain,(
    v2_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f74])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f119,plain,(
    ! [X0,X1] :
      ( v2_tex_2(u1_struct_0(X1),X0)
      | ~ v1_tdlat_3(X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f103])).

fof(f97,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK1(X0)) = X0
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_struct_0(X0) = X1
           => ( v2_tex_2(X1,X0)
            <=> v1_tdlat_3(X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_tdlat_3(X0) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_tdlat_3(X0) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ~ v1_tdlat_3(X0) )
            & ( v1_tdlat_3(X0)
              | ~ v2_tex_2(X1,X0) ) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f104,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X0)
      | ~ v2_tex_2(X1,X0)
      | u1_struct_0(X0) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f122,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | ~ v2_tex_2(u1_struct_0(X0),X0)
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f104])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f106,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f110,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f74])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f58])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f117,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f79])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f107,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_7141,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_7155,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_7575,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7141,c_7155])).

cnf(c_23,plain,
    ( m1_subset_1(sK1(X0),X0)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_7150,plain,
    ( m1_subset_1(sK1(X0),X0) = iProver_top
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_7157,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8654,plain,
    ( r2_hidden(sK1(X0),X0) = iProver_top
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7150,c_7157])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_7164,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_10150,plain,
    ( r2_hidden(sK1(X0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8654,c_7164])).

cnf(c_9,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_7158,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_14177,plain,
    ( m1_subset_1(sK1(X0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_10150,c_7158])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_7153,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_20028,plain,
    ( k6_domain_1(X0,sK1(X1)) = k1_tarski(sK1(X1))
    | r1_tarski(X1,X0) != iProver_top
    | v1_zfmisc_1(X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_14177,c_7153])).

cnf(c_30596,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK1(sK4)) = k1_tarski(sK1(sK4))
    | v1_zfmisc_1(sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_7575,c_20028])).

cnf(c_35,negated_conjecture,
    ( v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(sK4) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_7142,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK2(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_7149,plain,
    ( u1_struct_0(sK2(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_9212,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_7141,c_7149])).

cnf(c_41,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_38,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_37,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_7537,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(sK4)
    | u1_struct_0(sK2(X0,sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_7539,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(sK4)
    | u1_struct_0(sK2(sK3,sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_7537])).

cnf(c_9429,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9212,c_41,c_38,c_37,c_36,c_7539])).

cnf(c_28,plain,
    ( ~ v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v1_tdlat_3(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_7145,plain,
    ( v2_tex_2(u1_struct_0(X0),X1) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v1_tdlat_3(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_9925,plain,
    ( v2_tex_2(u1_struct_0(sK2(sK3,sK4)),X0) != iProver_top
    | m1_pre_topc(sK2(sK3,sK4),X0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2(sK3,sK4)) = iProver_top
    | v1_tdlat_3(sK2(sK3,sK4)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9429,c_7145])).

cnf(c_9948,plain,
    ( v2_tex_2(sK4,X0) != iProver_top
    | m1_pre_topc(sK2(sK3,sK4),X0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2(sK3,sK4)) = iProver_top
    | v1_tdlat_3(sK2(sK3,sK4)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9925,c_9429])).

cnf(c_42,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_45,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_46,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_47,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK2(X1,X0))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_7524,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK2(X0,sK4))
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_7525,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2(X0,sK4)) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7524])).

cnf(c_7527,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK2(sK3,sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7525])).

cnf(c_17,plain,
    ( ~ v1_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_33,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_765,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X2)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_33])).

cnf(c_766,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_765])).

cnf(c_7135,plain,
    ( v2_tex_2(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v1_tdlat_3(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_766])).

cnf(c_9438,plain,
    ( v2_tex_2(X0,sK2(sK3,sK4)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top
    | v2_struct_0(sK2(sK3,sK4)) = iProver_top
    | v1_tdlat_3(sK2(sK3,sK4)) != iProver_top
    | l1_pre_topc(sK2(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9429,c_7135])).

cnf(c_34,negated_conjecture,
    ( ~ v2_tex_2(sK4,sK3)
    | ~ v1_zfmisc_1(sK4) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_49,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v1_zfmisc_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_25,plain,
    ( m1_pre_topc(sK2(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_7542,plain,
    ( m1_pre_topc(sK2(X0,sK4),X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_7543,plain,
    ( m1_pre_topc(sK2(X0,sK4),X0) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7542])).

cnf(c_7545,plain,
    ( m1_pre_topc(sK2(sK3,sK4),sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7543])).

cnf(c_7148,plain,
    ( m1_pre_topc(sK2(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_9392,plain,
    ( m1_pre_topc(sK2(sK3,sK4),sK3) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_7141,c_7148])).

cnf(c_9617,plain,
    ( m1_pre_topc(sK2(sK3,sK4),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9392,c_42,c_45,c_46,c_47,c_7545])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_tdlat_3(X1)
    | ~ v1_tdlat_3(X0)
    | ~ v2_pre_topc(X1)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_13,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_15,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_517,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_13,c_15])).

cnf(c_535,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v1_tdlat_3(X0)
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_19,c_517])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_539,plain,
    ( v1_zfmisc_1(u1_struct_0(X0))
    | ~ v2_pre_topc(X1)
    | ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_535,c_14])).

cnf(c_540,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v1_tdlat_3(X0)
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_539])).

cnf(c_18,plain,
    ( ~ v2_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_559,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v1_tdlat_3(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_540,c_18])).

cnf(c_39,negated_conjecture,
    ( v2_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_580,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_559,c_39])).

cnf(c_581,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ v1_tdlat_3(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_580])).

cnf(c_585,plain,
    ( v1_zfmisc_1(u1_struct_0(X0))
    | ~ v1_tdlat_3(X0)
    | ~ m1_pre_topc(X0,sK3)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_581,c_41,c_38])).

cnf(c_586,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | v2_struct_0(X0)
    | ~ v1_tdlat_3(X0)
    | v1_zfmisc_1(u1_struct_0(X0)) ),
    inference(renaming,[status(thm)],[c_585])).

cnf(c_7137,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_586])).

cnf(c_9623,plain,
    ( v2_struct_0(sK2(sK3,sK4)) = iProver_top
    | v1_tdlat_3(sK2(sK3,sK4)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_9617,c_7137])).

cnf(c_9627,plain,
    ( v2_struct_0(sK2(sK3,sK4)) = iProver_top
    | v1_tdlat_3(sK2(sK3,sK4)) != iProver_top
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9623,c_9429])).

cnf(c_9697,plain,
    ( v1_tdlat_3(sK2(sK3,sK4)) != iProver_top
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9627,c_42,c_45,c_46,c_47,c_7527])).

cnf(c_27,plain,
    ( v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_tdlat_3(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_7146,plain,
    ( v2_tex_2(u1_struct_0(X0),X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_10077,plain,
    ( v2_tex_2(u1_struct_0(sK2(sK3,sK4)),X0) = iProver_top
    | m1_pre_topc(sK2(sK3,sK4),X0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2(sK3,sK4)) = iProver_top
    | v1_tdlat_3(sK2(sK3,sK4)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9429,c_7146])).

cnf(c_10100,plain,
    ( v2_tex_2(sK4,X0) = iProver_top
    | m1_pre_topc(sK2(sK3,sK4),X0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2(sK3,sK4)) = iProver_top
    | v1_tdlat_3(sK2(sK3,sK4)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10077,c_9429])).

cnf(c_10144,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top
    | m1_pre_topc(sK2(sK3,sK4),sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK2(sK3,sK4)) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_tdlat_3(sK2(sK3,sK4)) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_10100])).

cnf(c_10614,plain,
    ( v1_tdlat_3(sK2(sK3,sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9438,c_42,c_45,c_46,c_47,c_49,c_7527,c_7545,c_9697,c_10144])).

cnf(c_10756,plain,
    ( v2_tex_2(sK4,X0) != iProver_top
    | m1_pre_topc(sK2(sK3,sK4),X0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9948,c_42,c_45,c_46,c_47,c_49,c_7527,c_7545,c_9697,c_10144])).

cnf(c_10769,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | m1_pre_topc(sK2(sK3,sK4),sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7141,c_10756])).

cnf(c_9994,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | m1_pre_topc(sK2(sK3,sK4),sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK2(sK3,sK4)) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_tdlat_3(sK2(sK3,sK4)) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9948])).

cnf(c_10985,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10769,c_42,c_45,c_46,c_47,c_49,c_7527,c_7545,c_9697,c_9994,c_10144])).

cnf(c_10991,plain,
    ( v1_zfmisc_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_7142,c_10985])).

cnf(c_8741,plain,
    ( k6_domain_1(X0,sK1(X0)) = k1_tarski(sK1(X0))
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7150,c_7153])).

cnf(c_11129,plain,
    ( k6_domain_1(sK4,sK1(sK4)) = k1_tarski(sK1(sK4))
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_10991,c_8741])).

cnf(c_22,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | k6_domain_1(X0,sK1(X0)) = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_7151,plain,
    ( k6_domain_1(X0,sK1(X0)) = X0
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_11081,plain,
    ( k6_domain_1(sK4,sK1(sK4)) = sK4
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_10991,c_7151])).

cnf(c_306,plain,
    ( v1_zfmisc_1(sK4)
    | v2_tex_2(sK4,sK3) ),
    inference(prop_impl,[status(thm)],[c_35])).

cnf(c_307,plain,
    ( v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(sK4) ),
    inference(renaming,[status(thm)],[c_306])).

cnf(c_982,plain,
    ( v2_tex_2(sK4,sK3)
    | v1_xboole_0(X0)
    | k6_domain_1(X0,sK1(X0)) = X0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_307])).

cnf(c_983,plain,
    ( v2_tex_2(sK4,sK3)
    | v1_xboole_0(sK4)
    | k6_domain_1(sK4,sK1(sK4)) = sK4 ),
    inference(unflattening,[status(thm)],[c_982])).

cnf(c_984,plain,
    ( k6_domain_1(sK4,sK1(sK4)) = sK4
    | v2_tex_2(sK4,sK3) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_983])).

cnf(c_11084,plain,
    ( k6_domain_1(sK4,sK1(sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11081,c_42,c_45,c_46,c_47,c_49,c_984,c_7527,c_7545,c_9697,c_9994,c_10144])).

cnf(c_11130,plain,
    ( k1_tarski(sK1(sK4)) = sK4
    | v1_xboole_0(sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11129,c_11084])).

cnf(c_11343,plain,
    ( k1_tarski(sK1(sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11130,c_46])).

cnf(c_30806,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK1(sK4)) = sK4
    | v1_zfmisc_1(sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_30596,c_11343])).

cnf(c_30,plain,
    ( ~ v2_tex_2(u1_struct_0(X0),X0)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | v1_tdlat_3(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_31,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_40,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_825,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_40])).

cnf(c_826,plain,
    ( v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_825])).

cnf(c_830,plain,
    ( v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_826,c_41,c_38])).

cnf(c_1629,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | u1_struct_0(X1) != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_830])).

cnf(c_1630,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | v1_tdlat_3(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_1629])).

cnf(c_1632,plain,
    ( v1_tdlat_3(sK3)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1630,c_41,c_38])).

cnf(c_1633,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_tdlat_3(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_1632])).

cnf(c_1634,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_tdlat_3(sK3) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1633])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_7484,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X0,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_7805,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_7484])).

cnf(c_7807,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7805])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_7806,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_7809,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7806])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_7165,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8679,plain,
    ( m1_subset_1(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7165,c_7158])).

cnf(c_806,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_40])).

cnf(c_807,plain,
    ( v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v1_tdlat_3(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_806])).

cnf(c_809,plain,
    ( ~ v1_tdlat_3(sK3)
    | v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_807,c_41,c_38])).

cnf(c_810,plain,
    ( v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_tdlat_3(sK3) ),
    inference(renaming,[status(thm)],[c_809])).

cnf(c_7133,plain,
    ( v2_tex_2(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_tdlat_3(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_810])).

cnf(c_10249,plain,
    ( v2_tex_2(sK0(k1_zfmisc_1(u1_struct_0(sK3)),X0),sK3) = iProver_top
    | r1_tarski(k1_zfmisc_1(u1_struct_0(sK3)),X0) = iProver_top
    | v1_tdlat_3(sK3) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8679,c_7133])).

cnf(c_3113,plain,
    ( v2_tex_2(X0,sK3)
    | ~ v1_tdlat_3(sK3)
    | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_810])).

cnf(c_3114,plain,
    ( v2_tex_2(sK4,sK3)
    | ~ v1_tdlat_3(sK3) ),
    inference(unflattening,[status(thm)],[c_3113])).

cnf(c_3115,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top
    | v1_tdlat_3(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3114])).

cnf(c_10506,plain,
    ( v1_tdlat_3(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10249,c_42,c_45,c_46,c_47,c_49,c_3115,c_7527,c_7545,c_9697,c_9994,c_10144])).

cnf(c_7162,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_14176,plain,
    ( r2_hidden(sK1(X0),X1) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_10150,c_7164])).

cnf(c_29230,plain,
    ( r2_hidden(sK1(sK4),X0) = iProver_top
    | r1_tarski(u1_struct_0(sK3),X0) != iProver_top
    | v1_zfmisc_1(sK4) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_7575,c_14176])).

cnf(c_48,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_29495,plain,
    ( r2_hidden(sK1(sK4),X0) = iProver_top
    | r1_tarski(u1_struct_0(sK3),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_29230,c_42,c_45,c_46,c_47,c_48,c_49,c_7527,c_7545,c_9697,c_9994,c_10144])).

cnf(c_29506,plain,
    ( r2_hidden(sK1(sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7162,c_29495])).

cnf(c_30377,plain,
    ( m1_subset_1(sK1(sK4),u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_29506,c_7158])).

cnf(c_968,plain,
    ( v2_tex_2(sK4,sK3)
    | m1_subset_1(sK1(X0),X0)
    | v1_xboole_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_307])).

cnf(c_969,plain,
    ( v2_tex_2(sK4,sK3)
    | m1_subset_1(sK1(sK4),sK4)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_968])).

cnf(c_970,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top
    | m1_subset_1(sK1(sK4),sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_969])).

cnf(c_7506,plain,
    ( ~ m1_subset_1(X0,sK4)
    | r2_hidden(X0,sK4)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_7873,plain,
    ( ~ m1_subset_1(sK1(sK4),sK4)
    | r2_hidden(sK1(sK4),sK4)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_7506])).

cnf(c_7874,plain,
    ( m1_subset_1(sK1(sK4),sK4) != iProver_top
    | r2_hidden(sK1(sK4),sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7873])).

cnf(c_8122,plain,
    ( r2_hidden(sK1(sK4),X0)
    | ~ r2_hidden(sK1(sK4),sK4)
    | ~ r1_tarski(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_10443,plain,
    ( r2_hidden(sK1(sK4),u1_struct_0(sK3))
    | ~ r2_hidden(sK1(sK4),sK4)
    | ~ r1_tarski(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_8122])).

cnf(c_10445,plain,
    ( r2_hidden(sK1(sK4),u1_struct_0(sK3)) = iProver_top
    | r2_hidden(sK1(sK4),sK4) != iProver_top
    | r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10443])).

cnf(c_7709,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3))
    | ~ r2_hidden(X0,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_10444,plain,
    ( m1_subset_1(sK1(sK4),u1_struct_0(sK3))
    | ~ r2_hidden(sK1(sK4),u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_7709])).

cnf(c_10447,plain,
    ( m1_subset_1(sK1(sK4),u1_struct_0(sK3)) = iProver_top
    | r2_hidden(sK1(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10444])).

cnf(c_30572,plain,
    ( m1_subset_1(sK1(sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_30377,c_42,c_45,c_46,c_47,c_49,c_970,c_1634,c_3115,c_7527,c_7545,c_7575,c_7807,c_7809,c_7874,c_9697,c_9994,c_10144,c_10445,c_10447])).

cnf(c_30577,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK1(sK4)) = k1_tarski(sK1(sK4))
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_30572,c_7153])).

cnf(c_30582,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK1(sK4)) = sK4
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_30577,c_11343])).

cnf(c_33410,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK1(sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_30806,c_42,c_45,c_46,c_47,c_49,c_1634,c_3115,c_7527,c_7545,c_7807,c_7809,c_9697,c_9994,c_10144,c_30582])).

cnf(c_32,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_788,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_40])).

cnf(c_789,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_788])).

cnf(c_793,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_789,c_41,c_38])).

cnf(c_7134,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_793])).

cnf(c_33415,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top
    | m1_subset_1(sK1(sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_33410,c_7134])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_33415,c_10614,c_10506,c_10447,c_10445,c_9994,c_7874,c_7809,c_7807,c_7575,c_7545,c_7527,c_1634,c_970,c_47,c_46,c_45,c_42])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:32:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.54/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.54/1.50  
% 7.54/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.54/1.50  
% 7.54/1.50  ------  iProver source info
% 7.54/1.50  
% 7.54/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.54/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.54/1.50  git: non_committed_changes: false
% 7.54/1.50  git: last_make_outside_of_git: false
% 7.54/1.50  
% 7.54/1.50  ------ 
% 7.54/1.50  
% 7.54/1.50  ------ Input Options
% 7.54/1.50  
% 7.54/1.50  --out_options                           all
% 7.54/1.50  --tptp_safe_out                         true
% 7.54/1.50  --problem_path                          ""
% 7.54/1.50  --include_path                          ""
% 7.54/1.50  --clausifier                            res/vclausify_rel
% 7.54/1.50  --clausifier_options                    --mode clausify
% 7.54/1.50  --stdin                                 false
% 7.54/1.50  --stats_out                             all
% 7.54/1.50  
% 7.54/1.50  ------ General Options
% 7.54/1.50  
% 7.54/1.50  --fof                                   false
% 7.54/1.50  --time_out_real                         305.
% 7.54/1.50  --time_out_virtual                      -1.
% 7.54/1.50  --symbol_type_check                     false
% 7.54/1.50  --clausify_out                          false
% 7.54/1.50  --sig_cnt_out                           false
% 7.54/1.50  --trig_cnt_out                          false
% 7.54/1.50  --trig_cnt_out_tolerance                1.
% 7.54/1.50  --trig_cnt_out_sk_spl                   false
% 7.54/1.50  --abstr_cl_out                          false
% 7.54/1.50  
% 7.54/1.50  ------ Global Options
% 7.54/1.50  
% 7.54/1.50  --schedule                              default
% 7.54/1.50  --add_important_lit                     false
% 7.54/1.50  --prop_solver_per_cl                    1000
% 7.54/1.50  --min_unsat_core                        false
% 7.54/1.50  --soft_assumptions                      false
% 7.54/1.50  --soft_lemma_size                       3
% 7.54/1.50  --prop_impl_unit_size                   0
% 7.54/1.50  --prop_impl_unit                        []
% 7.54/1.50  --share_sel_clauses                     true
% 7.54/1.50  --reset_solvers                         false
% 7.54/1.50  --bc_imp_inh                            [conj_cone]
% 7.54/1.50  --conj_cone_tolerance                   3.
% 7.54/1.50  --extra_neg_conj                        none
% 7.54/1.50  --large_theory_mode                     true
% 7.54/1.50  --prolific_symb_bound                   200
% 7.54/1.50  --lt_threshold                          2000
% 7.54/1.50  --clause_weak_htbl                      true
% 7.54/1.50  --gc_record_bc_elim                     false
% 7.54/1.50  
% 7.54/1.50  ------ Preprocessing Options
% 7.54/1.50  
% 7.54/1.50  --preprocessing_flag                    true
% 7.54/1.50  --time_out_prep_mult                    0.1
% 7.54/1.50  --splitting_mode                        input
% 7.54/1.50  --splitting_grd                         true
% 7.54/1.50  --splitting_cvd                         false
% 7.54/1.50  --splitting_cvd_svl                     false
% 7.54/1.50  --splitting_nvd                         32
% 7.54/1.50  --sub_typing                            true
% 7.54/1.50  --prep_gs_sim                           true
% 7.54/1.50  --prep_unflatten                        true
% 7.54/1.50  --prep_res_sim                          true
% 7.54/1.50  --prep_upred                            true
% 7.54/1.50  --prep_sem_filter                       exhaustive
% 7.54/1.50  --prep_sem_filter_out                   false
% 7.54/1.50  --pred_elim                             true
% 7.54/1.50  --res_sim_input                         true
% 7.54/1.50  --eq_ax_congr_red                       true
% 7.54/1.50  --pure_diseq_elim                       true
% 7.54/1.50  --brand_transform                       false
% 7.54/1.50  --non_eq_to_eq                          false
% 7.54/1.50  --prep_def_merge                        true
% 7.54/1.50  --prep_def_merge_prop_impl              false
% 7.54/1.50  --prep_def_merge_mbd                    true
% 7.54/1.50  --prep_def_merge_tr_red                 false
% 7.54/1.50  --prep_def_merge_tr_cl                  false
% 7.54/1.50  --smt_preprocessing                     true
% 7.54/1.50  --smt_ac_axioms                         fast
% 7.54/1.50  --preprocessed_out                      false
% 7.54/1.50  --preprocessed_stats                    false
% 7.54/1.50  
% 7.54/1.50  ------ Abstraction refinement Options
% 7.54/1.50  
% 7.54/1.50  --abstr_ref                             []
% 7.54/1.50  --abstr_ref_prep                        false
% 7.54/1.50  --abstr_ref_until_sat                   false
% 7.54/1.50  --abstr_ref_sig_restrict                funpre
% 7.54/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.54/1.50  --abstr_ref_under                       []
% 7.54/1.50  
% 7.54/1.50  ------ SAT Options
% 7.54/1.50  
% 7.54/1.50  --sat_mode                              false
% 7.54/1.50  --sat_fm_restart_options                ""
% 7.54/1.50  --sat_gr_def                            false
% 7.54/1.50  --sat_epr_types                         true
% 7.54/1.50  --sat_non_cyclic_types                  false
% 7.54/1.50  --sat_finite_models                     false
% 7.54/1.50  --sat_fm_lemmas                         false
% 7.54/1.50  --sat_fm_prep                           false
% 7.54/1.50  --sat_fm_uc_incr                        true
% 7.54/1.50  --sat_out_model                         small
% 7.54/1.50  --sat_out_clauses                       false
% 7.54/1.50  
% 7.54/1.50  ------ QBF Options
% 7.54/1.50  
% 7.54/1.50  --qbf_mode                              false
% 7.54/1.50  --qbf_elim_univ                         false
% 7.54/1.50  --qbf_dom_inst                          none
% 7.54/1.50  --qbf_dom_pre_inst                      false
% 7.54/1.50  --qbf_sk_in                             false
% 7.54/1.50  --qbf_pred_elim                         true
% 7.54/1.50  --qbf_split                             512
% 7.54/1.50  
% 7.54/1.50  ------ BMC1 Options
% 7.54/1.50  
% 7.54/1.50  --bmc1_incremental                      false
% 7.54/1.50  --bmc1_axioms                           reachable_all
% 7.54/1.50  --bmc1_min_bound                        0
% 7.54/1.50  --bmc1_max_bound                        -1
% 7.54/1.50  --bmc1_max_bound_default                -1
% 7.54/1.50  --bmc1_symbol_reachability              true
% 7.54/1.50  --bmc1_property_lemmas                  false
% 7.54/1.50  --bmc1_k_induction                      false
% 7.54/1.50  --bmc1_non_equiv_states                 false
% 7.54/1.50  --bmc1_deadlock                         false
% 7.54/1.50  --bmc1_ucm                              false
% 7.54/1.50  --bmc1_add_unsat_core                   none
% 7.54/1.50  --bmc1_unsat_core_children              false
% 7.54/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.54/1.50  --bmc1_out_stat                         full
% 7.54/1.50  --bmc1_ground_init                      false
% 7.54/1.50  --bmc1_pre_inst_next_state              false
% 7.54/1.50  --bmc1_pre_inst_state                   false
% 7.54/1.50  --bmc1_pre_inst_reach_state             false
% 7.54/1.50  --bmc1_out_unsat_core                   false
% 7.54/1.50  --bmc1_aig_witness_out                  false
% 7.54/1.50  --bmc1_verbose                          false
% 7.54/1.50  --bmc1_dump_clauses_tptp                false
% 7.54/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.54/1.50  --bmc1_dump_file                        -
% 7.54/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.54/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.54/1.50  --bmc1_ucm_extend_mode                  1
% 7.54/1.50  --bmc1_ucm_init_mode                    2
% 7.54/1.50  --bmc1_ucm_cone_mode                    none
% 7.54/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.54/1.50  --bmc1_ucm_relax_model                  4
% 7.54/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.54/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.54/1.50  --bmc1_ucm_layered_model                none
% 7.54/1.50  --bmc1_ucm_max_lemma_size               10
% 7.54/1.50  
% 7.54/1.50  ------ AIG Options
% 7.54/1.50  
% 7.54/1.50  --aig_mode                              false
% 7.54/1.50  
% 7.54/1.50  ------ Instantiation Options
% 7.54/1.50  
% 7.54/1.50  --instantiation_flag                    true
% 7.54/1.50  --inst_sos_flag                         false
% 7.54/1.50  --inst_sos_phase                        true
% 7.54/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.54/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.54/1.50  --inst_lit_sel_side                     num_symb
% 7.54/1.50  --inst_solver_per_active                1400
% 7.54/1.50  --inst_solver_calls_frac                1.
% 7.54/1.50  --inst_passive_queue_type               priority_queues
% 7.54/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.54/1.50  --inst_passive_queues_freq              [25;2]
% 7.54/1.50  --inst_dismatching                      true
% 7.54/1.50  --inst_eager_unprocessed_to_passive     true
% 7.54/1.50  --inst_prop_sim_given                   true
% 7.54/1.50  --inst_prop_sim_new                     false
% 7.54/1.50  --inst_subs_new                         false
% 7.54/1.50  --inst_eq_res_simp                      false
% 7.54/1.50  --inst_subs_given                       false
% 7.54/1.50  --inst_orphan_elimination               true
% 7.54/1.50  --inst_learning_loop_flag               true
% 7.54/1.50  --inst_learning_start                   3000
% 7.54/1.50  --inst_learning_factor                  2
% 7.54/1.50  --inst_start_prop_sim_after_learn       3
% 7.54/1.50  --inst_sel_renew                        solver
% 7.54/1.50  --inst_lit_activity_flag                true
% 7.54/1.50  --inst_restr_to_given                   false
% 7.54/1.50  --inst_activity_threshold               500
% 7.54/1.50  --inst_out_proof                        true
% 7.54/1.50  
% 7.54/1.50  ------ Resolution Options
% 7.54/1.50  
% 7.54/1.50  --resolution_flag                       true
% 7.54/1.50  --res_lit_sel                           adaptive
% 7.54/1.50  --res_lit_sel_side                      none
% 7.54/1.50  --res_ordering                          kbo
% 7.54/1.50  --res_to_prop_solver                    active
% 7.54/1.50  --res_prop_simpl_new                    false
% 7.54/1.50  --res_prop_simpl_given                  true
% 7.54/1.50  --res_passive_queue_type                priority_queues
% 7.54/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.54/1.50  --res_passive_queues_freq               [15;5]
% 7.54/1.50  --res_forward_subs                      full
% 7.54/1.50  --res_backward_subs                     full
% 7.54/1.50  --res_forward_subs_resolution           true
% 7.54/1.50  --res_backward_subs_resolution          true
% 7.54/1.50  --res_orphan_elimination                true
% 7.54/1.50  --res_time_limit                        2.
% 7.54/1.50  --res_out_proof                         true
% 7.54/1.50  
% 7.54/1.50  ------ Superposition Options
% 7.54/1.50  
% 7.54/1.50  --superposition_flag                    true
% 7.54/1.50  --sup_passive_queue_type                priority_queues
% 7.54/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.54/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.54/1.50  --demod_completeness_check              fast
% 7.54/1.50  --demod_use_ground                      true
% 7.54/1.50  --sup_to_prop_solver                    passive
% 7.54/1.50  --sup_prop_simpl_new                    true
% 7.54/1.50  --sup_prop_simpl_given                  true
% 7.54/1.50  --sup_fun_splitting                     false
% 7.54/1.50  --sup_smt_interval                      50000
% 7.54/1.50  
% 7.54/1.50  ------ Superposition Simplification Setup
% 7.54/1.50  
% 7.54/1.50  --sup_indices_passive                   []
% 7.54/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.54/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.54/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.54/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.54/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.54/1.50  --sup_full_bw                           [BwDemod]
% 7.54/1.50  --sup_immed_triv                        [TrivRules]
% 7.54/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.54/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.54/1.50  --sup_immed_bw_main                     []
% 7.54/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.54/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.54/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.54/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.54/1.50  
% 7.54/1.50  ------ Combination Options
% 7.54/1.50  
% 7.54/1.50  --comb_res_mult                         3
% 7.54/1.50  --comb_sup_mult                         2
% 7.54/1.50  --comb_inst_mult                        10
% 7.54/1.50  
% 7.54/1.50  ------ Debug Options
% 7.54/1.50  
% 7.54/1.50  --dbg_backtrace                         false
% 7.54/1.50  --dbg_dump_prop_clauses                 false
% 7.54/1.50  --dbg_dump_prop_clauses_file            -
% 7.54/1.50  --dbg_out_stat                          false
% 7.54/1.50  ------ Parsing...
% 7.54/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.54/1.50  
% 7.54/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.54/1.50  
% 7.54/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.54/1.50  
% 7.54/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.54/1.50  ------ Proving...
% 7.54/1.50  ------ Problem Properties 
% 7.54/1.50  
% 7.54/1.50  
% 7.54/1.50  clauses                                 35
% 7.54/1.50  conjectures                             6
% 7.54/1.50  EPR                                     14
% 7.54/1.50  Horn                                    18
% 7.54/1.50  unary                                   5
% 7.54/1.50  binary                                  7
% 7.54/1.50  lits                                    110
% 7.54/1.50  lits eq                                 5
% 7.54/1.50  fd_pure                                 0
% 7.54/1.50  fd_pseudo                               0
% 7.54/1.50  fd_cond                                 0
% 7.54/1.50  fd_pseudo_cond                          1
% 7.54/1.50  AC symbols                              0
% 7.54/1.50  
% 7.54/1.50  ------ Schedule dynamic 5 is on 
% 7.54/1.50  
% 7.54/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.54/1.50  
% 7.54/1.50  
% 7.54/1.50  ------ 
% 7.54/1.50  Current options:
% 7.54/1.50  ------ 
% 7.54/1.50  
% 7.54/1.50  ------ Input Options
% 7.54/1.50  
% 7.54/1.50  --out_options                           all
% 7.54/1.50  --tptp_safe_out                         true
% 7.54/1.50  --problem_path                          ""
% 7.54/1.50  --include_path                          ""
% 7.54/1.50  --clausifier                            res/vclausify_rel
% 7.54/1.50  --clausifier_options                    --mode clausify
% 7.54/1.50  --stdin                                 false
% 7.54/1.50  --stats_out                             all
% 7.54/1.50  
% 7.54/1.50  ------ General Options
% 7.54/1.50  
% 7.54/1.50  --fof                                   false
% 7.54/1.50  --time_out_real                         305.
% 7.54/1.50  --time_out_virtual                      -1.
% 7.54/1.50  --symbol_type_check                     false
% 7.54/1.50  --clausify_out                          false
% 7.54/1.50  --sig_cnt_out                           false
% 7.54/1.50  --trig_cnt_out                          false
% 7.54/1.50  --trig_cnt_out_tolerance                1.
% 7.54/1.50  --trig_cnt_out_sk_spl                   false
% 7.54/1.50  --abstr_cl_out                          false
% 7.54/1.50  
% 7.54/1.50  ------ Global Options
% 7.54/1.50  
% 7.54/1.50  --schedule                              default
% 7.54/1.50  --add_important_lit                     false
% 7.54/1.50  --prop_solver_per_cl                    1000
% 7.54/1.50  --min_unsat_core                        false
% 7.54/1.50  --soft_assumptions                      false
% 7.54/1.50  --soft_lemma_size                       3
% 7.54/1.50  --prop_impl_unit_size                   0
% 7.54/1.50  --prop_impl_unit                        []
% 7.54/1.50  --share_sel_clauses                     true
% 7.54/1.50  --reset_solvers                         false
% 7.54/1.50  --bc_imp_inh                            [conj_cone]
% 7.54/1.50  --conj_cone_tolerance                   3.
% 7.54/1.50  --extra_neg_conj                        none
% 7.54/1.50  --large_theory_mode                     true
% 7.54/1.50  --prolific_symb_bound                   200
% 7.54/1.50  --lt_threshold                          2000
% 7.54/1.50  --clause_weak_htbl                      true
% 7.54/1.50  --gc_record_bc_elim                     false
% 7.54/1.50  
% 7.54/1.50  ------ Preprocessing Options
% 7.54/1.50  
% 7.54/1.50  --preprocessing_flag                    true
% 7.54/1.50  --time_out_prep_mult                    0.1
% 7.54/1.50  --splitting_mode                        input
% 7.54/1.50  --splitting_grd                         true
% 7.54/1.50  --splitting_cvd                         false
% 7.54/1.50  --splitting_cvd_svl                     false
% 7.54/1.50  --splitting_nvd                         32
% 7.54/1.50  --sub_typing                            true
% 7.54/1.50  --prep_gs_sim                           true
% 7.54/1.50  --prep_unflatten                        true
% 7.54/1.50  --prep_res_sim                          true
% 7.54/1.50  --prep_upred                            true
% 7.54/1.50  --prep_sem_filter                       exhaustive
% 7.54/1.50  --prep_sem_filter_out                   false
% 7.54/1.50  --pred_elim                             true
% 7.54/1.50  --res_sim_input                         true
% 7.54/1.50  --eq_ax_congr_red                       true
% 7.54/1.50  --pure_diseq_elim                       true
% 7.54/1.50  --brand_transform                       false
% 7.54/1.50  --non_eq_to_eq                          false
% 7.54/1.50  --prep_def_merge                        true
% 7.54/1.50  --prep_def_merge_prop_impl              false
% 7.54/1.50  --prep_def_merge_mbd                    true
% 7.54/1.50  --prep_def_merge_tr_red                 false
% 7.54/1.50  --prep_def_merge_tr_cl                  false
% 7.54/1.50  --smt_preprocessing                     true
% 7.54/1.50  --smt_ac_axioms                         fast
% 7.54/1.50  --preprocessed_out                      false
% 7.54/1.50  --preprocessed_stats                    false
% 7.54/1.50  
% 7.54/1.50  ------ Abstraction refinement Options
% 7.54/1.50  
% 7.54/1.50  --abstr_ref                             []
% 7.54/1.50  --abstr_ref_prep                        false
% 7.54/1.50  --abstr_ref_until_sat                   false
% 7.54/1.50  --abstr_ref_sig_restrict                funpre
% 7.54/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.54/1.50  --abstr_ref_under                       []
% 7.54/1.50  
% 7.54/1.50  ------ SAT Options
% 7.54/1.50  
% 7.54/1.50  --sat_mode                              false
% 7.54/1.50  --sat_fm_restart_options                ""
% 7.54/1.50  --sat_gr_def                            false
% 7.54/1.50  --sat_epr_types                         true
% 7.54/1.50  --sat_non_cyclic_types                  false
% 7.54/1.50  --sat_finite_models                     false
% 7.54/1.50  --sat_fm_lemmas                         false
% 7.54/1.50  --sat_fm_prep                           false
% 7.54/1.50  --sat_fm_uc_incr                        true
% 7.54/1.50  --sat_out_model                         small
% 7.54/1.50  --sat_out_clauses                       false
% 7.54/1.50  
% 7.54/1.50  ------ QBF Options
% 7.54/1.50  
% 7.54/1.50  --qbf_mode                              false
% 7.54/1.50  --qbf_elim_univ                         false
% 7.54/1.50  --qbf_dom_inst                          none
% 7.54/1.50  --qbf_dom_pre_inst                      false
% 7.54/1.50  --qbf_sk_in                             false
% 7.54/1.50  --qbf_pred_elim                         true
% 7.54/1.50  --qbf_split                             512
% 7.54/1.50  
% 7.54/1.50  ------ BMC1 Options
% 7.54/1.50  
% 7.54/1.50  --bmc1_incremental                      false
% 7.54/1.50  --bmc1_axioms                           reachable_all
% 7.54/1.50  --bmc1_min_bound                        0
% 7.54/1.50  --bmc1_max_bound                        -1
% 7.54/1.50  --bmc1_max_bound_default                -1
% 7.54/1.50  --bmc1_symbol_reachability              true
% 7.54/1.50  --bmc1_property_lemmas                  false
% 7.54/1.50  --bmc1_k_induction                      false
% 7.54/1.50  --bmc1_non_equiv_states                 false
% 7.54/1.50  --bmc1_deadlock                         false
% 7.54/1.50  --bmc1_ucm                              false
% 7.54/1.50  --bmc1_add_unsat_core                   none
% 7.54/1.50  --bmc1_unsat_core_children              false
% 7.54/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.54/1.50  --bmc1_out_stat                         full
% 7.54/1.50  --bmc1_ground_init                      false
% 7.54/1.50  --bmc1_pre_inst_next_state              false
% 7.54/1.50  --bmc1_pre_inst_state                   false
% 7.54/1.50  --bmc1_pre_inst_reach_state             false
% 7.54/1.50  --bmc1_out_unsat_core                   false
% 7.54/1.50  --bmc1_aig_witness_out                  false
% 7.54/1.50  --bmc1_verbose                          false
% 7.54/1.50  --bmc1_dump_clauses_tptp                false
% 7.54/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.54/1.50  --bmc1_dump_file                        -
% 7.54/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.54/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.54/1.50  --bmc1_ucm_extend_mode                  1
% 7.54/1.50  --bmc1_ucm_init_mode                    2
% 7.54/1.50  --bmc1_ucm_cone_mode                    none
% 7.54/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.54/1.50  --bmc1_ucm_relax_model                  4
% 7.54/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.54/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.54/1.50  --bmc1_ucm_layered_model                none
% 7.54/1.50  --bmc1_ucm_max_lemma_size               10
% 7.54/1.50  
% 7.54/1.50  ------ AIG Options
% 7.54/1.50  
% 7.54/1.50  --aig_mode                              false
% 7.54/1.50  
% 7.54/1.50  ------ Instantiation Options
% 7.54/1.50  
% 7.54/1.50  --instantiation_flag                    true
% 7.54/1.50  --inst_sos_flag                         false
% 7.54/1.50  --inst_sos_phase                        true
% 7.54/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.54/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.54/1.50  --inst_lit_sel_side                     none
% 7.54/1.50  --inst_solver_per_active                1400
% 7.54/1.50  --inst_solver_calls_frac                1.
% 7.54/1.50  --inst_passive_queue_type               priority_queues
% 7.54/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.54/1.50  --inst_passive_queues_freq              [25;2]
% 7.54/1.50  --inst_dismatching                      true
% 7.54/1.50  --inst_eager_unprocessed_to_passive     true
% 7.54/1.50  --inst_prop_sim_given                   true
% 7.54/1.50  --inst_prop_sim_new                     false
% 7.54/1.50  --inst_subs_new                         false
% 7.54/1.50  --inst_eq_res_simp                      false
% 7.54/1.50  --inst_subs_given                       false
% 7.54/1.50  --inst_orphan_elimination               true
% 7.54/1.50  --inst_learning_loop_flag               true
% 7.54/1.50  --inst_learning_start                   3000
% 7.54/1.50  --inst_learning_factor                  2
% 7.54/1.50  --inst_start_prop_sim_after_learn       3
% 7.54/1.50  --inst_sel_renew                        solver
% 7.54/1.50  --inst_lit_activity_flag                true
% 7.54/1.50  --inst_restr_to_given                   false
% 7.54/1.50  --inst_activity_threshold               500
% 7.54/1.50  --inst_out_proof                        true
% 7.54/1.50  
% 7.54/1.50  ------ Resolution Options
% 7.54/1.50  
% 7.54/1.50  --resolution_flag                       false
% 7.54/1.50  --res_lit_sel                           adaptive
% 7.54/1.50  --res_lit_sel_side                      none
% 7.54/1.50  --res_ordering                          kbo
% 7.54/1.50  --res_to_prop_solver                    active
% 7.54/1.50  --res_prop_simpl_new                    false
% 7.54/1.50  --res_prop_simpl_given                  true
% 7.54/1.50  --res_passive_queue_type                priority_queues
% 7.54/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.54/1.50  --res_passive_queues_freq               [15;5]
% 7.54/1.50  --res_forward_subs                      full
% 7.54/1.50  --res_backward_subs                     full
% 7.54/1.50  --res_forward_subs_resolution           true
% 7.54/1.50  --res_backward_subs_resolution          true
% 7.54/1.50  --res_orphan_elimination                true
% 7.54/1.50  --res_time_limit                        2.
% 7.54/1.50  --res_out_proof                         true
% 7.54/1.50  
% 7.54/1.50  ------ Superposition Options
% 7.54/1.50  
% 7.54/1.50  --superposition_flag                    true
% 7.54/1.50  --sup_passive_queue_type                priority_queues
% 7.54/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.54/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.54/1.50  --demod_completeness_check              fast
% 7.54/1.50  --demod_use_ground                      true
% 7.54/1.50  --sup_to_prop_solver                    passive
% 7.54/1.50  --sup_prop_simpl_new                    true
% 7.54/1.50  --sup_prop_simpl_given                  true
% 7.54/1.50  --sup_fun_splitting                     false
% 7.54/1.50  --sup_smt_interval                      50000
% 7.54/1.50  
% 7.54/1.50  ------ Superposition Simplification Setup
% 7.54/1.50  
% 7.54/1.50  --sup_indices_passive                   []
% 7.54/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.54/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.54/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.54/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.54/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.54/1.50  --sup_full_bw                           [BwDemod]
% 7.54/1.50  --sup_immed_triv                        [TrivRules]
% 7.54/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.54/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.54/1.50  --sup_immed_bw_main                     []
% 7.54/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.54/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.54/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.54/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.54/1.50  
% 7.54/1.50  ------ Combination Options
% 7.54/1.50  
% 7.54/1.50  --comb_res_mult                         3
% 7.54/1.50  --comb_sup_mult                         2
% 7.54/1.50  --comb_inst_mult                        10
% 7.54/1.50  
% 7.54/1.50  ------ Debug Options
% 7.54/1.50  
% 7.54/1.50  --dbg_backtrace                         false
% 7.54/1.50  --dbg_dump_prop_clauses                 false
% 7.54/1.50  --dbg_dump_prop_clauses_file            -
% 7.54/1.50  --dbg_out_stat                          false
% 7.54/1.50  
% 7.54/1.50  
% 7.54/1.50  
% 7.54/1.50  
% 7.54/1.50  ------ Proving...
% 7.54/1.50  
% 7.54/1.50  
% 7.54/1.50  % SZS status Theorem for theBenchmark.p
% 7.54/1.50  
% 7.54/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.54/1.50  
% 7.54/1.50  fof(f20,conjecture,(
% 7.54/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 7.54/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.54/1.50  
% 7.54/1.50  fof(f21,negated_conjecture,(
% 7.54/1.50    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 7.54/1.50    inference(negated_conjecture,[],[f20])).
% 7.54/1.50  
% 7.54/1.50  fof(f52,plain,(
% 7.54/1.50    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.54/1.50    inference(ennf_transformation,[],[f21])).
% 7.54/1.50  
% 7.54/1.50  fof(f53,plain,(
% 7.54/1.50    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.54/1.50    inference(flattening,[],[f52])).
% 7.54/1.50  
% 7.54/1.50  fof(f70,plain,(
% 7.54/1.50    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.54/1.50    inference(nnf_transformation,[],[f53])).
% 7.54/1.50  
% 7.54/1.50  fof(f71,plain,(
% 7.54/1.50    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.54/1.50    inference(flattening,[],[f70])).
% 7.54/1.50  
% 7.54/1.50  fof(f73,plain,(
% 7.54/1.50    ( ! [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,X0)) & (v1_zfmisc_1(sK4) | v2_tex_2(sK4,X0)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK4))) )),
% 7.54/1.50    introduced(choice_axiom,[])).
% 7.54/1.50  
% 7.54/1.50  fof(f72,plain,(
% 7.54/1.50    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK3)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 7.54/1.50    introduced(choice_axiom,[])).
% 7.54/1.50  
% 7.54/1.50  fof(f74,plain,(
% 7.54/1.50    ((~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3)) & (v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 7.54/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f71,f73,f72])).
% 7.54/1.50  
% 7.54/1.50  fof(f114,plain,(
% 7.54/1.50    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 7.54/1.50    inference(cnf_transformation,[],[f74])).
% 7.54/1.50  
% 7.54/1.50  fof(f5,axiom,(
% 7.54/1.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.54/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.54/1.50  
% 7.54/1.50  fof(f61,plain,(
% 7.54/1.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.54/1.50    inference(nnf_transformation,[],[f5])).
% 7.54/1.50  
% 7.54/1.50  fof(f86,plain,(
% 7.54/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.54/1.50    inference(cnf_transformation,[],[f61])).
% 7.54/1.50  
% 7.54/1.50  fof(f13,axiom,(
% 7.54/1.50    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 7.54/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.54/1.50  
% 7.54/1.50  fof(f39,plain,(
% 7.54/1.50    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 7.54/1.50    inference(ennf_transformation,[],[f13])).
% 7.54/1.50  
% 7.54/1.50  fof(f62,plain,(
% 7.54/1.50    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 7.54/1.50    inference(nnf_transformation,[],[f39])).
% 7.54/1.50  
% 7.54/1.50  fof(f63,plain,(
% 7.54/1.50    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 7.54/1.50    inference(rectify,[],[f62])).
% 7.54/1.50  
% 7.54/1.50  fof(f64,plain,(
% 7.54/1.50    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK1(X0)) = X0 & m1_subset_1(sK1(X0),X0)))),
% 7.54/1.50    introduced(choice_axiom,[])).
% 7.54/1.50  
% 7.54/1.50  fof(f65,plain,(
% 7.54/1.50    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK1(X0)) = X0 & m1_subset_1(sK1(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 7.54/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f63,f64])).
% 7.54/1.50  
% 7.54/1.50  fof(f96,plain,(
% 7.54/1.50    ( ! [X0] : (m1_subset_1(sK1(X0),X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 7.54/1.50    inference(cnf_transformation,[],[f65])).
% 7.54/1.50  
% 7.54/1.50  fof(f4,axiom,(
% 7.54/1.50    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 7.54/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.54/1.50  
% 7.54/1.50  fof(f26,plain,(
% 7.54/1.50    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 7.54/1.50    inference(ennf_transformation,[],[f4])).
% 7.54/1.50  
% 7.54/1.50  fof(f60,plain,(
% 7.54/1.50    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 7.54/1.50    inference(nnf_transformation,[],[f26])).
% 7.54/1.50  
% 7.54/1.50  fof(f82,plain,(
% 7.54/1.50    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 7.54/1.50    inference(cnf_transformation,[],[f60])).
% 7.54/1.50  
% 7.54/1.50  fof(f1,axiom,(
% 7.54/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.54/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.54/1.50  
% 7.54/1.50  fof(f23,plain,(
% 7.54/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.54/1.50    inference(ennf_transformation,[],[f1])).
% 7.54/1.50  
% 7.54/1.50  fof(f54,plain,(
% 7.54/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.54/1.50    inference(nnf_transformation,[],[f23])).
% 7.54/1.50  
% 7.54/1.50  fof(f55,plain,(
% 7.54/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.54/1.50    inference(rectify,[],[f54])).
% 7.54/1.50  
% 7.54/1.50  fof(f56,plain,(
% 7.54/1.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.54/1.50    introduced(choice_axiom,[])).
% 7.54/1.50  
% 7.54/1.50  fof(f57,plain,(
% 7.54/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.54/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f55,f56])).
% 7.54/1.50  
% 7.54/1.50  fof(f75,plain,(
% 7.54/1.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.54/1.50    inference(cnf_transformation,[],[f57])).
% 7.54/1.50  
% 7.54/1.50  fof(f83,plain,(
% 7.54/1.50    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 7.54/1.50    inference(cnf_transformation,[],[f60])).
% 7.54/1.50  
% 7.54/1.50  fof(f9,axiom,(
% 7.54/1.50    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 7.54/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.54/1.50  
% 7.54/1.50  fof(f31,plain,(
% 7.54/1.50    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 7.54/1.50    inference(ennf_transformation,[],[f9])).
% 7.54/1.50  
% 7.54/1.50  fof(f32,plain,(
% 7.54/1.50    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 7.54/1.50    inference(flattening,[],[f31])).
% 7.54/1.50  
% 7.54/1.50  fof(f91,plain,(
% 7.54/1.50    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 7.54/1.50    inference(cnf_transformation,[],[f32])).
% 7.54/1.50  
% 7.54/1.50  fof(f115,plain,(
% 7.54/1.50    v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3)),
% 7.54/1.50    inference(cnf_transformation,[],[f74])).
% 7.54/1.50  
% 7.54/1.50  fof(f14,axiom,(
% 7.54/1.50    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 7.54/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.54/1.50  
% 7.54/1.50  fof(f22,plain,(
% 7.54/1.50    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2))))),
% 7.54/1.50    inference(pure_predicate_removal,[],[f14])).
% 7.54/1.50  
% 7.54/1.50  fof(f40,plain,(
% 7.54/1.50    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 7.54/1.50    inference(ennf_transformation,[],[f22])).
% 7.54/1.50  
% 7.54/1.50  fof(f41,plain,(
% 7.54/1.50    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.54/1.50    inference(flattening,[],[f40])).
% 7.54/1.50  
% 7.54/1.50  fof(f66,plain,(
% 7.54/1.50    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & ~v2_struct_0(sK2(X0,X1))))),
% 7.54/1.50    introduced(choice_axiom,[])).
% 7.54/1.50  
% 7.54/1.50  fof(f67,plain,(
% 7.54/1.50    ! [X0] : (! [X1] : ((u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & ~v2_struct_0(sK2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.54/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f66])).
% 7.54/1.50  
% 7.54/1.50  fof(f101,plain,(
% 7.54/1.50    ( ! [X0,X1] : (u1_struct_0(sK2(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.54/1.50    inference(cnf_transformation,[],[f67])).
% 7.54/1.50  
% 7.54/1.50  fof(f109,plain,(
% 7.54/1.50    ~v2_struct_0(sK3)),
% 7.54/1.50    inference(cnf_transformation,[],[f74])).
% 7.54/1.50  
% 7.54/1.50  fof(f112,plain,(
% 7.54/1.50    l1_pre_topc(sK3)),
% 7.54/1.50    inference(cnf_transformation,[],[f74])).
% 7.54/1.50  
% 7.54/1.50  fof(f113,plain,(
% 7.54/1.50    ~v1_xboole_0(sK4)),
% 7.54/1.50    inference(cnf_transformation,[],[f74])).
% 7.54/1.50  
% 7.54/1.50  fof(f15,axiom,(
% 7.54/1.50    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 7.54/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.54/1.50  
% 7.54/1.50  fof(f42,plain,(
% 7.54/1.50    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 7.54/1.50    inference(ennf_transformation,[],[f15])).
% 7.54/1.50  
% 7.54/1.50  fof(f43,plain,(
% 7.54/1.50    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.54/1.50    inference(flattening,[],[f42])).
% 7.54/1.50  
% 7.54/1.50  fof(f68,plain,(
% 7.54/1.50    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.54/1.50    inference(nnf_transformation,[],[f43])).
% 7.54/1.50  
% 7.54/1.50  fof(f102,plain,(
% 7.54/1.50    ( ! [X2,X0,X1] : (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.54/1.50    inference(cnf_transformation,[],[f68])).
% 7.54/1.50  
% 7.54/1.50  fof(f120,plain,(
% 7.54/1.50    ( ! [X0,X1] : (v1_tdlat_3(X1) | ~v2_tex_2(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.54/1.50    inference(equality_resolution,[],[f102])).
% 7.54/1.50  
% 7.54/1.50  fof(f99,plain,(
% 7.54/1.50    ( ! [X0,X1] : (~v2_struct_0(sK2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.54/1.50    inference(cnf_transformation,[],[f67])).
% 7.54/1.50  
% 7.54/1.50  fof(f10,axiom,(
% 7.54/1.50    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 7.54/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.54/1.50  
% 7.54/1.50  fof(f33,plain,(
% 7.54/1.50    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 7.54/1.50    inference(ennf_transformation,[],[f10])).
% 7.54/1.50  
% 7.54/1.50  fof(f34,plain,(
% 7.54/1.50    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 7.54/1.50    inference(flattening,[],[f33])).
% 7.54/1.50  
% 7.54/1.50  fof(f92,plain,(
% 7.54/1.50    ( ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 7.54/1.50    inference(cnf_transformation,[],[f34])).
% 7.54/1.50  
% 7.54/1.50  fof(f19,axiom,(
% 7.54/1.50    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 7.54/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.54/1.50  
% 7.54/1.50  fof(f50,plain,(
% 7.54/1.50    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.54/1.50    inference(ennf_transformation,[],[f19])).
% 7.54/1.50  
% 7.54/1.50  fof(f51,plain,(
% 7.54/1.50    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.54/1.50    inference(flattening,[],[f50])).
% 7.54/1.50  
% 7.54/1.50  fof(f108,plain,(
% 7.54/1.50    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.54/1.50    inference(cnf_transformation,[],[f51])).
% 7.54/1.50  
% 7.54/1.50  fof(f116,plain,(
% 7.54/1.50    ~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3)),
% 7.54/1.50    inference(cnf_transformation,[],[f74])).
% 7.54/1.50  
% 7.54/1.50  fof(f100,plain,(
% 7.54/1.50    ( ! [X0,X1] : (m1_pre_topc(sK2(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.54/1.50    inference(cnf_transformation,[],[f67])).
% 7.54/1.50  
% 7.54/1.50  fof(f12,axiom,(
% 7.54/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((~v7_struct_0(X1) & ~v2_struct_0(X1)) => (~v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 7.54/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.54/1.50  
% 7.54/1.50  fof(f37,plain,(
% 7.54/1.50    ! [X0] : (! [X1] : (((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (v7_struct_0(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.54/1.50    inference(ennf_transformation,[],[f12])).
% 7.54/1.50  
% 7.54/1.50  fof(f38,plain,(
% 7.54/1.50    ! [X0] : (! [X1] : ((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.54/1.50    inference(flattening,[],[f37])).
% 7.54/1.50  
% 7.54/1.50  fof(f95,plain,(
% 7.54/1.50    ( ! [X0,X1] : (~v1_tdlat_3(X1) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.54/1.50    inference(cnf_transformation,[],[f38])).
% 7.54/1.50  
% 7.54/1.50  fof(f6,axiom,(
% 7.54/1.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.54/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.54/1.50  
% 7.54/1.50  fof(f27,plain,(
% 7.54/1.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.54/1.50    inference(ennf_transformation,[],[f6])).
% 7.54/1.50  
% 7.54/1.50  fof(f88,plain,(
% 7.54/1.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.54/1.50    inference(cnf_transformation,[],[f27])).
% 7.54/1.50  
% 7.54/1.50  fof(f8,axiom,(
% 7.54/1.50    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 7.54/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.54/1.50  
% 7.54/1.50  fof(f29,plain,(
% 7.54/1.50    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 7.54/1.50    inference(ennf_transformation,[],[f8])).
% 7.54/1.50  
% 7.54/1.50  fof(f30,plain,(
% 7.54/1.50    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 7.54/1.50    inference(flattening,[],[f29])).
% 7.54/1.50  
% 7.54/1.50  fof(f90,plain,(
% 7.54/1.50    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 7.54/1.50    inference(cnf_transformation,[],[f30])).
% 7.54/1.50  
% 7.54/1.50  fof(f7,axiom,(
% 7.54/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.54/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.54/1.50  
% 7.54/1.50  fof(f28,plain,(
% 7.54/1.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.54/1.50    inference(ennf_transformation,[],[f7])).
% 7.54/1.50  
% 7.54/1.50  fof(f89,plain,(
% 7.54/1.50    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.54/1.50    inference(cnf_transformation,[],[f28])).
% 7.54/1.50  
% 7.54/1.50  fof(f11,axiom,(
% 7.54/1.50    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 7.54/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.54/1.50  
% 7.54/1.50  fof(f35,plain,(
% 7.54/1.50    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 7.54/1.50    inference(ennf_transformation,[],[f11])).
% 7.54/1.50  
% 7.54/1.50  fof(f36,plain,(
% 7.54/1.50    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 7.54/1.50    inference(flattening,[],[f35])).
% 7.54/1.50  
% 7.54/1.50  fof(f93,plain,(
% 7.54/1.50    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 7.54/1.50    inference(cnf_transformation,[],[f36])).
% 7.54/1.50  
% 7.54/1.50  fof(f111,plain,(
% 7.54/1.50    v2_tdlat_3(sK3)),
% 7.54/1.50    inference(cnf_transformation,[],[f74])).
% 7.54/1.50  
% 7.54/1.50  fof(f103,plain,(
% 7.54/1.50    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v1_tdlat_3(X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.54/1.50    inference(cnf_transformation,[],[f68])).
% 7.54/1.50  
% 7.54/1.50  fof(f119,plain,(
% 7.54/1.50    ( ! [X0,X1] : (v2_tex_2(u1_struct_0(X1),X0) | ~v1_tdlat_3(X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.54/1.50    inference(equality_resolution,[],[f103])).
% 7.54/1.50  
% 7.54/1.50  fof(f97,plain,(
% 7.54/1.50    ( ! [X0] : (k6_domain_1(X0,sK1(X0)) = X0 | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 7.54/1.50    inference(cnf_transformation,[],[f65])).
% 7.54/1.50  
% 7.54/1.50  fof(f16,axiom,(
% 7.54/1.50    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X0) = X1 => (v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)))))),
% 7.54/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.54/1.50  
% 7.54/1.50  fof(f44,plain,(
% 7.54/1.50    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)) | u1_struct_0(X0) != X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 7.54/1.50    inference(ennf_transformation,[],[f16])).
% 7.54/1.50  
% 7.54/1.50  fof(f45,plain,(
% 7.54/1.50    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)) | u1_struct_0(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.54/1.50    inference(flattening,[],[f44])).
% 7.54/1.50  
% 7.54/1.50  fof(f69,plain,(
% 7.54/1.50    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_tdlat_3(X0)) & (v1_tdlat_3(X0) | ~v2_tex_2(X1,X0))) | u1_struct_0(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.54/1.50    inference(nnf_transformation,[],[f45])).
% 7.54/1.50  
% 7.54/1.50  fof(f104,plain,(
% 7.54/1.50    ( ! [X0,X1] : (v1_tdlat_3(X0) | ~v2_tex_2(X1,X0) | u1_struct_0(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.54/1.50    inference(cnf_transformation,[],[f69])).
% 7.54/1.50  
% 7.54/1.50  fof(f122,plain,(
% 7.54/1.50    ( ! [X0] : (v1_tdlat_3(X0) | ~v2_tex_2(u1_struct_0(X0),X0) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.54/1.50    inference(equality_resolution,[],[f104])).
% 7.54/1.50  
% 7.54/1.50  fof(f17,axiom,(
% 7.54/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 7.54/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.54/1.50  
% 7.54/1.50  fof(f46,plain,(
% 7.54/1.50    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.54/1.50    inference(ennf_transformation,[],[f17])).
% 7.54/1.50  
% 7.54/1.50  fof(f47,plain,(
% 7.54/1.50    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.54/1.50    inference(flattening,[],[f46])).
% 7.54/1.50  
% 7.54/1.50  fof(f106,plain,(
% 7.54/1.50    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.54/1.50    inference(cnf_transformation,[],[f47])).
% 7.54/1.50  
% 7.54/1.50  fof(f110,plain,(
% 7.54/1.50    v2_pre_topc(sK3)),
% 7.54/1.50    inference(cnf_transformation,[],[f74])).
% 7.54/1.50  
% 7.54/1.50  fof(f87,plain,(
% 7.54/1.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.54/1.50    inference(cnf_transformation,[],[f61])).
% 7.54/1.50  
% 7.54/1.50  fof(f2,axiom,(
% 7.54/1.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.54/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.54/1.50  
% 7.54/1.50  fof(f58,plain,(
% 7.54/1.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.54/1.50    inference(nnf_transformation,[],[f2])).
% 7.54/1.50  
% 7.54/1.50  fof(f59,plain,(
% 7.54/1.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.54/1.50    inference(flattening,[],[f58])).
% 7.54/1.50  
% 7.54/1.50  fof(f79,plain,(
% 7.54/1.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.54/1.50    inference(cnf_transformation,[],[f59])).
% 7.54/1.50  
% 7.54/1.50  fof(f117,plain,(
% 7.54/1.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.54/1.50    inference(equality_resolution,[],[f79])).
% 7.54/1.50  
% 7.54/1.50  fof(f76,plain,(
% 7.54/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.54/1.50    inference(cnf_transformation,[],[f57])).
% 7.54/1.50  
% 7.54/1.50  fof(f18,axiom,(
% 7.54/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 7.54/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.54/1.50  
% 7.54/1.50  fof(f48,plain,(
% 7.54/1.50    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.54/1.50    inference(ennf_transformation,[],[f18])).
% 7.54/1.50  
% 7.54/1.50  fof(f49,plain,(
% 7.54/1.50    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.54/1.50    inference(flattening,[],[f48])).
% 7.54/1.50  
% 7.54/1.50  fof(f107,plain,(
% 7.54/1.50    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.54/1.50    inference(cnf_transformation,[],[f49])).
% 7.54/1.50  
% 7.54/1.50  cnf(c_36,negated_conjecture,
% 7.54/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 7.54/1.50      inference(cnf_transformation,[],[f114]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_7141,plain,
% 7.54/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 7.54/1.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_12,plain,
% 7.54/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.54/1.50      inference(cnf_transformation,[],[f86]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_7155,plain,
% 7.54/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.54/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.54/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_7575,plain,
% 7.54/1.50      ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
% 7.54/1.50      inference(superposition,[status(thm)],[c_7141,c_7155]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_23,plain,
% 7.54/1.50      ( m1_subset_1(sK1(X0),X0) | ~ v1_zfmisc_1(X0) | v1_xboole_0(X0) ),
% 7.54/1.50      inference(cnf_transformation,[],[f96]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_7150,plain,
% 7.54/1.50      ( m1_subset_1(sK1(X0),X0) = iProver_top
% 7.54/1.50      | v1_zfmisc_1(X0) != iProver_top
% 7.54/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.54/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_10,plain,
% 7.54/1.50      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.54/1.50      inference(cnf_transformation,[],[f82]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_7157,plain,
% 7.54/1.50      ( m1_subset_1(X0,X1) != iProver_top
% 7.54/1.50      | r2_hidden(X0,X1) = iProver_top
% 7.54/1.50      | v1_xboole_0(X1) = iProver_top ),
% 7.54/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_8654,plain,
% 7.54/1.50      ( r2_hidden(sK1(X0),X0) = iProver_top
% 7.54/1.50      | v1_zfmisc_1(X0) != iProver_top
% 7.54/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.54/1.50      inference(superposition,[status(thm)],[c_7150,c_7157]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_2,plain,
% 7.54/1.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.54/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_7164,plain,
% 7.54/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.54/1.50      | r2_hidden(X0,X2) = iProver_top
% 7.54/1.50      | r1_tarski(X1,X2) != iProver_top ),
% 7.54/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_10150,plain,
% 7.54/1.50      ( r2_hidden(sK1(X0),X1) = iProver_top
% 7.54/1.50      | r1_tarski(X0,X1) != iProver_top
% 7.54/1.50      | v1_zfmisc_1(X0) != iProver_top
% 7.54/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.54/1.50      inference(superposition,[status(thm)],[c_8654,c_7164]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_9,plain,
% 7.54/1.50      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.54/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_7158,plain,
% 7.54/1.50      ( m1_subset_1(X0,X1) = iProver_top
% 7.54/1.50      | r2_hidden(X0,X1) != iProver_top
% 7.54/1.50      | v1_xboole_0(X1) = iProver_top ),
% 7.54/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_14177,plain,
% 7.54/1.50      ( m1_subset_1(sK1(X0),X1) = iProver_top
% 7.54/1.50      | r1_tarski(X0,X1) != iProver_top
% 7.54/1.50      | v1_zfmisc_1(X0) != iProver_top
% 7.54/1.50      | v1_xboole_0(X0) = iProver_top
% 7.54/1.50      | v1_xboole_0(X1) = iProver_top ),
% 7.54/1.50      inference(superposition,[status(thm)],[c_10150,c_7158]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_16,plain,
% 7.54/1.50      ( ~ m1_subset_1(X0,X1)
% 7.54/1.50      | v1_xboole_0(X1)
% 7.54/1.50      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 7.54/1.50      inference(cnf_transformation,[],[f91]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_7153,plain,
% 7.54/1.50      ( k6_domain_1(X0,X1) = k1_tarski(X1)
% 7.54/1.50      | m1_subset_1(X1,X0) != iProver_top
% 7.54/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.54/1.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_20028,plain,
% 7.54/1.50      ( k6_domain_1(X0,sK1(X1)) = k1_tarski(sK1(X1))
% 7.54/1.50      | r1_tarski(X1,X0) != iProver_top
% 7.54/1.50      | v1_zfmisc_1(X1) != iProver_top
% 7.54/1.50      | v1_xboole_0(X1) = iProver_top
% 7.54/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.54/1.50      inference(superposition,[status(thm)],[c_14177,c_7153]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_30596,plain,
% 7.54/1.50      ( k6_domain_1(u1_struct_0(sK3),sK1(sK4)) = k1_tarski(sK1(sK4))
% 7.54/1.50      | v1_zfmisc_1(sK4) != iProver_top
% 7.54/1.50      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
% 7.54/1.50      | v1_xboole_0(sK4) = iProver_top ),
% 7.54/1.50      inference(superposition,[status(thm)],[c_7575,c_20028]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_35,negated_conjecture,
% 7.54/1.50      ( v2_tex_2(sK4,sK3) | v1_zfmisc_1(sK4) ),
% 7.54/1.50      inference(cnf_transformation,[],[f115]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_7142,plain,
% 7.54/1.50      ( v2_tex_2(sK4,sK3) = iProver_top
% 7.54/1.50      | v1_zfmisc_1(sK4) = iProver_top ),
% 7.54/1.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_24,plain,
% 7.54/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.54/1.50      | v2_struct_0(X1)
% 7.54/1.50      | ~ l1_pre_topc(X1)
% 7.54/1.50      | v1_xboole_0(X0)
% 7.54/1.50      | u1_struct_0(sK2(X1,X0)) = X0 ),
% 7.54/1.50      inference(cnf_transformation,[],[f101]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_7149,plain,
% 7.54/1.50      ( u1_struct_0(sK2(X0,X1)) = X1
% 7.54/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.54/1.50      | v2_struct_0(X0) = iProver_top
% 7.54/1.50      | l1_pre_topc(X0) != iProver_top
% 7.54/1.50      | v1_xboole_0(X1) = iProver_top ),
% 7.54/1.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_9212,plain,
% 7.54/1.50      ( u1_struct_0(sK2(sK3,sK4)) = sK4
% 7.54/1.50      | v2_struct_0(sK3) = iProver_top
% 7.54/1.50      | l1_pre_topc(sK3) != iProver_top
% 7.54/1.50      | v1_xboole_0(sK4) = iProver_top ),
% 7.54/1.50      inference(superposition,[status(thm)],[c_7141,c_7149]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_41,negated_conjecture,
% 7.54/1.50      ( ~ v2_struct_0(sK3) ),
% 7.54/1.50      inference(cnf_transformation,[],[f109]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_38,negated_conjecture,
% 7.54/1.50      ( l1_pre_topc(sK3) ),
% 7.54/1.50      inference(cnf_transformation,[],[f112]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_37,negated_conjecture,
% 7.54/1.50      ( ~ v1_xboole_0(sK4) ),
% 7.54/1.50      inference(cnf_transformation,[],[f113]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_7537,plain,
% 7.54/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
% 7.54/1.50      | v2_struct_0(X0)
% 7.54/1.50      | ~ l1_pre_topc(X0)
% 7.54/1.50      | v1_xboole_0(sK4)
% 7.54/1.50      | u1_struct_0(sK2(X0,sK4)) = sK4 ),
% 7.54/1.50      inference(instantiation,[status(thm)],[c_24]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_7539,plain,
% 7.54/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.54/1.50      | v2_struct_0(sK3)
% 7.54/1.50      | ~ l1_pre_topc(sK3)
% 7.54/1.50      | v1_xboole_0(sK4)
% 7.54/1.50      | u1_struct_0(sK2(sK3,sK4)) = sK4 ),
% 7.54/1.50      inference(instantiation,[status(thm)],[c_7537]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_9429,plain,
% 7.54/1.50      ( u1_struct_0(sK2(sK3,sK4)) = sK4 ),
% 7.54/1.50      inference(global_propositional_subsumption,
% 7.54/1.50                [status(thm)],
% 7.54/1.50                [c_9212,c_41,c_38,c_37,c_36,c_7539]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_28,plain,
% 7.54/1.50      ( ~ v2_tex_2(u1_struct_0(X0),X1)
% 7.54/1.50      | ~ m1_pre_topc(X0,X1)
% 7.54/1.50      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.54/1.50      | v2_struct_0(X1)
% 7.54/1.50      | v2_struct_0(X0)
% 7.54/1.50      | v1_tdlat_3(X0)
% 7.54/1.50      | ~ l1_pre_topc(X1) ),
% 7.54/1.50      inference(cnf_transformation,[],[f120]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_7145,plain,
% 7.54/1.50      ( v2_tex_2(u1_struct_0(X0),X1) != iProver_top
% 7.54/1.50      | m1_pre_topc(X0,X1) != iProver_top
% 7.54/1.50      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.54/1.50      | v2_struct_0(X1) = iProver_top
% 7.54/1.50      | v2_struct_0(X0) = iProver_top
% 7.54/1.50      | v1_tdlat_3(X0) = iProver_top
% 7.54/1.50      | l1_pre_topc(X1) != iProver_top ),
% 7.54/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_9925,plain,
% 7.54/1.50      ( v2_tex_2(u1_struct_0(sK2(sK3,sK4)),X0) != iProver_top
% 7.54/1.50      | m1_pre_topc(sK2(sK3,sK4),X0) != iProver_top
% 7.54/1.50      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.54/1.50      | v2_struct_0(X0) = iProver_top
% 7.54/1.50      | v2_struct_0(sK2(sK3,sK4)) = iProver_top
% 7.54/1.50      | v1_tdlat_3(sK2(sK3,sK4)) = iProver_top
% 7.54/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.54/1.50      inference(superposition,[status(thm)],[c_9429,c_7145]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_9948,plain,
% 7.54/1.50      ( v2_tex_2(sK4,X0) != iProver_top
% 7.54/1.50      | m1_pre_topc(sK2(sK3,sK4),X0) != iProver_top
% 7.54/1.50      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.54/1.50      | v2_struct_0(X0) = iProver_top
% 7.54/1.50      | v2_struct_0(sK2(sK3,sK4)) = iProver_top
% 7.54/1.50      | v1_tdlat_3(sK2(sK3,sK4)) = iProver_top
% 7.54/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.54/1.50      inference(light_normalisation,[status(thm)],[c_9925,c_9429]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_42,plain,
% 7.54/1.50      ( v2_struct_0(sK3) != iProver_top ),
% 7.54/1.50      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_45,plain,
% 7.54/1.50      ( l1_pre_topc(sK3) = iProver_top ),
% 7.54/1.50      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_46,plain,
% 7.54/1.50      ( v1_xboole_0(sK4) != iProver_top ),
% 7.54/1.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_47,plain,
% 7.54/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 7.54/1.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_26,plain,
% 7.54/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.54/1.50      | v2_struct_0(X1)
% 7.54/1.50      | ~ v2_struct_0(sK2(X1,X0))
% 7.54/1.50      | ~ l1_pre_topc(X1)
% 7.54/1.50      | v1_xboole_0(X0) ),
% 7.54/1.50      inference(cnf_transformation,[],[f99]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_7524,plain,
% 7.54/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
% 7.54/1.50      | v2_struct_0(X0)
% 7.54/1.50      | ~ v2_struct_0(sK2(X0,sK4))
% 7.54/1.50      | ~ l1_pre_topc(X0)
% 7.54/1.50      | v1_xboole_0(sK4) ),
% 7.54/1.50      inference(instantiation,[status(thm)],[c_26]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_7525,plain,
% 7.54/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.54/1.50      | v2_struct_0(X0) = iProver_top
% 7.54/1.50      | v2_struct_0(sK2(X0,sK4)) != iProver_top
% 7.54/1.50      | l1_pre_topc(X0) != iProver_top
% 7.54/1.50      | v1_xboole_0(sK4) = iProver_top ),
% 7.54/1.50      inference(predicate_to_equality,[status(thm)],[c_7524]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_7527,plain,
% 7.54/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.54/1.50      | v2_struct_0(sK2(sK3,sK4)) != iProver_top
% 7.54/1.50      | v2_struct_0(sK3) = iProver_top
% 7.54/1.50      | l1_pre_topc(sK3) != iProver_top
% 7.54/1.50      | v1_xboole_0(sK4) = iProver_top ),
% 7.54/1.50      inference(instantiation,[status(thm)],[c_7525]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_17,plain,
% 7.54/1.50      ( ~ v1_tdlat_3(X0) | v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 7.54/1.50      inference(cnf_transformation,[],[f92]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_33,plain,
% 7.54/1.50      ( v2_tex_2(X0,X1)
% 7.54/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.54/1.50      | v2_struct_0(X1)
% 7.54/1.50      | ~ v1_tdlat_3(X1)
% 7.54/1.50      | ~ v2_pre_topc(X1)
% 7.54/1.50      | ~ l1_pre_topc(X1) ),
% 7.54/1.50      inference(cnf_transformation,[],[f108]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_765,plain,
% 7.54/1.50      ( v2_tex_2(X0,X1)
% 7.54/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.54/1.50      | v2_struct_0(X1)
% 7.54/1.50      | ~ v1_tdlat_3(X2)
% 7.54/1.50      | ~ v1_tdlat_3(X1)
% 7.54/1.50      | ~ l1_pre_topc(X2)
% 7.54/1.50      | ~ l1_pre_topc(X1)
% 7.54/1.50      | X1 != X2 ),
% 7.54/1.50      inference(resolution_lifted,[status(thm)],[c_17,c_33]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_766,plain,
% 7.54/1.50      ( v2_tex_2(X0,X1)
% 7.54/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.54/1.50      | v2_struct_0(X1)
% 7.54/1.50      | ~ v1_tdlat_3(X1)
% 7.54/1.50      | ~ l1_pre_topc(X1) ),
% 7.54/1.50      inference(unflattening,[status(thm)],[c_765]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_7135,plain,
% 7.54/1.50      ( v2_tex_2(X0,X1) = iProver_top
% 7.54/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.54/1.50      | v2_struct_0(X1) = iProver_top
% 7.54/1.50      | v1_tdlat_3(X1) != iProver_top
% 7.54/1.50      | l1_pre_topc(X1) != iProver_top ),
% 7.54/1.50      inference(predicate_to_equality,[status(thm)],[c_766]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_9438,plain,
% 7.54/1.50      ( v2_tex_2(X0,sK2(sK3,sK4)) = iProver_top
% 7.54/1.50      | m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top
% 7.54/1.50      | v2_struct_0(sK2(sK3,sK4)) = iProver_top
% 7.54/1.50      | v1_tdlat_3(sK2(sK3,sK4)) != iProver_top
% 7.54/1.50      | l1_pre_topc(sK2(sK3,sK4)) != iProver_top ),
% 7.54/1.50      inference(superposition,[status(thm)],[c_9429,c_7135]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_34,negated_conjecture,
% 7.54/1.50      ( ~ v2_tex_2(sK4,sK3) | ~ v1_zfmisc_1(sK4) ),
% 7.54/1.50      inference(cnf_transformation,[],[f116]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_49,plain,
% 7.54/1.50      ( v2_tex_2(sK4,sK3) != iProver_top
% 7.54/1.50      | v1_zfmisc_1(sK4) != iProver_top ),
% 7.54/1.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_25,plain,
% 7.54/1.50      ( m1_pre_topc(sK2(X0,X1),X0)
% 7.54/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.54/1.50      | v2_struct_0(X0)
% 7.54/1.50      | ~ l1_pre_topc(X0)
% 7.54/1.50      | v1_xboole_0(X1) ),
% 7.54/1.50      inference(cnf_transformation,[],[f100]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_7542,plain,
% 7.54/1.50      ( m1_pre_topc(sK2(X0,sK4),X0)
% 7.54/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
% 7.54/1.50      | v2_struct_0(X0)
% 7.54/1.50      | ~ l1_pre_topc(X0)
% 7.54/1.50      | v1_xboole_0(sK4) ),
% 7.54/1.50      inference(instantiation,[status(thm)],[c_25]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_7543,plain,
% 7.54/1.50      ( m1_pre_topc(sK2(X0,sK4),X0) = iProver_top
% 7.54/1.50      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.54/1.50      | v2_struct_0(X0) = iProver_top
% 7.54/1.50      | l1_pre_topc(X0) != iProver_top
% 7.54/1.50      | v1_xboole_0(sK4) = iProver_top ),
% 7.54/1.50      inference(predicate_to_equality,[status(thm)],[c_7542]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_7545,plain,
% 7.54/1.50      ( m1_pre_topc(sK2(sK3,sK4),sK3) = iProver_top
% 7.54/1.50      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.54/1.50      | v2_struct_0(sK3) = iProver_top
% 7.54/1.50      | l1_pre_topc(sK3) != iProver_top
% 7.54/1.50      | v1_xboole_0(sK4) = iProver_top ),
% 7.54/1.50      inference(instantiation,[status(thm)],[c_7543]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_7148,plain,
% 7.54/1.50      ( m1_pre_topc(sK2(X0,X1),X0) = iProver_top
% 7.54/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.54/1.50      | v2_struct_0(X0) = iProver_top
% 7.54/1.50      | l1_pre_topc(X0) != iProver_top
% 7.54/1.50      | v1_xboole_0(X1) = iProver_top ),
% 7.54/1.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_9392,plain,
% 7.54/1.50      ( m1_pre_topc(sK2(sK3,sK4),sK3) = iProver_top
% 7.54/1.50      | v2_struct_0(sK3) = iProver_top
% 7.54/1.50      | l1_pre_topc(sK3) != iProver_top
% 7.54/1.50      | v1_xboole_0(sK4) = iProver_top ),
% 7.54/1.50      inference(superposition,[status(thm)],[c_7141,c_7148]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_9617,plain,
% 7.54/1.50      ( m1_pre_topc(sK2(sK3,sK4),sK3) = iProver_top ),
% 7.54/1.50      inference(global_propositional_subsumption,
% 7.54/1.50                [status(thm)],
% 7.54/1.50                [c_9392,c_42,c_45,c_46,c_47,c_7545]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_19,plain,
% 7.54/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.54/1.50      | v2_struct_0(X1)
% 7.54/1.50      | v2_struct_0(X0)
% 7.54/1.50      | ~ v2_tdlat_3(X1)
% 7.54/1.50      | ~ v1_tdlat_3(X0)
% 7.54/1.50      | ~ v2_pre_topc(X1)
% 7.54/1.50      | v7_struct_0(X0)
% 7.54/1.50      | ~ l1_pre_topc(X1) ),
% 7.54/1.50      inference(cnf_transformation,[],[f95]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_13,plain,
% 7.54/1.50      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 7.54/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_15,plain,
% 7.54/1.50      ( ~ v7_struct_0(X0)
% 7.54/1.50      | v1_zfmisc_1(u1_struct_0(X0))
% 7.54/1.50      | ~ l1_struct_0(X0) ),
% 7.54/1.50      inference(cnf_transformation,[],[f90]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_517,plain,
% 7.54/1.50      ( ~ v7_struct_0(X0)
% 7.54/1.50      | v1_zfmisc_1(u1_struct_0(X0))
% 7.54/1.50      | ~ l1_pre_topc(X0) ),
% 7.54/1.50      inference(resolution,[status(thm)],[c_13,c_15]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_535,plain,
% 7.54/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.54/1.50      | v2_struct_0(X0)
% 7.54/1.50      | v2_struct_0(X1)
% 7.54/1.50      | ~ v2_tdlat_3(X1)
% 7.54/1.50      | ~ v1_tdlat_3(X0)
% 7.54/1.50      | ~ v2_pre_topc(X1)
% 7.54/1.50      | v1_zfmisc_1(u1_struct_0(X0))
% 7.54/1.50      | ~ l1_pre_topc(X0)
% 7.54/1.50      | ~ l1_pre_topc(X1) ),
% 7.54/1.50      inference(resolution,[status(thm)],[c_19,c_517]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_14,plain,
% 7.54/1.50      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.54/1.50      inference(cnf_transformation,[],[f89]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_539,plain,
% 7.54/1.50      ( v1_zfmisc_1(u1_struct_0(X0))
% 7.54/1.50      | ~ v2_pre_topc(X1)
% 7.54/1.50      | ~ v1_tdlat_3(X0)
% 7.54/1.50      | ~ v2_tdlat_3(X1)
% 7.54/1.50      | v2_struct_0(X1)
% 7.54/1.50      | v2_struct_0(X0)
% 7.54/1.50      | ~ m1_pre_topc(X0,X1)
% 7.54/1.50      | ~ l1_pre_topc(X1) ),
% 7.54/1.50      inference(global_propositional_subsumption,
% 7.54/1.50                [status(thm)],
% 7.54/1.50                [c_535,c_14]) ).
% 7.54/1.50  
% 7.54/1.50  cnf(c_540,plain,
% 7.54/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.54/1.50      | v2_struct_0(X0)
% 7.54/1.50      | v2_struct_0(X1)
% 7.54/1.50      | ~ v2_tdlat_3(X1)
% 7.54/1.50      | ~ v1_tdlat_3(X0)
% 7.54/1.51      | ~ v2_pre_topc(X1)
% 7.54/1.51      | v1_zfmisc_1(u1_struct_0(X0))
% 7.54/1.51      | ~ l1_pre_topc(X1) ),
% 7.54/1.51      inference(renaming,[status(thm)],[c_539]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_18,plain,
% 7.54/1.51      ( ~ v2_tdlat_3(X0) | v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 7.54/1.51      inference(cnf_transformation,[],[f93]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_559,plain,
% 7.54/1.51      ( ~ m1_pre_topc(X0,X1)
% 7.54/1.51      | v2_struct_0(X0)
% 7.54/1.51      | v2_struct_0(X1)
% 7.54/1.51      | ~ v2_tdlat_3(X1)
% 7.54/1.51      | ~ v1_tdlat_3(X0)
% 7.54/1.51      | v1_zfmisc_1(u1_struct_0(X0))
% 7.54/1.51      | ~ l1_pre_topc(X1) ),
% 7.54/1.51      inference(forward_subsumption_resolution,
% 7.54/1.51                [status(thm)],
% 7.54/1.51                [c_540,c_18]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_39,negated_conjecture,
% 7.54/1.51      ( v2_tdlat_3(sK3) ),
% 7.54/1.51      inference(cnf_transformation,[],[f111]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_580,plain,
% 7.54/1.51      ( ~ m1_pre_topc(X0,X1)
% 7.54/1.51      | v2_struct_0(X0)
% 7.54/1.51      | v2_struct_0(X1)
% 7.54/1.51      | ~ v1_tdlat_3(X0)
% 7.54/1.51      | v1_zfmisc_1(u1_struct_0(X0))
% 7.54/1.51      | ~ l1_pre_topc(X1)
% 7.54/1.51      | sK3 != X1 ),
% 7.54/1.51      inference(resolution_lifted,[status(thm)],[c_559,c_39]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_581,plain,
% 7.54/1.51      ( ~ m1_pre_topc(X0,sK3)
% 7.54/1.51      | v2_struct_0(X0)
% 7.54/1.51      | v2_struct_0(sK3)
% 7.54/1.51      | ~ v1_tdlat_3(X0)
% 7.54/1.51      | v1_zfmisc_1(u1_struct_0(X0))
% 7.54/1.51      | ~ l1_pre_topc(sK3) ),
% 7.54/1.51      inference(unflattening,[status(thm)],[c_580]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_585,plain,
% 7.54/1.51      ( v1_zfmisc_1(u1_struct_0(X0))
% 7.54/1.51      | ~ v1_tdlat_3(X0)
% 7.54/1.51      | ~ m1_pre_topc(X0,sK3)
% 7.54/1.51      | v2_struct_0(X0) ),
% 7.54/1.51      inference(global_propositional_subsumption,
% 7.54/1.51                [status(thm)],
% 7.54/1.51                [c_581,c_41,c_38]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_586,plain,
% 7.54/1.51      ( ~ m1_pre_topc(X0,sK3)
% 7.54/1.51      | v2_struct_0(X0)
% 7.54/1.51      | ~ v1_tdlat_3(X0)
% 7.54/1.51      | v1_zfmisc_1(u1_struct_0(X0)) ),
% 7.54/1.51      inference(renaming,[status(thm)],[c_585]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_7137,plain,
% 7.54/1.51      ( m1_pre_topc(X0,sK3) != iProver_top
% 7.54/1.51      | v2_struct_0(X0) = iProver_top
% 7.54/1.51      | v1_tdlat_3(X0) != iProver_top
% 7.54/1.51      | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top ),
% 7.54/1.51      inference(predicate_to_equality,[status(thm)],[c_586]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_9623,plain,
% 7.54/1.51      ( v2_struct_0(sK2(sK3,sK4)) = iProver_top
% 7.54/1.51      | v1_tdlat_3(sK2(sK3,sK4)) != iProver_top
% 7.54/1.51      | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) = iProver_top ),
% 7.54/1.51      inference(superposition,[status(thm)],[c_9617,c_7137]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_9627,plain,
% 7.54/1.51      ( v2_struct_0(sK2(sK3,sK4)) = iProver_top
% 7.54/1.51      | v1_tdlat_3(sK2(sK3,sK4)) != iProver_top
% 7.54/1.51      | v1_zfmisc_1(sK4) = iProver_top ),
% 7.54/1.51      inference(light_normalisation,[status(thm)],[c_9623,c_9429]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_9697,plain,
% 7.54/1.51      ( v1_tdlat_3(sK2(sK3,sK4)) != iProver_top
% 7.54/1.51      | v1_zfmisc_1(sK4) = iProver_top ),
% 7.54/1.51      inference(global_propositional_subsumption,
% 7.54/1.51                [status(thm)],
% 7.54/1.51                [c_9627,c_42,c_45,c_46,c_47,c_7527]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_27,plain,
% 7.54/1.51      ( v2_tex_2(u1_struct_0(X0),X1)
% 7.54/1.51      | ~ m1_pre_topc(X0,X1)
% 7.54/1.51      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.54/1.51      | v2_struct_0(X1)
% 7.54/1.51      | v2_struct_0(X0)
% 7.54/1.51      | ~ v1_tdlat_3(X0)
% 7.54/1.51      | ~ l1_pre_topc(X1) ),
% 7.54/1.51      inference(cnf_transformation,[],[f119]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_7146,plain,
% 7.54/1.51      ( v2_tex_2(u1_struct_0(X0),X1) = iProver_top
% 7.54/1.51      | m1_pre_topc(X0,X1) != iProver_top
% 7.54/1.51      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.54/1.51      | v2_struct_0(X1) = iProver_top
% 7.54/1.51      | v2_struct_0(X0) = iProver_top
% 7.54/1.51      | v1_tdlat_3(X0) != iProver_top
% 7.54/1.51      | l1_pre_topc(X1) != iProver_top ),
% 7.54/1.51      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_10077,plain,
% 7.54/1.51      ( v2_tex_2(u1_struct_0(sK2(sK3,sK4)),X0) = iProver_top
% 7.54/1.51      | m1_pre_topc(sK2(sK3,sK4),X0) != iProver_top
% 7.54/1.51      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.54/1.51      | v2_struct_0(X0) = iProver_top
% 7.54/1.51      | v2_struct_0(sK2(sK3,sK4)) = iProver_top
% 7.54/1.51      | v1_tdlat_3(sK2(sK3,sK4)) != iProver_top
% 7.54/1.51      | l1_pre_topc(X0) != iProver_top ),
% 7.54/1.51      inference(superposition,[status(thm)],[c_9429,c_7146]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_10100,plain,
% 7.54/1.51      ( v2_tex_2(sK4,X0) = iProver_top
% 7.54/1.51      | m1_pre_topc(sK2(sK3,sK4),X0) != iProver_top
% 7.54/1.51      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.54/1.51      | v2_struct_0(X0) = iProver_top
% 7.54/1.51      | v2_struct_0(sK2(sK3,sK4)) = iProver_top
% 7.54/1.51      | v1_tdlat_3(sK2(sK3,sK4)) != iProver_top
% 7.54/1.51      | l1_pre_topc(X0) != iProver_top ),
% 7.54/1.51      inference(light_normalisation,[status(thm)],[c_10077,c_9429]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_10144,plain,
% 7.54/1.51      ( v2_tex_2(sK4,sK3) = iProver_top
% 7.54/1.51      | m1_pre_topc(sK2(sK3,sK4),sK3) != iProver_top
% 7.54/1.51      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.54/1.51      | v2_struct_0(sK2(sK3,sK4)) = iProver_top
% 7.54/1.51      | v2_struct_0(sK3) = iProver_top
% 7.54/1.51      | v1_tdlat_3(sK2(sK3,sK4)) != iProver_top
% 7.54/1.51      | l1_pre_topc(sK3) != iProver_top ),
% 7.54/1.51      inference(instantiation,[status(thm)],[c_10100]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_10614,plain,
% 7.54/1.51      ( v1_tdlat_3(sK2(sK3,sK4)) != iProver_top ),
% 7.54/1.51      inference(global_propositional_subsumption,
% 7.54/1.51                [status(thm)],
% 7.54/1.51                [c_9438,c_42,c_45,c_46,c_47,c_49,c_7527,c_7545,c_9697,
% 7.54/1.51                 c_10144]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_10756,plain,
% 7.54/1.51      ( v2_tex_2(sK4,X0) != iProver_top
% 7.54/1.51      | m1_pre_topc(sK2(sK3,sK4),X0) != iProver_top
% 7.54/1.51      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.54/1.51      | v2_struct_0(X0) = iProver_top
% 7.54/1.51      | l1_pre_topc(X0) != iProver_top ),
% 7.54/1.51      inference(global_propositional_subsumption,
% 7.54/1.51                [status(thm)],
% 7.54/1.51                [c_9948,c_42,c_45,c_46,c_47,c_49,c_7527,c_7545,c_9697,
% 7.54/1.51                 c_10144]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_10769,plain,
% 7.54/1.51      ( v2_tex_2(sK4,sK3) != iProver_top
% 7.54/1.51      | m1_pre_topc(sK2(sK3,sK4),sK3) != iProver_top
% 7.54/1.51      | v2_struct_0(sK3) = iProver_top
% 7.54/1.51      | l1_pre_topc(sK3) != iProver_top ),
% 7.54/1.51      inference(superposition,[status(thm)],[c_7141,c_10756]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_9994,plain,
% 7.54/1.51      ( v2_tex_2(sK4,sK3) != iProver_top
% 7.54/1.51      | m1_pre_topc(sK2(sK3,sK4),sK3) != iProver_top
% 7.54/1.51      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.54/1.51      | v2_struct_0(sK2(sK3,sK4)) = iProver_top
% 7.54/1.51      | v2_struct_0(sK3) = iProver_top
% 7.54/1.51      | v1_tdlat_3(sK2(sK3,sK4)) = iProver_top
% 7.54/1.51      | l1_pre_topc(sK3) != iProver_top ),
% 7.54/1.51      inference(instantiation,[status(thm)],[c_9948]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_10985,plain,
% 7.54/1.51      ( v2_tex_2(sK4,sK3) != iProver_top ),
% 7.54/1.51      inference(global_propositional_subsumption,
% 7.54/1.51                [status(thm)],
% 7.54/1.51                [c_10769,c_42,c_45,c_46,c_47,c_49,c_7527,c_7545,c_9697,
% 7.54/1.51                 c_9994,c_10144]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_10991,plain,
% 7.54/1.51      ( v1_zfmisc_1(sK4) = iProver_top ),
% 7.54/1.51      inference(superposition,[status(thm)],[c_7142,c_10985]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_8741,plain,
% 7.54/1.51      ( k6_domain_1(X0,sK1(X0)) = k1_tarski(sK1(X0))
% 7.54/1.51      | v1_zfmisc_1(X0) != iProver_top
% 7.54/1.51      | v1_xboole_0(X0) = iProver_top ),
% 7.54/1.51      inference(superposition,[status(thm)],[c_7150,c_7153]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_11129,plain,
% 7.54/1.51      ( k6_domain_1(sK4,sK1(sK4)) = k1_tarski(sK1(sK4))
% 7.54/1.51      | v1_xboole_0(sK4) = iProver_top ),
% 7.54/1.51      inference(superposition,[status(thm)],[c_10991,c_8741]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_22,plain,
% 7.54/1.51      ( ~ v1_zfmisc_1(X0)
% 7.54/1.51      | v1_xboole_0(X0)
% 7.54/1.51      | k6_domain_1(X0,sK1(X0)) = X0 ),
% 7.54/1.51      inference(cnf_transformation,[],[f97]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_7151,plain,
% 7.54/1.51      ( k6_domain_1(X0,sK1(X0)) = X0
% 7.54/1.51      | v1_zfmisc_1(X0) != iProver_top
% 7.54/1.51      | v1_xboole_0(X0) = iProver_top ),
% 7.54/1.51      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_11081,plain,
% 7.54/1.51      ( k6_domain_1(sK4,sK1(sK4)) = sK4
% 7.54/1.51      | v1_xboole_0(sK4) = iProver_top ),
% 7.54/1.51      inference(superposition,[status(thm)],[c_10991,c_7151]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_306,plain,
% 7.54/1.51      ( v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3) ),
% 7.54/1.51      inference(prop_impl,[status(thm)],[c_35]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_307,plain,
% 7.54/1.51      ( v2_tex_2(sK4,sK3) | v1_zfmisc_1(sK4) ),
% 7.54/1.51      inference(renaming,[status(thm)],[c_306]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_982,plain,
% 7.54/1.51      ( v2_tex_2(sK4,sK3)
% 7.54/1.51      | v1_xboole_0(X0)
% 7.54/1.51      | k6_domain_1(X0,sK1(X0)) = X0
% 7.54/1.51      | sK4 != X0 ),
% 7.54/1.51      inference(resolution_lifted,[status(thm)],[c_22,c_307]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_983,plain,
% 7.54/1.51      ( v2_tex_2(sK4,sK3)
% 7.54/1.51      | v1_xboole_0(sK4)
% 7.54/1.51      | k6_domain_1(sK4,sK1(sK4)) = sK4 ),
% 7.54/1.51      inference(unflattening,[status(thm)],[c_982]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_984,plain,
% 7.54/1.51      ( k6_domain_1(sK4,sK1(sK4)) = sK4
% 7.54/1.51      | v2_tex_2(sK4,sK3) = iProver_top
% 7.54/1.51      | v1_xboole_0(sK4) = iProver_top ),
% 7.54/1.51      inference(predicate_to_equality,[status(thm)],[c_983]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_11084,plain,
% 7.54/1.51      ( k6_domain_1(sK4,sK1(sK4)) = sK4 ),
% 7.54/1.51      inference(global_propositional_subsumption,
% 7.54/1.51                [status(thm)],
% 7.54/1.51                [c_11081,c_42,c_45,c_46,c_47,c_49,c_984,c_7527,c_7545,
% 7.54/1.51                 c_9697,c_9994,c_10144]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_11130,plain,
% 7.54/1.51      ( k1_tarski(sK1(sK4)) = sK4 | v1_xboole_0(sK4) = iProver_top ),
% 7.54/1.51      inference(light_normalisation,[status(thm)],[c_11129,c_11084]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_11343,plain,
% 7.54/1.51      ( k1_tarski(sK1(sK4)) = sK4 ),
% 7.54/1.51      inference(global_propositional_subsumption,
% 7.54/1.51                [status(thm)],
% 7.54/1.51                [c_11130,c_46]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_30806,plain,
% 7.54/1.51      ( k6_domain_1(u1_struct_0(sK3),sK1(sK4)) = sK4
% 7.54/1.51      | v1_zfmisc_1(sK4) != iProver_top
% 7.54/1.51      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
% 7.54/1.51      | v1_xboole_0(sK4) = iProver_top ),
% 7.54/1.51      inference(light_normalisation,[status(thm)],[c_30596,c_11343]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_30,plain,
% 7.54/1.51      ( ~ v2_tex_2(u1_struct_0(X0),X0)
% 7.54/1.51      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 7.54/1.51      | v2_struct_0(X0)
% 7.54/1.51      | v1_tdlat_3(X0)
% 7.54/1.51      | ~ l1_pre_topc(X0) ),
% 7.54/1.51      inference(cnf_transformation,[],[f122]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_31,plain,
% 7.54/1.51      ( v2_tex_2(X0,X1)
% 7.54/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.54/1.51      | v2_struct_0(X1)
% 7.54/1.51      | ~ v2_pre_topc(X1)
% 7.54/1.51      | ~ l1_pre_topc(X1)
% 7.54/1.51      | ~ v1_xboole_0(X0) ),
% 7.54/1.51      inference(cnf_transformation,[],[f106]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_40,negated_conjecture,
% 7.54/1.51      ( v2_pre_topc(sK3) ),
% 7.54/1.51      inference(cnf_transformation,[],[f110]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_825,plain,
% 7.54/1.51      ( v2_tex_2(X0,X1)
% 7.54/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.54/1.51      | v2_struct_0(X1)
% 7.54/1.51      | ~ l1_pre_topc(X1)
% 7.54/1.51      | ~ v1_xboole_0(X0)
% 7.54/1.51      | sK3 != X1 ),
% 7.54/1.51      inference(resolution_lifted,[status(thm)],[c_31,c_40]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_826,plain,
% 7.54/1.51      ( v2_tex_2(X0,sK3)
% 7.54/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.54/1.51      | v2_struct_0(sK3)
% 7.54/1.51      | ~ l1_pre_topc(sK3)
% 7.54/1.51      | ~ v1_xboole_0(X0) ),
% 7.54/1.51      inference(unflattening,[status(thm)],[c_825]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_830,plain,
% 7.54/1.51      ( v2_tex_2(X0,sK3)
% 7.54/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.54/1.51      | ~ v1_xboole_0(X0) ),
% 7.54/1.51      inference(global_propositional_subsumption,
% 7.54/1.51                [status(thm)],
% 7.54/1.51                [c_826,c_41,c_38]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_1629,plain,
% 7.54/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.54/1.51      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
% 7.54/1.51      | v2_struct_0(X1)
% 7.54/1.51      | v1_tdlat_3(X1)
% 7.54/1.51      | ~ l1_pre_topc(X1)
% 7.54/1.51      | ~ v1_xboole_0(X0)
% 7.54/1.51      | u1_struct_0(X1) != X0
% 7.54/1.51      | sK3 != X1 ),
% 7.54/1.51      inference(resolution_lifted,[status(thm)],[c_30,c_830]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_1630,plain,
% 7.54/1.51      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 7.54/1.51      | v2_struct_0(sK3)
% 7.54/1.51      | v1_tdlat_3(sK3)
% 7.54/1.51      | ~ l1_pre_topc(sK3)
% 7.54/1.51      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 7.54/1.51      inference(unflattening,[status(thm)],[c_1629]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_1632,plain,
% 7.54/1.51      ( v1_tdlat_3(sK3)
% 7.54/1.51      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 7.54/1.51      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 7.54/1.51      inference(global_propositional_subsumption,
% 7.54/1.51                [status(thm)],
% 7.54/1.51                [c_1630,c_41,c_38]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_1633,plain,
% 7.54/1.51      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 7.54/1.51      | v1_tdlat_3(sK3)
% 7.54/1.51      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 7.54/1.51      inference(renaming,[status(thm)],[c_1632]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_1634,plain,
% 7.54/1.51      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.54/1.51      | v1_tdlat_3(sK3) = iProver_top
% 7.54/1.51      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 7.54/1.51      inference(predicate_to_equality,[status(thm)],[c_1633]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_11,plain,
% 7.54/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.54/1.51      inference(cnf_transformation,[],[f87]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_7484,plain,
% 7.54/1.51      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.54/1.51      | ~ r1_tarski(X0,u1_struct_0(sK3)) ),
% 7.54/1.51      inference(instantiation,[status(thm)],[c_11]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_7805,plain,
% 7.54/1.51      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 7.54/1.51      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
% 7.54/1.51      inference(instantiation,[status(thm)],[c_7484]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_7807,plain,
% 7.54/1.51      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 7.54/1.51      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top ),
% 7.54/1.51      inference(predicate_to_equality,[status(thm)],[c_7805]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_4,plain,
% 7.54/1.51      ( r1_tarski(X0,X0) ),
% 7.54/1.51      inference(cnf_transformation,[],[f117]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_7806,plain,
% 7.54/1.51      ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) ),
% 7.54/1.51      inference(instantiation,[status(thm)],[c_4]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_7809,plain,
% 7.54/1.51      ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
% 7.54/1.51      inference(predicate_to_equality,[status(thm)],[c_7806]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_1,plain,
% 7.54/1.51      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.54/1.51      inference(cnf_transformation,[],[f76]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_7165,plain,
% 7.54/1.51      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 7.54/1.51      | r1_tarski(X0,X1) = iProver_top ),
% 7.54/1.51      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_8679,plain,
% 7.54/1.51      ( m1_subset_1(sK0(X0,X1),X0) = iProver_top
% 7.54/1.51      | r1_tarski(X0,X1) = iProver_top
% 7.54/1.51      | v1_xboole_0(X0) = iProver_top ),
% 7.54/1.51      inference(superposition,[status(thm)],[c_7165,c_7158]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_806,plain,
% 7.54/1.51      ( v2_tex_2(X0,X1)
% 7.54/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.54/1.51      | v2_struct_0(X1)
% 7.54/1.51      | ~ v1_tdlat_3(X1)
% 7.54/1.51      | ~ l1_pre_topc(X1)
% 7.54/1.51      | sK3 != X1 ),
% 7.54/1.51      inference(resolution_lifted,[status(thm)],[c_33,c_40]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_807,plain,
% 7.54/1.51      ( v2_tex_2(X0,sK3)
% 7.54/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.54/1.51      | v2_struct_0(sK3)
% 7.54/1.51      | ~ v1_tdlat_3(sK3)
% 7.54/1.51      | ~ l1_pre_topc(sK3) ),
% 7.54/1.51      inference(unflattening,[status(thm)],[c_806]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_809,plain,
% 7.54/1.51      ( ~ v1_tdlat_3(sK3)
% 7.54/1.51      | v2_tex_2(X0,sK3)
% 7.54/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 7.54/1.51      inference(global_propositional_subsumption,
% 7.54/1.51                [status(thm)],
% 7.54/1.51                [c_807,c_41,c_38]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_810,plain,
% 7.54/1.51      ( v2_tex_2(X0,sK3)
% 7.54/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.54/1.51      | ~ v1_tdlat_3(sK3) ),
% 7.54/1.51      inference(renaming,[status(thm)],[c_809]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_7133,plain,
% 7.54/1.51      ( v2_tex_2(X0,sK3) = iProver_top
% 7.54/1.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.54/1.51      | v1_tdlat_3(sK3) != iProver_top ),
% 7.54/1.51      inference(predicate_to_equality,[status(thm)],[c_810]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_10249,plain,
% 7.54/1.51      ( v2_tex_2(sK0(k1_zfmisc_1(u1_struct_0(sK3)),X0),sK3) = iProver_top
% 7.54/1.51      | r1_tarski(k1_zfmisc_1(u1_struct_0(sK3)),X0) = iProver_top
% 7.54/1.51      | v1_tdlat_3(sK3) != iProver_top
% 7.54/1.51      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 7.54/1.51      inference(superposition,[status(thm)],[c_8679,c_7133]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_3113,plain,
% 7.54/1.51      ( v2_tex_2(X0,sK3)
% 7.54/1.51      | ~ v1_tdlat_3(sK3)
% 7.54/1.51      | k1_zfmisc_1(u1_struct_0(sK3)) != k1_zfmisc_1(u1_struct_0(sK3))
% 7.54/1.51      | sK4 != X0 ),
% 7.54/1.51      inference(resolution_lifted,[status(thm)],[c_36,c_810]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_3114,plain,
% 7.54/1.51      ( v2_tex_2(sK4,sK3) | ~ v1_tdlat_3(sK3) ),
% 7.54/1.51      inference(unflattening,[status(thm)],[c_3113]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_3115,plain,
% 7.54/1.51      ( v2_tex_2(sK4,sK3) = iProver_top
% 7.54/1.51      | v1_tdlat_3(sK3) != iProver_top ),
% 7.54/1.51      inference(predicate_to_equality,[status(thm)],[c_3114]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_10506,plain,
% 7.54/1.51      ( v1_tdlat_3(sK3) != iProver_top ),
% 7.54/1.51      inference(global_propositional_subsumption,
% 7.54/1.51                [status(thm)],
% 7.54/1.51                [c_10249,c_42,c_45,c_46,c_47,c_49,c_3115,c_7527,c_7545,
% 7.54/1.51                 c_9697,c_9994,c_10144]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_7162,plain,
% 7.54/1.51      ( r1_tarski(X0,X0) = iProver_top ),
% 7.54/1.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_14176,plain,
% 7.54/1.51      ( r2_hidden(sK1(X0),X1) = iProver_top
% 7.54/1.51      | r1_tarski(X0,X2) != iProver_top
% 7.54/1.51      | r1_tarski(X2,X1) != iProver_top
% 7.54/1.51      | v1_zfmisc_1(X0) != iProver_top
% 7.54/1.51      | v1_xboole_0(X0) = iProver_top ),
% 7.54/1.51      inference(superposition,[status(thm)],[c_10150,c_7164]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_29230,plain,
% 7.54/1.51      ( r2_hidden(sK1(sK4),X0) = iProver_top
% 7.54/1.51      | r1_tarski(u1_struct_0(sK3),X0) != iProver_top
% 7.54/1.51      | v1_zfmisc_1(sK4) != iProver_top
% 7.54/1.51      | v1_xboole_0(sK4) = iProver_top ),
% 7.54/1.51      inference(superposition,[status(thm)],[c_7575,c_14176]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_48,plain,
% 7.54/1.51      ( v2_tex_2(sK4,sK3) = iProver_top
% 7.54/1.51      | v1_zfmisc_1(sK4) = iProver_top ),
% 7.54/1.51      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_29495,plain,
% 7.54/1.51      ( r2_hidden(sK1(sK4),X0) = iProver_top
% 7.54/1.51      | r1_tarski(u1_struct_0(sK3),X0) != iProver_top ),
% 7.54/1.51      inference(global_propositional_subsumption,
% 7.54/1.51                [status(thm)],
% 7.54/1.51                [c_29230,c_42,c_45,c_46,c_47,c_48,c_49,c_7527,c_7545,
% 7.54/1.51                 c_9697,c_9994,c_10144]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_29506,plain,
% 7.54/1.51      ( r2_hidden(sK1(sK4),u1_struct_0(sK3)) = iProver_top ),
% 7.54/1.51      inference(superposition,[status(thm)],[c_7162,c_29495]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_30377,plain,
% 7.54/1.51      ( m1_subset_1(sK1(sK4),u1_struct_0(sK3)) = iProver_top
% 7.54/1.51      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 7.54/1.51      inference(superposition,[status(thm)],[c_29506,c_7158]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_968,plain,
% 7.54/1.51      ( v2_tex_2(sK4,sK3)
% 7.54/1.51      | m1_subset_1(sK1(X0),X0)
% 7.54/1.51      | v1_xboole_0(X0)
% 7.54/1.51      | sK4 != X0 ),
% 7.54/1.51      inference(resolution_lifted,[status(thm)],[c_23,c_307]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_969,plain,
% 7.54/1.51      ( v2_tex_2(sK4,sK3)
% 7.54/1.51      | m1_subset_1(sK1(sK4),sK4)
% 7.54/1.51      | v1_xboole_0(sK4) ),
% 7.54/1.51      inference(unflattening,[status(thm)],[c_968]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_970,plain,
% 7.54/1.51      ( v2_tex_2(sK4,sK3) = iProver_top
% 7.54/1.51      | m1_subset_1(sK1(sK4),sK4) = iProver_top
% 7.54/1.51      | v1_xboole_0(sK4) = iProver_top ),
% 7.54/1.51      inference(predicate_to_equality,[status(thm)],[c_969]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_7506,plain,
% 7.54/1.51      ( ~ m1_subset_1(X0,sK4) | r2_hidden(X0,sK4) | v1_xboole_0(sK4) ),
% 7.54/1.51      inference(instantiation,[status(thm)],[c_10]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_7873,plain,
% 7.54/1.51      ( ~ m1_subset_1(sK1(sK4),sK4)
% 7.54/1.51      | r2_hidden(sK1(sK4),sK4)
% 7.54/1.51      | v1_xboole_0(sK4) ),
% 7.54/1.51      inference(instantiation,[status(thm)],[c_7506]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_7874,plain,
% 7.54/1.51      ( m1_subset_1(sK1(sK4),sK4) != iProver_top
% 7.54/1.51      | r2_hidden(sK1(sK4),sK4) = iProver_top
% 7.54/1.51      | v1_xboole_0(sK4) = iProver_top ),
% 7.54/1.51      inference(predicate_to_equality,[status(thm)],[c_7873]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_8122,plain,
% 7.54/1.51      ( r2_hidden(sK1(sK4),X0)
% 7.54/1.51      | ~ r2_hidden(sK1(sK4),sK4)
% 7.54/1.51      | ~ r1_tarski(sK4,X0) ),
% 7.54/1.51      inference(instantiation,[status(thm)],[c_2]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_10443,plain,
% 7.54/1.51      ( r2_hidden(sK1(sK4),u1_struct_0(sK3))
% 7.54/1.51      | ~ r2_hidden(sK1(sK4),sK4)
% 7.54/1.51      | ~ r1_tarski(sK4,u1_struct_0(sK3)) ),
% 7.54/1.51      inference(instantiation,[status(thm)],[c_8122]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_10445,plain,
% 7.54/1.51      ( r2_hidden(sK1(sK4),u1_struct_0(sK3)) = iProver_top
% 7.54/1.51      | r2_hidden(sK1(sK4),sK4) != iProver_top
% 7.54/1.51      | r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top ),
% 7.54/1.51      inference(predicate_to_equality,[status(thm)],[c_10443]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_7709,plain,
% 7.54/1.51      ( m1_subset_1(X0,u1_struct_0(sK3))
% 7.54/1.51      | ~ r2_hidden(X0,u1_struct_0(sK3))
% 7.54/1.51      | v1_xboole_0(u1_struct_0(sK3)) ),
% 7.54/1.51      inference(instantiation,[status(thm)],[c_9]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_10444,plain,
% 7.54/1.51      ( m1_subset_1(sK1(sK4),u1_struct_0(sK3))
% 7.54/1.51      | ~ r2_hidden(sK1(sK4),u1_struct_0(sK3))
% 7.54/1.51      | v1_xboole_0(u1_struct_0(sK3)) ),
% 7.54/1.51      inference(instantiation,[status(thm)],[c_7709]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_10447,plain,
% 7.54/1.51      ( m1_subset_1(sK1(sK4),u1_struct_0(sK3)) = iProver_top
% 7.54/1.51      | r2_hidden(sK1(sK4),u1_struct_0(sK3)) != iProver_top
% 7.54/1.51      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 7.54/1.51      inference(predicate_to_equality,[status(thm)],[c_10444]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_30572,plain,
% 7.54/1.51      ( m1_subset_1(sK1(sK4),u1_struct_0(sK3)) = iProver_top ),
% 7.54/1.51      inference(global_propositional_subsumption,
% 7.54/1.51                [status(thm)],
% 7.54/1.51                [c_30377,c_42,c_45,c_46,c_47,c_49,c_970,c_1634,c_3115,
% 7.54/1.51                 c_7527,c_7545,c_7575,c_7807,c_7809,c_7874,c_9697,c_9994,
% 7.54/1.51                 c_10144,c_10445,c_10447]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_30577,plain,
% 7.54/1.51      ( k6_domain_1(u1_struct_0(sK3),sK1(sK4)) = k1_tarski(sK1(sK4))
% 7.54/1.51      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 7.54/1.51      inference(superposition,[status(thm)],[c_30572,c_7153]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_30582,plain,
% 7.54/1.51      ( k6_domain_1(u1_struct_0(sK3),sK1(sK4)) = sK4
% 7.54/1.51      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 7.54/1.51      inference(light_normalisation,[status(thm)],[c_30577,c_11343]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_33410,plain,
% 7.54/1.51      ( k6_domain_1(u1_struct_0(sK3),sK1(sK4)) = sK4 ),
% 7.54/1.51      inference(global_propositional_subsumption,
% 7.54/1.51                [status(thm)],
% 7.54/1.51                [c_30806,c_42,c_45,c_46,c_47,c_49,c_1634,c_3115,c_7527,
% 7.54/1.51                 c_7545,c_7807,c_7809,c_9697,c_9994,c_10144,c_30582]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_32,plain,
% 7.54/1.51      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 7.54/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.54/1.51      | v2_struct_0(X0)
% 7.54/1.51      | ~ v2_pre_topc(X0)
% 7.54/1.51      | ~ l1_pre_topc(X0) ),
% 7.54/1.51      inference(cnf_transformation,[],[f107]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_788,plain,
% 7.54/1.51      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 7.54/1.51      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.54/1.51      | v2_struct_0(X0)
% 7.54/1.51      | ~ l1_pre_topc(X0)
% 7.54/1.51      | sK3 != X0 ),
% 7.54/1.51      inference(resolution_lifted,[status(thm)],[c_32,c_40]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_789,plain,
% 7.54/1.51      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
% 7.54/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 7.54/1.51      | v2_struct_0(sK3)
% 7.54/1.51      | ~ l1_pre_topc(sK3) ),
% 7.54/1.51      inference(unflattening,[status(thm)],[c_788]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_793,plain,
% 7.54/1.51      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
% 7.54/1.51      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 7.54/1.51      inference(global_propositional_subsumption,
% 7.54/1.51                [status(thm)],
% 7.54/1.51                [c_789,c_41,c_38]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_7134,plain,
% 7.54/1.51      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) = iProver_top
% 7.54/1.51      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 7.54/1.51      inference(predicate_to_equality,[status(thm)],[c_793]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(c_33415,plain,
% 7.54/1.51      ( v2_tex_2(sK4,sK3) = iProver_top
% 7.54/1.51      | m1_subset_1(sK1(sK4),u1_struct_0(sK3)) != iProver_top ),
% 7.54/1.51      inference(superposition,[status(thm)],[c_33410,c_7134]) ).
% 7.54/1.51  
% 7.54/1.51  cnf(contradiction,plain,
% 7.54/1.51      ( $false ),
% 7.54/1.51      inference(minisat,
% 7.54/1.51                [status(thm)],
% 7.54/1.51                [c_33415,c_10614,c_10506,c_10447,c_10445,c_9994,c_7874,
% 7.54/1.51                 c_7809,c_7807,c_7575,c_7545,c_7527,c_1634,c_970,c_47,
% 7.54/1.51                 c_46,c_45,c_42]) ).
% 7.54/1.51  
% 7.54/1.51  
% 7.54/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.54/1.51  
% 7.54/1.51  ------                               Statistics
% 7.54/1.51  
% 7.54/1.51  ------ General
% 7.54/1.51  
% 7.54/1.51  abstr_ref_over_cycles:                  0
% 7.54/1.51  abstr_ref_under_cycles:                 0
% 7.54/1.51  gc_basic_clause_elim:                   0
% 7.54/1.51  forced_gc_time:                         0
% 7.54/1.51  parsing_time:                           0.01
% 7.54/1.51  unif_index_cands_time:                  0.
% 7.54/1.51  unif_index_add_time:                    0.
% 7.54/1.51  orderings_time:                         0.
% 7.54/1.51  out_proof_time:                         0.014
% 7.54/1.51  total_time:                             0.727
% 7.54/1.51  num_of_symbols:                         54
% 7.54/1.51  num_of_terms:                           15642
% 7.54/1.51  
% 7.54/1.51  ------ Preprocessing
% 7.54/1.51  
% 7.54/1.51  num_of_splits:                          0
% 7.54/1.51  num_of_split_atoms:                     0
% 7.54/1.51  num_of_reused_defs:                     0
% 7.54/1.51  num_eq_ax_congr_red:                    31
% 7.54/1.51  num_of_sem_filtered_clauses:            1
% 7.54/1.51  num_of_subtypes:                        0
% 7.54/1.51  monotx_restored_types:                  0
% 7.54/1.51  sat_num_of_epr_types:                   0
% 7.54/1.51  sat_num_of_non_cyclic_types:            0
% 7.54/1.51  sat_guarded_non_collapsed_types:        0
% 7.54/1.51  num_pure_diseq_elim:                    0
% 7.54/1.51  simp_replaced_by:                       0
% 7.54/1.51  res_preprocessed:                       174
% 7.54/1.51  prep_upred:                             0
% 7.54/1.51  prep_unflattend:                        321
% 7.54/1.51  smt_new_axioms:                         0
% 7.54/1.51  pred_elim_cands:                        10
% 7.54/1.51  pred_elim:                              4
% 7.54/1.51  pred_elim_cl:                           5
% 7.54/1.51  pred_elim_cycles:                       14
% 7.54/1.51  merged_defs:                            16
% 7.54/1.51  merged_defs_ncl:                        0
% 7.54/1.51  bin_hyper_res:                          16
% 7.54/1.51  prep_cycles:                            4
% 7.54/1.51  pred_elim_time:                         0.091
% 7.54/1.51  splitting_time:                         0.
% 7.54/1.51  sem_filter_time:                        0.
% 7.54/1.51  monotx_time:                            0.
% 7.54/1.51  subtype_inf_time:                       0.
% 7.54/1.51  
% 7.54/1.51  ------ Problem properties
% 7.54/1.51  
% 7.54/1.51  clauses:                                35
% 7.54/1.51  conjectures:                            6
% 7.54/1.51  epr:                                    14
% 7.54/1.51  horn:                                   18
% 7.54/1.51  ground:                                 6
% 7.54/1.51  unary:                                  5
% 7.54/1.51  binary:                                 7
% 7.54/1.51  lits:                                   110
% 7.54/1.51  lits_eq:                                5
% 7.54/1.51  fd_pure:                                0
% 7.54/1.51  fd_pseudo:                              0
% 7.54/1.51  fd_cond:                                0
% 7.54/1.51  fd_pseudo_cond:                         1
% 7.54/1.51  ac_symbols:                             0
% 7.54/1.51  
% 7.54/1.51  ------ Propositional Solver
% 7.54/1.51  
% 7.54/1.51  prop_solver_calls:                      31
% 7.54/1.51  prop_fast_solver_calls:                 3602
% 7.54/1.51  smt_solver_calls:                       0
% 7.54/1.51  smt_fast_solver_calls:                  0
% 7.54/1.51  prop_num_of_clauses:                    8839
% 7.54/1.51  prop_preprocess_simplified:             18992
% 7.54/1.51  prop_fo_subsumed:                       232
% 7.54/1.51  prop_solver_time:                       0.
% 7.54/1.51  smt_solver_time:                        0.
% 7.54/1.51  smt_fast_solver_time:                   0.
% 7.54/1.51  prop_fast_solver_time:                  0.
% 7.54/1.51  prop_unsat_core_time:                   0.
% 7.54/1.51  
% 7.54/1.51  ------ QBF
% 7.54/1.51  
% 7.54/1.51  qbf_q_res:                              0
% 7.54/1.51  qbf_num_tautologies:                    0
% 7.54/1.51  qbf_prep_cycles:                        0
% 7.54/1.51  
% 7.54/1.51  ------ BMC1
% 7.54/1.51  
% 7.54/1.51  bmc1_current_bound:                     -1
% 7.54/1.51  bmc1_last_solved_bound:                 -1
% 7.54/1.51  bmc1_unsat_core_size:                   -1
% 7.54/1.51  bmc1_unsat_core_parents_size:           -1
% 7.54/1.51  bmc1_merge_next_fun:                    0
% 7.54/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.54/1.51  
% 7.54/1.51  ------ Instantiation
% 7.54/1.51  
% 7.54/1.51  inst_num_of_clauses:                    1955
% 7.54/1.51  inst_num_in_passive:                    826
% 7.54/1.51  inst_num_in_active:                     829
% 7.54/1.51  inst_num_in_unprocessed:                303
% 7.54/1.51  inst_num_of_loops:                      1160
% 7.54/1.51  inst_num_of_learning_restarts:          0
% 7.54/1.51  inst_num_moves_active_passive:          327
% 7.54/1.51  inst_lit_activity:                      0
% 7.54/1.51  inst_lit_activity_moves:                0
% 7.54/1.51  inst_num_tautologies:                   0
% 7.54/1.51  inst_num_prop_implied:                  0
% 7.54/1.51  inst_num_existing_simplified:           0
% 7.54/1.51  inst_num_eq_res_simplified:             0
% 7.54/1.51  inst_num_child_elim:                    0
% 7.54/1.51  inst_num_of_dismatching_blockings:      1410
% 7.54/1.51  inst_num_of_non_proper_insts:           2402
% 7.54/1.51  inst_num_of_duplicates:                 0
% 7.54/1.51  inst_inst_num_from_inst_to_res:         0
% 7.54/1.51  inst_dismatching_checking_time:         0.
% 7.54/1.51  
% 7.54/1.51  ------ Resolution
% 7.54/1.51  
% 7.54/1.51  res_num_of_clauses:                     0
% 7.54/1.51  res_num_in_passive:                     0
% 7.54/1.51  res_num_in_active:                      0
% 7.54/1.51  res_num_of_loops:                       178
% 7.54/1.51  res_forward_subset_subsumed:            389
% 7.54/1.51  res_backward_subset_subsumed:           12
% 7.54/1.51  res_forward_subsumed:                   2
% 7.54/1.51  res_backward_subsumed:                  1
% 7.54/1.51  res_forward_subsumption_resolution:     5
% 7.54/1.51  res_backward_subsumption_resolution:    3
% 7.54/1.51  res_clause_to_clause_subsumption:       5448
% 7.54/1.51  res_orphan_elimination:                 0
% 7.54/1.51  res_tautology_del:                      379
% 7.54/1.51  res_num_eq_res_simplified:              0
% 7.54/1.51  res_num_sel_changes:                    0
% 7.54/1.51  res_moves_from_active_to_pass:          0
% 7.54/1.51  
% 7.54/1.51  ------ Superposition
% 7.54/1.51  
% 7.54/1.51  sup_time_total:                         0.
% 7.54/1.51  sup_time_generating:                    0.
% 7.54/1.51  sup_time_sim_full:                      0.
% 7.54/1.51  sup_time_sim_immed:                     0.
% 7.54/1.51  
% 7.54/1.51  sup_num_of_clauses:                     796
% 7.54/1.51  sup_num_in_active:                      228
% 7.54/1.51  sup_num_in_passive:                     568
% 7.54/1.51  sup_num_of_loops:                       231
% 7.54/1.51  sup_fw_superposition:                   435
% 7.54/1.51  sup_bw_superposition:                   702
% 7.54/1.51  sup_immediate_simplified:               238
% 7.54/1.51  sup_given_eliminated:                   0
% 7.54/1.51  comparisons_done:                       0
% 7.54/1.51  comparisons_avoided:                    115
% 7.54/1.51  
% 7.54/1.51  ------ Simplifications
% 7.54/1.51  
% 7.54/1.51  
% 7.54/1.51  sim_fw_subset_subsumed:                 140
% 7.54/1.51  sim_bw_subset_subsumed:                 7
% 7.54/1.51  sim_fw_subsumed:                        57
% 7.54/1.51  sim_bw_subsumed:                        6
% 7.54/1.51  sim_fw_subsumption_res:                 1
% 7.54/1.51  sim_bw_subsumption_res:                 1
% 7.54/1.51  sim_tautology_del:                      43
% 7.54/1.51  sim_eq_tautology_del:                   33
% 7.54/1.51  sim_eq_res_simp:                        0
% 7.54/1.51  sim_fw_demodulated:                     0
% 7.54/1.51  sim_bw_demodulated:                     0
% 7.54/1.51  sim_light_normalised:                   39
% 7.54/1.51  sim_joinable_taut:                      0
% 7.54/1.51  sim_joinable_simp:                      0
% 7.54/1.51  sim_ac_normalised:                      0
% 7.54/1.51  sim_smt_subsumption:                    0
% 7.54/1.51  
%------------------------------------------------------------------------------
