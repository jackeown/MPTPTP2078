%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:51 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :  241 (1528 expanded)
%              Number of clauses        :  149 ( 387 expanded)
%              Number of leaves         :   27 ( 347 expanded)
%              Depth                    :   27
%              Number of atoms          :  993 (10780 expanded)
%              Number of equality atoms :  251 ( 597 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
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

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

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
    inference(ennf_transformation,[],[f19])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

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
    inference(nnf_transformation,[],[f49])).

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
     => ( ( ~ v1_zfmisc_1(sK4)
          | ~ v2_tex_2(sK4,X0) )
        & ( v1_zfmisc_1(sK4)
          | v2_tex_2(sK4,X0) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK4) ) ) ),
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

fof(f62,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f59,f61,f60])).

fof(f92,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f62])).

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

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f21])).

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

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK1(X0,X1)) = X1
        & m1_pre_topc(sK1(X0,X1),X0)
        & ~ v2_struct_0(sK1(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK1(X0,X1)) = X1
            & m1_pre_topc(sK1(X0,X1),X0)
            & ~ v2_struct_0(sK1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f54])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f87,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f90,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f91,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f80,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f51,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f50])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f51,f52])).

fof(f64,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

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

fof(f30,plain,(
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

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f93,plain,
    ( v1_zfmisc_1(sK4)
    | v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f16,axiom,(
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

fof(f22,plain,(
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
    inference(pure_predicate_removal,[],[f16])).

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
    inference(ennf_transformation,[],[f22])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f56,plain,(
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

fof(f57,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f45,f56])).

fof(f85,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK2(X0,X1)) = X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f88,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f81,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_tdlat_3(X1)
      | v7_struct_0(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f69,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f71,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f70,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f75,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f89,plain,(
    v2_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK2(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f94,plain,
    ( ~ v1_zfmisc_1(sK4)
    | ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2316,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_16,plain,
    ( m1_pre_topc(sK1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2320,plain,
    ( m1_pre_topc(sK1(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3319,plain,
    ( m1_pre_topc(sK1(sK3,sK4),sK3) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2316,c_2320])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_32,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_35,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_36,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_37,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2639,plain,
    ( m1_pre_topc(sK1(X0,sK4),X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2640,plain,
    ( m1_pre_topc(sK1(X0,sK4),X0) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2639])).

cnf(c_2642,plain,
    ( m1_pre_topc(sK1(sK3,sK4),sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2640])).

cnf(c_3516,plain,
    ( m1_pre_topc(sK1(sK3,sK4),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3319,c_32,c_35,c_36,c_37,c_2642])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2321,plain,
    ( u1_struct_0(sK1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3211,plain,
    ( u1_struct_0(sK1(sK3,sK4)) = sK4
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2316,c_2321])).

cnf(c_2629,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(sK4)
    | u1_struct_0(sK1(X0,sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2631,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(sK4)
    | u1_struct_0(sK1(sK3,sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_2629])).

cnf(c_3367,plain,
    ( u1_struct_0(sK1(sK3,sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3211,c_31,c_28,c_27,c_26,c_2631])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_4,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_425,plain,
    ( m1_subset_1(X0,X1)
    | v1_xboole_0(X2)
    | X1 != X2
    | sK0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_426,plain,
    ( m1_subset_1(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_425])).

cnf(c_2312,plain,
    ( m1_subset_1(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_426])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2324,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4321,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(X0)),u1_struct_0(X1)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2312,c_2324])).

cnf(c_8466,plain,
    ( m1_pre_topc(sK1(sK3,sK4),X0) != iProver_top
    | m1_subset_1(sK0(sK4),u1_struct_0(X0)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1(sK3,sK4)) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3367,c_4321])).

cnf(c_8638,plain,
    ( m1_pre_topc(sK1(sK3,sK4),X0) != iProver_top
    | m1_subset_1(sK0(sK4),u1_struct_0(X0)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1(sK3,sK4)) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8466,c_3367])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK1(X1,X0))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2619,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK1(X0,sK4))
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2620,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1(X0,sK4)) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2619])).

cnf(c_2622,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK1(sK3,sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2620])).

cnf(c_8972,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(sK1(sK3,sK4),X0) != iProver_top
    | m1_subset_1(sK0(sK4),u1_struct_0(X0)) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8638,c_32,c_35,c_36,c_37,c_2622])).

cnf(c_8973,plain,
    ( m1_pre_topc(sK1(sK3,sK4),X0) != iProver_top
    | m1_subset_1(sK0(sK4),u1_struct_0(X0)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8972])).

cnf(c_8982,plain,
    ( m1_subset_1(sK0(sK4),u1_struct_0(sK3)) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3516,c_8973])).

cnf(c_2552,plain,
    ( m1_subset_1(sK0(sK4),sK4)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_426])).

cnf(c_2553,plain,
    ( m1_subset_1(sK0(sK4),sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2552])).

cnf(c_1740,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3024,plain,
    ( sK0(sK4) = sK0(sK4) ),
    inference(instantiation,[status(thm)],[c_1740])).

cnf(c_1744,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2667,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK0(sK4),sK4)
    | X0 != sK0(sK4)
    | X1 != sK4 ),
    inference(instantiation,[status(thm)],[c_1744])).

cnf(c_2859,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1(X1,sK4)))
    | ~ m1_subset_1(sK0(sK4),sK4)
    | X0 != sK0(sK4)
    | u1_struct_0(sK1(X1,sK4)) != sK4 ),
    inference(instantiation,[status(thm)],[c_2667])).

cnf(c_3354,plain,
    ( m1_subset_1(sK0(sK4),u1_struct_0(sK1(X0,sK4)))
    | ~ m1_subset_1(sK0(sK4),sK4)
    | u1_struct_0(sK1(X0,sK4)) != sK4
    | sK0(sK4) != sK0(sK4) ),
    inference(instantiation,[status(thm)],[c_2859])).

cnf(c_3357,plain,
    ( u1_struct_0(sK1(X0,sK4)) != sK4
    | sK0(sK4) != sK0(sK4)
    | m1_subset_1(sK0(sK4),u1_struct_0(sK1(X0,sK4))) = iProver_top
    | m1_subset_1(sK0(sK4),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3354])).

cnf(c_3359,plain,
    ( u1_struct_0(sK1(sK3,sK4)) != sK4
    | sK0(sK4) != sK0(sK4)
    | m1_subset_1(sK0(sK4),u1_struct_0(sK1(sK3,sK4))) = iProver_top
    | m1_subset_1(sK0(sK4),sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3357])).

cnf(c_2779,plain,
    ( ~ m1_pre_topc(sK1(X0,sK4),X0)
    | m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK1(X0,sK4)))
    | v2_struct_0(X0)
    | v2_struct_0(sK1(X0,sK4))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3749,plain,
    ( ~ m1_pre_topc(sK1(X0,sK4),X0)
    | m1_subset_1(sK0(sK4),u1_struct_0(X0))
    | ~ m1_subset_1(sK0(sK4),u1_struct_0(sK1(X0,sK4)))
    | v2_struct_0(X0)
    | v2_struct_0(sK1(X0,sK4))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_2779])).

cnf(c_3750,plain,
    ( m1_pre_topc(sK1(X0,sK4),X0) != iProver_top
    | m1_subset_1(sK0(sK4),u1_struct_0(X0)) = iProver_top
    | m1_subset_1(sK0(sK4),u1_struct_0(sK1(X0,sK4))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1(X0,sK4)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3749])).

cnf(c_3752,plain,
    ( m1_pre_topc(sK1(sK3,sK4),sK3) != iProver_top
    | m1_subset_1(sK0(sK4),u1_struct_0(sK1(sK3,sK4))) != iProver_top
    | m1_subset_1(sK0(sK4),u1_struct_0(sK3)) = iProver_top
    | v2_struct_0(sK1(sK3,sK4)) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3750])).

cnf(c_8985,plain,
    ( m1_subset_1(sK0(sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8982,c_31,c_32,c_28,c_35,c_27,c_36,c_26,c_37,c_2553,c_2622,c_2631,c_2642,c_3024,c_3359,c_3752])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2322,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_8993,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k1_tarski(sK0(sK4))
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8985,c_2322])).

cnf(c_25,negated_conjecture,
    ( v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(sK4) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2317,plain,
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
    inference(cnf_transformation,[],[f85])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_754,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK2(X1,X0)) = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_755,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(X0)
    | u1_struct_0(sK2(sK3,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_754])).

cnf(c_759,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(X0)
    | u1_struct_0(sK2(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_755,c_31,c_28])).

cnf(c_2307,plain,
    ( u1_struct_0(sK2(sK3,X0)) = X0
    | v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_759])).

cnf(c_2995,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | v2_tex_2(sK4,sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2316,c_2307])).

cnf(c_3039,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | u1_struct_0(sK2(sK3,sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2995,c_36])).

cnf(c_3040,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | v2_tex_2(sK4,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3039])).

cnf(c_3045,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2317,c_3040])).

cnf(c_4326,plain,
    ( k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0))
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2312,c_2322])).

cnf(c_2315,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4474,plain,
    ( k6_domain_1(sK4,sK0(sK4)) = k1_tarski(sK0(sK4)) ),
    inference(superposition,[status(thm)],[c_4326,c_2315])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2323,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4511,plain,
    ( m1_subset_1(k1_tarski(sK0(sK4)),k1_zfmisc_1(sK4)) = iProver_top
    | m1_subset_1(sK0(sK4),sK4) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4474,c_2323])).

cnf(c_4798,plain,
    ( m1_subset_1(k1_tarski(sK0(sK4)),k1_zfmisc_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4511,c_36,c_2553])).

cnf(c_5,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_442,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_5,c_18])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_446,plain,
    ( v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_442,c_3])).

cnf(c_447,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | X1 = X0 ),
    inference(renaming,[status(thm)],[c_446])).

cnf(c_2311,plain,
    ( X0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_447])).

cnf(c_4806,plain,
    ( k1_tarski(sK0(sK4)) = sK4
    | v1_zfmisc_1(sK4) != iProver_top
    | v1_xboole_0(k1_tarski(sK0(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4798,c_2311])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2327,plain,
    ( v1_xboole_0(k1_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5561,plain,
    ( k1_tarski(sK0(sK4)) = sK4
    | v1_zfmisc_1(sK4) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4806,c_2327])).

cnf(c_5563,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | k1_tarski(sK0(sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_3045,c_5561])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_6,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_8,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_407,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_6,c_8])).

cnf(c_468,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_13,c_407])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_472,plain,
    ( v1_zfmisc_1(u1_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v1_tdlat_3(X0)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_468,c_7])).

cnf(c_473,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_472])).

cnf(c_12,plain,
    ( ~ v2_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_492,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_473,c_12])).

cnf(c_29,negated_conjecture,
    ( v2_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_513,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_492,c_29])).

cnf(c_514,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_518,plain,
    ( v1_zfmisc_1(u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK3)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_514,c_31,c_28])).

cnf(c_519,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0)) ),
    inference(renaming,[status(thm)],[c_518])).

cnf(c_21,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tdlat_3(sK2(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_706,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tdlat_3(sK2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_30])).

cnf(c_707,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_tdlat_3(sK2(sK3,X0))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_706])).

cnf(c_711,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_tdlat_3(sK2(sK3,X0))
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_707,c_31,c_28])).

cnf(c_801,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_pre_topc(X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(X1)
    | v1_zfmisc_1(u1_struct_0(X1))
    | v1_xboole_0(X0)
    | sK2(sK3,X0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_519,c_711])).

cnf(c_802,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_pre_topc(sK2(sK3,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK2(sK3,X0))
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_801])).

cnf(c_22,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK2(X1,X0))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_682,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK2(X1,X0))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_30])).

cnf(c_683,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_struct_0(sK2(sK3,X0))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_682])).

cnf(c_687,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_struct_0(sK2(sK3,X0))
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_683,c_31,c_28])).

cnf(c_20,plain,
    ( ~ v2_tex_2(X0,X1)
    | m1_pre_topc(sK2(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_730,plain,
    ( ~ v2_tex_2(X0,X1)
    | m1_pre_topc(sK2(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_30])).

cnf(c_731,plain,
    ( ~ v2_tex_2(X0,sK3)
    | m1_pre_topc(sK2(sK3,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_730])).

cnf(c_735,plain,
    ( ~ v2_tex_2(X0,sK3)
    | m1_pre_topc(sK2(sK3,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_731,c_31,c_28])).

cnf(c_806,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_tex_2(X0,sK3)
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_802,c_687,c_735])).

cnf(c_807,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_806])).

cnf(c_2306,plain,
    ( v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0))) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_807])).

cnf(c_2665,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2316,c_2306])).

cnf(c_2984,plain,
    ( v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) = iProver_top
    | v2_tex_2(sK4,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2665,c_36])).

cnf(c_2985,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) = iProver_top ),
    inference(renaming,[status(thm)],[c_2984])).

cnf(c_5623,plain,
    ( k1_tarski(sK0(sK4)) = sK4
    | v2_tex_2(sK4,sK3) != iProver_top
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5563,c_2985])).

cnf(c_38,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5694,plain,
    ( k1_tarski(sK0(sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5623,c_38,c_5561])).

cnf(c_8996,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = sK4
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8993,c_5694])).

cnf(c_2560,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2672,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2560])).

cnf(c_2673,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2672])).

cnf(c_9605,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8996,c_36,c_37,c_2673])).

cnf(c_23,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_664,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_665,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_664])).

cnf(c_669,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_665,c_31,c_28])).

cnf(c_2310,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_669])).

cnf(c_9617,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top
    | m1_subset_1(sK0(sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9605,c_2310])).

cnf(c_1748,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_zfmisc_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2834,plain,
    ( v1_zfmisc_1(X0)
    | ~ v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
    | X0 != u1_struct_0(sK2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1748])).

cnf(c_7190,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
    | v1_zfmisc_1(sK4)
    | sK4 != u1_struct_0(sK2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2834])).

cnf(c_7191,plain,
    ( sK4 != u1_struct_0(sK2(sK3,sK4))
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) != iProver_top
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7190])).

cnf(c_1741,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2675,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_1741])).

cnf(c_2872,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2675])).

cnf(c_3031,plain,
    ( u1_struct_0(sK2(sK3,sK4)) != sK4
    | sK4 = u1_struct_0(sK2(sK3,sK4))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2872])).

cnf(c_2696,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1740])).

cnf(c_24,negated_conjecture,
    ( ~ v2_tex_2(sK4,sK3)
    | ~ v1_zfmisc_1(sK4) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_39,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v1_zfmisc_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9617,c_7191,c_3752,c_3359,c_3031,c_3024,c_2995,c_2696,c_2665,c_2642,c_2631,c_2622,c_2553,c_39,c_37,c_26,c_36,c_27,c_35,c_28,c_32,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:46:23 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 3.40/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.00  
% 3.40/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.40/1.00  
% 3.40/1.00  ------  iProver source info
% 3.40/1.00  
% 3.40/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.40/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.40/1.00  git: non_committed_changes: false
% 3.40/1.00  git: last_make_outside_of_git: false
% 3.40/1.00  
% 3.40/1.00  ------ 
% 3.40/1.00  
% 3.40/1.00  ------ Input Options
% 3.40/1.00  
% 3.40/1.00  --out_options                           all
% 3.40/1.00  --tptp_safe_out                         true
% 3.40/1.00  --problem_path                          ""
% 3.40/1.00  --include_path                          ""
% 3.40/1.00  --clausifier                            res/vclausify_rel
% 3.40/1.00  --clausifier_options                    --mode clausify
% 3.40/1.00  --stdin                                 false
% 3.40/1.00  --stats_out                             all
% 3.40/1.00  
% 3.40/1.00  ------ General Options
% 3.40/1.00  
% 3.40/1.00  --fof                                   false
% 3.40/1.00  --time_out_real                         305.
% 3.40/1.00  --time_out_virtual                      -1.
% 3.40/1.00  --symbol_type_check                     false
% 3.40/1.00  --clausify_out                          false
% 3.40/1.00  --sig_cnt_out                           false
% 3.40/1.00  --trig_cnt_out                          false
% 3.40/1.00  --trig_cnt_out_tolerance                1.
% 3.40/1.00  --trig_cnt_out_sk_spl                   false
% 3.40/1.00  --abstr_cl_out                          false
% 3.40/1.00  
% 3.40/1.00  ------ Global Options
% 3.40/1.00  
% 3.40/1.00  --schedule                              default
% 3.40/1.00  --add_important_lit                     false
% 3.40/1.00  --prop_solver_per_cl                    1000
% 3.40/1.00  --min_unsat_core                        false
% 3.40/1.00  --soft_assumptions                      false
% 3.40/1.00  --soft_lemma_size                       3
% 3.40/1.00  --prop_impl_unit_size                   0
% 3.40/1.00  --prop_impl_unit                        []
% 3.40/1.00  --share_sel_clauses                     true
% 3.40/1.00  --reset_solvers                         false
% 3.40/1.00  --bc_imp_inh                            [conj_cone]
% 3.40/1.00  --conj_cone_tolerance                   3.
% 3.40/1.00  --extra_neg_conj                        none
% 3.40/1.00  --large_theory_mode                     true
% 3.40/1.00  --prolific_symb_bound                   200
% 3.40/1.00  --lt_threshold                          2000
% 3.40/1.00  --clause_weak_htbl                      true
% 3.40/1.00  --gc_record_bc_elim                     false
% 3.40/1.00  
% 3.40/1.00  ------ Preprocessing Options
% 3.40/1.00  
% 3.40/1.00  --preprocessing_flag                    true
% 3.40/1.00  --time_out_prep_mult                    0.1
% 3.40/1.00  --splitting_mode                        input
% 3.40/1.00  --splitting_grd                         true
% 3.40/1.00  --splitting_cvd                         false
% 3.40/1.00  --splitting_cvd_svl                     false
% 3.40/1.00  --splitting_nvd                         32
% 3.40/1.00  --sub_typing                            true
% 3.40/1.00  --prep_gs_sim                           true
% 3.40/1.00  --prep_unflatten                        true
% 3.40/1.00  --prep_res_sim                          true
% 3.40/1.00  --prep_upred                            true
% 3.40/1.00  --prep_sem_filter                       exhaustive
% 3.40/1.00  --prep_sem_filter_out                   false
% 3.40/1.00  --pred_elim                             true
% 3.40/1.00  --res_sim_input                         true
% 3.40/1.00  --eq_ax_congr_red                       true
% 3.40/1.00  --pure_diseq_elim                       true
% 3.40/1.00  --brand_transform                       false
% 3.40/1.00  --non_eq_to_eq                          false
% 3.40/1.00  --prep_def_merge                        true
% 3.40/1.00  --prep_def_merge_prop_impl              false
% 3.40/1.00  --prep_def_merge_mbd                    true
% 3.40/1.00  --prep_def_merge_tr_red                 false
% 3.40/1.00  --prep_def_merge_tr_cl                  false
% 3.40/1.00  --smt_preprocessing                     true
% 3.40/1.00  --smt_ac_axioms                         fast
% 3.40/1.00  --preprocessed_out                      false
% 3.40/1.00  --preprocessed_stats                    false
% 3.40/1.00  
% 3.40/1.00  ------ Abstraction refinement Options
% 3.40/1.00  
% 3.40/1.00  --abstr_ref                             []
% 3.40/1.00  --abstr_ref_prep                        false
% 3.40/1.00  --abstr_ref_until_sat                   false
% 3.40/1.00  --abstr_ref_sig_restrict                funpre
% 3.40/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.40/1.00  --abstr_ref_under                       []
% 3.40/1.00  
% 3.40/1.00  ------ SAT Options
% 3.40/1.00  
% 3.40/1.00  --sat_mode                              false
% 3.40/1.00  --sat_fm_restart_options                ""
% 3.40/1.00  --sat_gr_def                            false
% 3.40/1.00  --sat_epr_types                         true
% 3.40/1.00  --sat_non_cyclic_types                  false
% 3.40/1.00  --sat_finite_models                     false
% 3.40/1.00  --sat_fm_lemmas                         false
% 3.40/1.00  --sat_fm_prep                           false
% 3.40/1.00  --sat_fm_uc_incr                        true
% 3.40/1.00  --sat_out_model                         small
% 3.40/1.00  --sat_out_clauses                       false
% 3.40/1.00  
% 3.40/1.00  ------ QBF Options
% 3.40/1.00  
% 3.40/1.00  --qbf_mode                              false
% 3.40/1.00  --qbf_elim_univ                         false
% 3.40/1.00  --qbf_dom_inst                          none
% 3.40/1.00  --qbf_dom_pre_inst                      false
% 3.40/1.00  --qbf_sk_in                             false
% 3.40/1.00  --qbf_pred_elim                         true
% 3.40/1.00  --qbf_split                             512
% 3.40/1.00  
% 3.40/1.00  ------ BMC1 Options
% 3.40/1.00  
% 3.40/1.00  --bmc1_incremental                      false
% 3.40/1.00  --bmc1_axioms                           reachable_all
% 3.40/1.00  --bmc1_min_bound                        0
% 3.40/1.00  --bmc1_max_bound                        -1
% 3.40/1.00  --bmc1_max_bound_default                -1
% 3.40/1.00  --bmc1_symbol_reachability              true
% 3.40/1.00  --bmc1_property_lemmas                  false
% 3.40/1.00  --bmc1_k_induction                      false
% 3.40/1.00  --bmc1_non_equiv_states                 false
% 3.40/1.00  --bmc1_deadlock                         false
% 3.40/1.00  --bmc1_ucm                              false
% 3.40/1.00  --bmc1_add_unsat_core                   none
% 3.40/1.00  --bmc1_unsat_core_children              false
% 3.40/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.40/1.00  --bmc1_out_stat                         full
% 3.40/1.00  --bmc1_ground_init                      false
% 3.40/1.00  --bmc1_pre_inst_next_state              false
% 3.40/1.00  --bmc1_pre_inst_state                   false
% 3.40/1.00  --bmc1_pre_inst_reach_state             false
% 3.40/1.00  --bmc1_out_unsat_core                   false
% 3.40/1.00  --bmc1_aig_witness_out                  false
% 3.40/1.00  --bmc1_verbose                          false
% 3.40/1.00  --bmc1_dump_clauses_tptp                false
% 3.40/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.40/1.00  --bmc1_dump_file                        -
% 3.40/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.40/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.40/1.00  --bmc1_ucm_extend_mode                  1
% 3.40/1.00  --bmc1_ucm_init_mode                    2
% 3.40/1.00  --bmc1_ucm_cone_mode                    none
% 3.40/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.40/1.00  --bmc1_ucm_relax_model                  4
% 3.40/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.40/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.40/1.00  --bmc1_ucm_layered_model                none
% 3.40/1.00  --bmc1_ucm_max_lemma_size               10
% 3.40/1.00  
% 3.40/1.00  ------ AIG Options
% 3.40/1.00  
% 3.40/1.00  --aig_mode                              false
% 3.40/1.00  
% 3.40/1.00  ------ Instantiation Options
% 3.40/1.00  
% 3.40/1.00  --instantiation_flag                    true
% 3.40/1.00  --inst_sos_flag                         false
% 3.40/1.00  --inst_sos_phase                        true
% 3.40/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.40/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.40/1.00  --inst_lit_sel_side                     num_symb
% 3.40/1.00  --inst_solver_per_active                1400
% 3.40/1.00  --inst_solver_calls_frac                1.
% 3.40/1.00  --inst_passive_queue_type               priority_queues
% 3.40/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.40/1.00  --inst_passive_queues_freq              [25;2]
% 3.40/1.00  --inst_dismatching                      true
% 3.40/1.00  --inst_eager_unprocessed_to_passive     true
% 3.40/1.00  --inst_prop_sim_given                   true
% 3.40/1.00  --inst_prop_sim_new                     false
% 3.40/1.00  --inst_subs_new                         false
% 3.40/1.00  --inst_eq_res_simp                      false
% 3.40/1.00  --inst_subs_given                       false
% 3.40/1.00  --inst_orphan_elimination               true
% 3.40/1.00  --inst_learning_loop_flag               true
% 3.40/1.00  --inst_learning_start                   3000
% 3.40/1.00  --inst_learning_factor                  2
% 3.40/1.00  --inst_start_prop_sim_after_learn       3
% 3.40/1.00  --inst_sel_renew                        solver
% 3.40/1.00  --inst_lit_activity_flag                true
% 3.40/1.00  --inst_restr_to_given                   false
% 3.40/1.00  --inst_activity_threshold               500
% 3.40/1.00  --inst_out_proof                        true
% 3.40/1.00  
% 3.40/1.00  ------ Resolution Options
% 3.40/1.00  
% 3.40/1.00  --resolution_flag                       true
% 3.40/1.00  --res_lit_sel                           adaptive
% 3.40/1.00  --res_lit_sel_side                      none
% 3.40/1.00  --res_ordering                          kbo
% 3.40/1.00  --res_to_prop_solver                    active
% 3.40/1.00  --res_prop_simpl_new                    false
% 3.40/1.00  --res_prop_simpl_given                  true
% 3.40/1.00  --res_passive_queue_type                priority_queues
% 3.40/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.40/1.00  --res_passive_queues_freq               [15;5]
% 3.40/1.00  --res_forward_subs                      full
% 3.40/1.00  --res_backward_subs                     full
% 3.40/1.00  --res_forward_subs_resolution           true
% 3.40/1.00  --res_backward_subs_resolution          true
% 3.40/1.00  --res_orphan_elimination                true
% 3.40/1.00  --res_time_limit                        2.
% 3.40/1.00  --res_out_proof                         true
% 3.40/1.00  
% 3.40/1.00  ------ Superposition Options
% 3.40/1.00  
% 3.40/1.00  --superposition_flag                    true
% 3.40/1.00  --sup_passive_queue_type                priority_queues
% 3.40/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.40/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.40/1.00  --demod_completeness_check              fast
% 3.40/1.00  --demod_use_ground                      true
% 3.40/1.00  --sup_to_prop_solver                    passive
% 3.40/1.00  --sup_prop_simpl_new                    true
% 3.40/1.00  --sup_prop_simpl_given                  true
% 3.40/1.00  --sup_fun_splitting                     false
% 3.40/1.00  --sup_smt_interval                      50000
% 3.40/1.00  
% 3.40/1.00  ------ Superposition Simplification Setup
% 3.40/1.00  
% 3.40/1.00  --sup_indices_passive                   []
% 3.40/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.40/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/1.00  --sup_full_bw                           [BwDemod]
% 3.40/1.00  --sup_immed_triv                        [TrivRules]
% 3.40/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.40/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/1.00  --sup_immed_bw_main                     []
% 3.40/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.40/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.40/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.40/1.00  
% 3.40/1.00  ------ Combination Options
% 3.40/1.00  
% 3.40/1.00  --comb_res_mult                         3
% 3.40/1.00  --comb_sup_mult                         2
% 3.40/1.00  --comb_inst_mult                        10
% 3.40/1.00  
% 3.40/1.00  ------ Debug Options
% 3.40/1.00  
% 3.40/1.00  --dbg_backtrace                         false
% 3.40/1.00  --dbg_dump_prop_clauses                 false
% 3.40/1.00  --dbg_dump_prop_clauses_file            -
% 3.40/1.00  --dbg_out_stat                          false
% 3.40/1.00  ------ Parsing...
% 3.40/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.40/1.00  
% 3.40/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.40/1.00  
% 3.40/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.40/1.00  
% 3.40/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.40/1.00  ------ Proving...
% 3.40/1.00  ------ Problem Properties 
% 3.40/1.00  
% 3.40/1.00  
% 3.40/1.00  clauses                                 22
% 3.40/1.00  conjectures                             6
% 3.40/1.00  EPR                                     6
% 3.40/1.00  Horn                                    10
% 3.40/1.00  unary                                   5
% 3.40/1.00  binary                                  4
% 3.40/1.00  lits                                    66
% 3.40/1.00  lits eq                                 4
% 3.40/1.00  fd_pure                                 0
% 3.40/1.00  fd_pseudo                               0
% 3.40/1.00  fd_cond                                 0
% 3.40/1.00  fd_pseudo_cond                          1
% 3.40/1.00  AC symbols                              0
% 3.40/1.00  
% 3.40/1.00  ------ Schedule dynamic 5 is on 
% 3.40/1.00  
% 3.40/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.40/1.00  
% 3.40/1.00  
% 3.40/1.00  ------ 
% 3.40/1.00  Current options:
% 3.40/1.00  ------ 
% 3.40/1.00  
% 3.40/1.00  ------ Input Options
% 3.40/1.00  
% 3.40/1.00  --out_options                           all
% 3.40/1.00  --tptp_safe_out                         true
% 3.40/1.00  --problem_path                          ""
% 3.40/1.00  --include_path                          ""
% 3.40/1.00  --clausifier                            res/vclausify_rel
% 3.40/1.00  --clausifier_options                    --mode clausify
% 3.40/1.00  --stdin                                 false
% 3.40/1.00  --stats_out                             all
% 3.40/1.00  
% 3.40/1.00  ------ General Options
% 3.40/1.00  
% 3.40/1.00  --fof                                   false
% 3.40/1.00  --time_out_real                         305.
% 3.40/1.00  --time_out_virtual                      -1.
% 3.40/1.00  --symbol_type_check                     false
% 3.40/1.00  --clausify_out                          false
% 3.40/1.00  --sig_cnt_out                           false
% 3.40/1.00  --trig_cnt_out                          false
% 3.40/1.00  --trig_cnt_out_tolerance                1.
% 3.40/1.00  --trig_cnt_out_sk_spl                   false
% 3.40/1.00  --abstr_cl_out                          false
% 3.40/1.00  
% 3.40/1.00  ------ Global Options
% 3.40/1.00  
% 3.40/1.00  --schedule                              default
% 3.40/1.00  --add_important_lit                     false
% 3.40/1.00  --prop_solver_per_cl                    1000
% 3.40/1.00  --min_unsat_core                        false
% 3.40/1.00  --soft_assumptions                      false
% 3.40/1.00  --soft_lemma_size                       3
% 3.40/1.00  --prop_impl_unit_size                   0
% 3.40/1.00  --prop_impl_unit                        []
% 3.40/1.00  --share_sel_clauses                     true
% 3.40/1.00  --reset_solvers                         false
% 3.40/1.00  --bc_imp_inh                            [conj_cone]
% 3.40/1.00  --conj_cone_tolerance                   3.
% 3.40/1.00  --extra_neg_conj                        none
% 3.40/1.00  --large_theory_mode                     true
% 3.40/1.00  --prolific_symb_bound                   200
% 3.40/1.00  --lt_threshold                          2000
% 3.40/1.00  --clause_weak_htbl                      true
% 3.40/1.00  --gc_record_bc_elim                     false
% 3.40/1.00  
% 3.40/1.00  ------ Preprocessing Options
% 3.40/1.00  
% 3.40/1.00  --preprocessing_flag                    true
% 3.40/1.00  --time_out_prep_mult                    0.1
% 3.40/1.00  --splitting_mode                        input
% 3.40/1.00  --splitting_grd                         true
% 3.40/1.00  --splitting_cvd                         false
% 3.40/1.00  --splitting_cvd_svl                     false
% 3.40/1.00  --splitting_nvd                         32
% 3.40/1.00  --sub_typing                            true
% 3.40/1.00  --prep_gs_sim                           true
% 3.40/1.00  --prep_unflatten                        true
% 3.40/1.00  --prep_res_sim                          true
% 3.40/1.00  --prep_upred                            true
% 3.40/1.00  --prep_sem_filter                       exhaustive
% 3.40/1.00  --prep_sem_filter_out                   false
% 3.40/1.00  --pred_elim                             true
% 3.40/1.00  --res_sim_input                         true
% 3.40/1.00  --eq_ax_congr_red                       true
% 3.40/1.00  --pure_diseq_elim                       true
% 3.40/1.00  --brand_transform                       false
% 3.40/1.00  --non_eq_to_eq                          false
% 3.40/1.00  --prep_def_merge                        true
% 3.40/1.00  --prep_def_merge_prop_impl              false
% 3.40/1.00  --prep_def_merge_mbd                    true
% 3.40/1.00  --prep_def_merge_tr_red                 false
% 3.40/1.00  --prep_def_merge_tr_cl                  false
% 3.40/1.00  --smt_preprocessing                     true
% 3.40/1.00  --smt_ac_axioms                         fast
% 3.40/1.00  --preprocessed_out                      false
% 3.40/1.00  --preprocessed_stats                    false
% 3.40/1.00  
% 3.40/1.00  ------ Abstraction refinement Options
% 3.40/1.00  
% 3.40/1.00  --abstr_ref                             []
% 3.40/1.00  --abstr_ref_prep                        false
% 3.40/1.00  --abstr_ref_until_sat                   false
% 3.40/1.00  --abstr_ref_sig_restrict                funpre
% 3.40/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.40/1.00  --abstr_ref_under                       []
% 3.40/1.00  
% 3.40/1.00  ------ SAT Options
% 3.40/1.00  
% 3.40/1.00  --sat_mode                              false
% 3.40/1.00  --sat_fm_restart_options                ""
% 3.40/1.00  --sat_gr_def                            false
% 3.40/1.00  --sat_epr_types                         true
% 3.40/1.00  --sat_non_cyclic_types                  false
% 3.40/1.00  --sat_finite_models                     false
% 3.40/1.00  --sat_fm_lemmas                         false
% 3.40/1.00  --sat_fm_prep                           false
% 3.40/1.00  --sat_fm_uc_incr                        true
% 3.40/1.00  --sat_out_model                         small
% 3.40/1.00  --sat_out_clauses                       false
% 3.40/1.00  
% 3.40/1.00  ------ QBF Options
% 3.40/1.00  
% 3.40/1.00  --qbf_mode                              false
% 3.40/1.00  --qbf_elim_univ                         false
% 3.40/1.00  --qbf_dom_inst                          none
% 3.40/1.00  --qbf_dom_pre_inst                      false
% 3.40/1.00  --qbf_sk_in                             false
% 3.40/1.00  --qbf_pred_elim                         true
% 3.40/1.00  --qbf_split                             512
% 3.40/1.00  
% 3.40/1.00  ------ BMC1 Options
% 3.40/1.00  
% 3.40/1.00  --bmc1_incremental                      false
% 3.40/1.00  --bmc1_axioms                           reachable_all
% 3.40/1.00  --bmc1_min_bound                        0
% 3.40/1.00  --bmc1_max_bound                        -1
% 3.40/1.00  --bmc1_max_bound_default                -1
% 3.40/1.00  --bmc1_symbol_reachability              true
% 3.40/1.00  --bmc1_property_lemmas                  false
% 3.40/1.00  --bmc1_k_induction                      false
% 3.40/1.00  --bmc1_non_equiv_states                 false
% 3.40/1.00  --bmc1_deadlock                         false
% 3.40/1.00  --bmc1_ucm                              false
% 3.40/1.00  --bmc1_add_unsat_core                   none
% 3.40/1.00  --bmc1_unsat_core_children              false
% 3.40/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.40/1.00  --bmc1_out_stat                         full
% 3.40/1.00  --bmc1_ground_init                      false
% 3.40/1.00  --bmc1_pre_inst_next_state              false
% 3.40/1.00  --bmc1_pre_inst_state                   false
% 3.40/1.00  --bmc1_pre_inst_reach_state             false
% 3.40/1.00  --bmc1_out_unsat_core                   false
% 3.40/1.00  --bmc1_aig_witness_out                  false
% 3.40/1.00  --bmc1_verbose                          false
% 3.40/1.00  --bmc1_dump_clauses_tptp                false
% 3.40/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.40/1.00  --bmc1_dump_file                        -
% 3.40/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.40/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.40/1.00  --bmc1_ucm_extend_mode                  1
% 3.40/1.00  --bmc1_ucm_init_mode                    2
% 3.40/1.00  --bmc1_ucm_cone_mode                    none
% 3.40/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.40/1.00  --bmc1_ucm_relax_model                  4
% 3.40/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.40/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.40/1.00  --bmc1_ucm_layered_model                none
% 3.40/1.00  --bmc1_ucm_max_lemma_size               10
% 3.40/1.00  
% 3.40/1.00  ------ AIG Options
% 3.40/1.00  
% 3.40/1.00  --aig_mode                              false
% 3.40/1.00  
% 3.40/1.00  ------ Instantiation Options
% 3.40/1.00  
% 3.40/1.00  --instantiation_flag                    true
% 3.40/1.00  --inst_sos_flag                         false
% 3.40/1.00  --inst_sos_phase                        true
% 3.40/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.40/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.40/1.00  --inst_lit_sel_side                     none
% 3.40/1.00  --inst_solver_per_active                1400
% 3.40/1.00  --inst_solver_calls_frac                1.
% 3.40/1.00  --inst_passive_queue_type               priority_queues
% 3.40/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.40/1.00  --inst_passive_queues_freq              [25;2]
% 3.40/1.00  --inst_dismatching                      true
% 3.40/1.00  --inst_eager_unprocessed_to_passive     true
% 3.40/1.00  --inst_prop_sim_given                   true
% 3.40/1.00  --inst_prop_sim_new                     false
% 3.40/1.00  --inst_subs_new                         false
% 3.40/1.00  --inst_eq_res_simp                      false
% 3.40/1.00  --inst_subs_given                       false
% 3.40/1.00  --inst_orphan_elimination               true
% 3.40/1.00  --inst_learning_loop_flag               true
% 3.40/1.00  --inst_learning_start                   3000
% 3.40/1.00  --inst_learning_factor                  2
% 3.40/1.00  --inst_start_prop_sim_after_learn       3
% 3.40/1.00  --inst_sel_renew                        solver
% 3.40/1.00  --inst_lit_activity_flag                true
% 3.40/1.00  --inst_restr_to_given                   false
% 3.40/1.00  --inst_activity_threshold               500
% 3.40/1.00  --inst_out_proof                        true
% 3.40/1.00  
% 3.40/1.00  ------ Resolution Options
% 3.40/1.00  
% 3.40/1.00  --resolution_flag                       false
% 3.40/1.00  --res_lit_sel                           adaptive
% 3.40/1.00  --res_lit_sel_side                      none
% 3.40/1.00  --res_ordering                          kbo
% 3.40/1.00  --res_to_prop_solver                    active
% 3.40/1.00  --res_prop_simpl_new                    false
% 3.40/1.00  --res_prop_simpl_given                  true
% 3.40/1.00  --res_passive_queue_type                priority_queues
% 3.40/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.40/1.00  --res_passive_queues_freq               [15;5]
% 3.40/1.00  --res_forward_subs                      full
% 3.40/1.00  --res_backward_subs                     full
% 3.40/1.00  --res_forward_subs_resolution           true
% 3.40/1.00  --res_backward_subs_resolution          true
% 3.40/1.00  --res_orphan_elimination                true
% 3.40/1.00  --res_time_limit                        2.
% 3.40/1.00  --res_out_proof                         true
% 3.40/1.00  
% 3.40/1.00  ------ Superposition Options
% 3.40/1.00  
% 3.40/1.00  --superposition_flag                    true
% 3.40/1.00  --sup_passive_queue_type                priority_queues
% 3.40/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.40/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.40/1.00  --demod_completeness_check              fast
% 3.40/1.00  --demod_use_ground                      true
% 3.40/1.00  --sup_to_prop_solver                    passive
% 3.40/1.00  --sup_prop_simpl_new                    true
% 3.40/1.00  --sup_prop_simpl_given                  true
% 3.40/1.00  --sup_fun_splitting                     false
% 3.40/1.00  --sup_smt_interval                      50000
% 3.40/1.00  
% 3.40/1.00  ------ Superposition Simplification Setup
% 3.40/1.00  
% 3.40/1.00  --sup_indices_passive                   []
% 3.40/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.40/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/1.00  --sup_full_bw                           [BwDemod]
% 3.40/1.00  --sup_immed_triv                        [TrivRules]
% 3.40/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.40/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/1.00  --sup_immed_bw_main                     []
% 3.40/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.40/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.40/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.40/1.00  
% 3.40/1.00  ------ Combination Options
% 3.40/1.00  
% 3.40/1.00  --comb_res_mult                         3
% 3.40/1.00  --comb_sup_mult                         2
% 3.40/1.00  --comb_inst_mult                        10
% 3.40/1.00  
% 3.40/1.00  ------ Debug Options
% 3.40/1.00  
% 3.40/1.00  --dbg_backtrace                         false
% 3.40/1.00  --dbg_dump_prop_clauses                 false
% 3.40/1.00  --dbg_dump_prop_clauses_file            -
% 3.40/1.00  --dbg_out_stat                          false
% 3.40/1.00  
% 3.40/1.00  
% 3.40/1.00  
% 3.40/1.00  
% 3.40/1.00  ------ Proving...
% 3.40/1.00  
% 3.40/1.00  
% 3.40/1.00  % SZS status Theorem for theBenchmark.p
% 3.40/1.00  
% 3.40/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.40/1.00  
% 3.40/1.00  fof(f18,conjecture,(
% 3.40/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f19,negated_conjecture,(
% 3.40/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 3.40/1.00    inference(negated_conjecture,[],[f18])).
% 3.40/1.00  
% 3.40/1.00  fof(f48,plain,(
% 3.40/1.00    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.40/1.00    inference(ennf_transformation,[],[f19])).
% 3.40/1.00  
% 3.40/1.00  fof(f49,plain,(
% 3.40/1.00    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.40/1.00    inference(flattening,[],[f48])).
% 3.40/1.00  
% 3.40/1.00  fof(f58,plain,(
% 3.40/1.00    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.40/1.00    inference(nnf_transformation,[],[f49])).
% 3.40/1.00  
% 3.40/1.00  fof(f59,plain,(
% 3.40/1.00    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.40/1.00    inference(flattening,[],[f58])).
% 3.40/1.00  
% 3.40/1.00  fof(f61,plain,(
% 3.40/1.00    ( ! [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,X0)) & (v1_zfmisc_1(sK4) | v2_tex_2(sK4,X0)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK4))) )),
% 3.40/1.00    introduced(choice_axiom,[])).
% 3.40/1.00  
% 3.40/1.00  fof(f60,plain,(
% 3.40/1.00    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK3)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 3.40/1.00    introduced(choice_axiom,[])).
% 3.40/1.00  
% 3.40/1.00  fof(f62,plain,(
% 3.40/1.00    ((~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3)) & (v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 3.40/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f59,f61,f60])).
% 3.40/1.00  
% 3.40/1.00  fof(f92,plain,(
% 3.40/1.00    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 3.40/1.00    inference(cnf_transformation,[],[f62])).
% 3.40/1.00  
% 3.40/1.00  fof(f14,axiom,(
% 3.40/1.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f21,plain,(
% 3.40/1.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2))))),
% 3.40/1.00    inference(pure_predicate_removal,[],[f14])).
% 3.40/1.00  
% 3.40/1.00  fof(f40,plain,(
% 3.40/1.00    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.40/1.00    inference(ennf_transformation,[],[f21])).
% 3.40/1.00  
% 3.40/1.00  fof(f41,plain,(
% 3.40/1.00    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.40/1.00    inference(flattening,[],[f40])).
% 3.40/1.00  
% 3.40/1.00  fof(f54,plain,(
% 3.40/1.00    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(sK1(X0,X1)) = X1 & m1_pre_topc(sK1(X0,X1),X0) & ~v2_struct_0(sK1(X0,X1))))),
% 3.40/1.00    introduced(choice_axiom,[])).
% 3.40/1.00  
% 3.40/1.00  fof(f55,plain,(
% 3.40/1.00    ! [X0] : (! [X1] : ((u1_struct_0(sK1(X0,X1)) = X1 & m1_pre_topc(sK1(X0,X1),X0) & ~v2_struct_0(sK1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.40/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f54])).
% 3.40/1.00  
% 3.40/1.00  fof(f79,plain,(
% 3.40/1.00    ( ! [X0,X1] : (m1_pre_topc(sK1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f55])).
% 3.40/1.00  
% 3.40/1.00  fof(f87,plain,(
% 3.40/1.00    ~v2_struct_0(sK3)),
% 3.40/1.00    inference(cnf_transformation,[],[f62])).
% 3.40/1.00  
% 3.40/1.00  fof(f90,plain,(
% 3.40/1.00    l1_pre_topc(sK3)),
% 3.40/1.00    inference(cnf_transformation,[],[f62])).
% 3.40/1.00  
% 3.40/1.00  fof(f91,plain,(
% 3.40/1.00    ~v1_xboole_0(sK4)),
% 3.40/1.00    inference(cnf_transformation,[],[f62])).
% 3.40/1.00  
% 3.40/1.00  fof(f80,plain,(
% 3.40/1.00    ( ! [X0,X1] : (u1_struct_0(sK1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f55])).
% 3.40/1.00  
% 3.40/1.00  fof(f1,axiom,(
% 3.40/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f50,plain,(
% 3.40/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.40/1.00    inference(nnf_transformation,[],[f1])).
% 3.40/1.00  
% 3.40/1.00  fof(f51,plain,(
% 3.40/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.40/1.00    inference(rectify,[],[f50])).
% 3.40/1.00  
% 3.40/1.00  fof(f52,plain,(
% 3.40/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.40/1.00    introduced(choice_axiom,[])).
% 3.40/1.00  
% 3.40/1.00  fof(f53,plain,(
% 3.40/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.40/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f51,f52])).
% 3.40/1.00  
% 3.40/1.00  fof(f64,plain,(
% 3.40/1.00    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f53])).
% 3.40/1.00  
% 3.40/1.00  fof(f4,axiom,(
% 3.40/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f24,plain,(
% 3.40/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.40/1.00    inference(ennf_transformation,[],[f4])).
% 3.40/1.00  
% 3.40/1.00  fof(f67,plain,(
% 3.40/1.00    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f24])).
% 3.40/1.00  
% 3.40/1.00  fof(f9,axiom,(
% 3.40/1.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f30,plain,(
% 3.40/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.40/1.00    inference(ennf_transformation,[],[f9])).
% 3.40/1.00  
% 3.40/1.00  fof(f31,plain,(
% 3.40/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.40/1.00    inference(flattening,[],[f30])).
% 3.40/1.00  
% 3.40/1.00  fof(f72,plain,(
% 3.40/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f31])).
% 3.40/1.00  
% 3.40/1.00  fof(f78,plain,(
% 3.40/1.00    ( ! [X0,X1] : (~v2_struct_0(sK1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f55])).
% 3.40/1.00  
% 3.40/1.00  fof(f11,axiom,(
% 3.40/1.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f34,plain,(
% 3.40/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.40/1.00    inference(ennf_transformation,[],[f11])).
% 3.40/1.00  
% 3.40/1.00  fof(f35,plain,(
% 3.40/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.40/1.00    inference(flattening,[],[f34])).
% 3.40/1.00  
% 3.40/1.00  fof(f74,plain,(
% 3.40/1.00    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f35])).
% 3.40/1.00  
% 3.40/1.00  fof(f93,plain,(
% 3.40/1.00    v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3)),
% 3.40/1.00    inference(cnf_transformation,[],[f62])).
% 3.40/1.00  
% 3.40/1.00  fof(f16,axiom,(
% 3.40/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f22,plain,(
% 3.40/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 3.40/1.00    inference(pure_predicate_removal,[],[f16])).
% 3.40/1.00  
% 3.40/1.00  fof(f44,plain,(
% 3.40/1.00    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.40/1.00    inference(ennf_transformation,[],[f22])).
% 3.40/1.00  
% 3.40/1.00  fof(f45,plain,(
% 3.40/1.00    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.40/1.00    inference(flattening,[],[f44])).
% 3.40/1.00  
% 3.40/1.00  fof(f56,plain,(
% 3.40/1.00    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_tdlat_3(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))))),
% 3.40/1.00    introduced(choice_axiom,[])).
% 3.40/1.00  
% 3.40/1.00  fof(f57,plain,(
% 3.40/1.00    ! [X0] : (! [X1] : ((u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_tdlat_3(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.40/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f45,f56])).
% 3.40/1.00  
% 3.40/1.00  fof(f85,plain,(
% 3.40/1.00    ( ! [X0,X1] : (u1_struct_0(sK2(X0,X1)) = X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f57])).
% 3.40/1.00  
% 3.40/1.00  fof(f88,plain,(
% 3.40/1.00    v2_pre_topc(sK3)),
% 3.40/1.00    inference(cnf_transformation,[],[f62])).
% 3.40/1.00  
% 3.40/1.00  fof(f10,axiom,(
% 3.40/1.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f32,plain,(
% 3.40/1.00    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.40/1.00    inference(ennf_transformation,[],[f10])).
% 3.40/1.00  
% 3.40/1.00  fof(f33,plain,(
% 3.40/1.00    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.40/1.00    inference(flattening,[],[f32])).
% 3.40/1.00  
% 3.40/1.00  fof(f73,plain,(
% 3.40/1.00    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f33])).
% 3.40/1.00  
% 3.40/1.00  fof(f5,axiom,(
% 3.40/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f20,plain,(
% 3.40/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 3.40/1.00    inference(unused_predicate_definition_removal,[],[f5])).
% 3.40/1.00  
% 3.40/1.00  fof(f25,plain,(
% 3.40/1.00    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 3.40/1.00    inference(ennf_transformation,[],[f20])).
% 3.40/1.00  
% 3.40/1.00  fof(f68,plain,(
% 3.40/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.40/1.00    inference(cnf_transformation,[],[f25])).
% 3.40/1.00  
% 3.40/1.00  fof(f15,axiom,(
% 3.40/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f42,plain,(
% 3.40/1.00    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 3.40/1.00    inference(ennf_transformation,[],[f15])).
% 3.40/1.00  
% 3.40/1.00  fof(f43,plain,(
% 3.40/1.00    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.40/1.00    inference(flattening,[],[f42])).
% 3.40/1.00  
% 3.40/1.00  fof(f81,plain,(
% 3.40/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f43])).
% 3.40/1.00  
% 3.40/1.00  fof(f3,axiom,(
% 3.40/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f23,plain,(
% 3.40/1.00    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.40/1.00    inference(ennf_transformation,[],[f3])).
% 3.40/1.00  
% 3.40/1.00  fof(f66,plain,(
% 3.40/1.00    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f23])).
% 3.40/1.00  
% 3.40/1.00  fof(f2,axiom,(
% 3.40/1.00    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f65,plain,(
% 3.40/1.00    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 3.40/1.00    inference(cnf_transformation,[],[f2])).
% 3.40/1.00  
% 3.40/1.00  fof(f13,axiom,(
% 3.40/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((~v7_struct_0(X1) & ~v2_struct_0(X1)) => (~v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f38,plain,(
% 3.40/1.00    ! [X0] : (! [X1] : (((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (v7_struct_0(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.40/1.00    inference(ennf_transformation,[],[f13])).
% 3.40/1.00  
% 3.40/1.00  fof(f39,plain,(
% 3.40/1.00    ! [X0] : (! [X1] : ((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.40/1.00    inference(flattening,[],[f38])).
% 3.40/1.00  
% 3.40/1.00  fof(f77,plain,(
% 3.40/1.00    ( ! [X0,X1] : (~v1_tdlat_3(X1) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f39])).
% 3.40/1.00  
% 3.40/1.00  fof(f6,axiom,(
% 3.40/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f26,plain,(
% 3.40/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.40/1.00    inference(ennf_transformation,[],[f6])).
% 3.40/1.00  
% 3.40/1.00  fof(f69,plain,(
% 3.40/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f26])).
% 3.40/1.00  
% 3.40/1.00  fof(f8,axiom,(
% 3.40/1.00    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f28,plain,(
% 3.40/1.00    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 3.40/1.00    inference(ennf_transformation,[],[f8])).
% 3.40/1.00  
% 3.40/1.00  fof(f29,plain,(
% 3.40/1.00    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 3.40/1.00    inference(flattening,[],[f28])).
% 3.40/1.00  
% 3.40/1.00  fof(f71,plain,(
% 3.40/1.00    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f29])).
% 3.40/1.00  
% 3.40/1.00  fof(f7,axiom,(
% 3.40/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f27,plain,(
% 3.40/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.40/1.00    inference(ennf_transformation,[],[f7])).
% 3.40/1.00  
% 3.40/1.00  fof(f70,plain,(
% 3.40/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f27])).
% 3.40/1.00  
% 3.40/1.00  fof(f12,axiom,(
% 3.40/1.00    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f36,plain,(
% 3.40/1.00    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 3.40/1.00    inference(ennf_transformation,[],[f12])).
% 3.40/1.00  
% 3.40/1.00  fof(f37,plain,(
% 3.40/1.00    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 3.40/1.00    inference(flattening,[],[f36])).
% 3.40/1.00  
% 3.40/1.00  fof(f75,plain,(
% 3.40/1.00    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f37])).
% 3.40/1.00  
% 3.40/1.00  fof(f89,plain,(
% 3.40/1.00    v2_tdlat_3(sK3)),
% 3.40/1.00    inference(cnf_transformation,[],[f62])).
% 3.40/1.00  
% 3.40/1.00  fof(f83,plain,(
% 3.40/1.00    ( ! [X0,X1] : (v1_tdlat_3(sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f57])).
% 3.40/1.00  
% 3.40/1.00  fof(f82,plain,(
% 3.40/1.00    ( ! [X0,X1] : (~v2_struct_0(sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f57])).
% 3.40/1.00  
% 3.40/1.00  fof(f84,plain,(
% 3.40/1.00    ( ! [X0,X1] : (m1_pre_topc(sK2(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f57])).
% 3.40/1.00  
% 3.40/1.00  fof(f17,axiom,(
% 3.40/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 3.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/1.00  
% 3.40/1.00  fof(f46,plain,(
% 3.40/1.00    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.40/1.00    inference(ennf_transformation,[],[f17])).
% 3.40/1.00  
% 3.40/1.00  fof(f47,plain,(
% 3.40/1.00    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.40/1.00    inference(flattening,[],[f46])).
% 3.40/1.00  
% 3.40/1.00  fof(f86,plain,(
% 3.40/1.00    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.40/1.00    inference(cnf_transformation,[],[f47])).
% 3.40/1.00  
% 3.40/1.00  fof(f94,plain,(
% 3.40/1.00    ~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3)),
% 3.40/1.00    inference(cnf_transformation,[],[f62])).
% 3.40/1.00  
% 3.40/1.00  cnf(c_26,negated_conjecture,
% 3.40/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.40/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2316,plain,
% 3.40/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.40/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_16,plain,
% 3.40/1.00      ( m1_pre_topc(sK1(X0,X1),X0)
% 3.40/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.40/1.00      | v2_struct_0(X0)
% 3.40/1.00      | ~ l1_pre_topc(X0)
% 3.40/1.00      | v1_xboole_0(X1) ),
% 3.40/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2320,plain,
% 3.40/1.00      ( m1_pre_topc(sK1(X0,X1),X0) = iProver_top
% 3.40/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.40/1.00      | v2_struct_0(X0) = iProver_top
% 3.40/1.00      | l1_pre_topc(X0) != iProver_top
% 3.40/1.00      | v1_xboole_0(X1) = iProver_top ),
% 3.40/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_3319,plain,
% 3.40/1.00      ( m1_pre_topc(sK1(sK3,sK4),sK3) = iProver_top
% 3.40/1.00      | v2_struct_0(sK3) = iProver_top
% 3.40/1.00      | l1_pre_topc(sK3) != iProver_top
% 3.40/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.40/1.00      inference(superposition,[status(thm)],[c_2316,c_2320]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_31,negated_conjecture,
% 3.40/1.00      ( ~ v2_struct_0(sK3) ),
% 3.40/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_32,plain,
% 3.40/1.00      ( v2_struct_0(sK3) != iProver_top ),
% 3.40/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_28,negated_conjecture,
% 3.40/1.00      ( l1_pre_topc(sK3) ),
% 3.40/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_35,plain,
% 3.40/1.00      ( l1_pre_topc(sK3) = iProver_top ),
% 3.40/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_27,negated_conjecture,
% 3.40/1.00      ( ~ v1_xboole_0(sK4) ),
% 3.40/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_36,plain,
% 3.40/1.00      ( v1_xboole_0(sK4) != iProver_top ),
% 3.40/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_37,plain,
% 3.40/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.40/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2639,plain,
% 3.40/1.00      ( m1_pre_topc(sK1(X0,sK4),X0)
% 3.40/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
% 3.40/1.00      | v2_struct_0(X0)
% 3.40/1.00      | ~ l1_pre_topc(X0)
% 3.40/1.00      | v1_xboole_0(sK4) ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2640,plain,
% 3.40/1.00      ( m1_pre_topc(sK1(X0,sK4),X0) = iProver_top
% 3.40/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.40/1.00      | v2_struct_0(X0) = iProver_top
% 3.40/1.00      | l1_pre_topc(X0) != iProver_top
% 3.40/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.40/1.00      inference(predicate_to_equality,[status(thm)],[c_2639]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2642,plain,
% 3.40/1.00      ( m1_pre_topc(sK1(sK3,sK4),sK3) = iProver_top
% 3.40/1.00      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.40/1.00      | v2_struct_0(sK3) = iProver_top
% 3.40/1.00      | l1_pre_topc(sK3) != iProver_top
% 3.40/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_2640]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_3516,plain,
% 3.40/1.00      ( m1_pre_topc(sK1(sK3,sK4),sK3) = iProver_top ),
% 3.40/1.00      inference(global_propositional_subsumption,
% 3.40/1.00                [status(thm)],
% 3.40/1.00                [c_3319,c_32,c_35,c_36,c_37,c_2642]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_15,plain,
% 3.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.40/1.00      | v2_struct_0(X1)
% 3.40/1.00      | ~ l1_pre_topc(X1)
% 3.40/1.00      | v1_xboole_0(X0)
% 3.40/1.00      | u1_struct_0(sK1(X1,X0)) = X0 ),
% 3.40/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2321,plain,
% 3.40/1.00      ( u1_struct_0(sK1(X0,X1)) = X1
% 3.40/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.40/1.00      | v2_struct_0(X0) = iProver_top
% 3.40/1.00      | l1_pre_topc(X0) != iProver_top
% 3.40/1.00      | v1_xboole_0(X1) = iProver_top ),
% 3.40/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_3211,plain,
% 3.40/1.00      ( u1_struct_0(sK1(sK3,sK4)) = sK4
% 3.40/1.00      | v2_struct_0(sK3) = iProver_top
% 3.40/1.00      | l1_pre_topc(sK3) != iProver_top
% 3.40/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.40/1.00      inference(superposition,[status(thm)],[c_2316,c_2321]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2629,plain,
% 3.40/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
% 3.40/1.00      | v2_struct_0(X0)
% 3.40/1.00      | ~ l1_pre_topc(X0)
% 3.40/1.00      | v1_xboole_0(sK4)
% 3.40/1.00      | u1_struct_0(sK1(X0,sK4)) = sK4 ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2631,plain,
% 3.40/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.40/1.00      | v2_struct_0(sK3)
% 3.40/1.00      | ~ l1_pre_topc(sK3)
% 3.40/1.00      | v1_xboole_0(sK4)
% 3.40/1.00      | u1_struct_0(sK1(sK3,sK4)) = sK4 ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_2629]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_3367,plain,
% 3.40/1.00      ( u1_struct_0(sK1(sK3,sK4)) = sK4 ),
% 3.40/1.00      inference(global_propositional_subsumption,
% 3.40/1.00                [status(thm)],
% 3.40/1.00                [c_3211,c_31,c_28,c_27,c_26,c_2631]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_0,plain,
% 3.40/1.00      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.40/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_4,plain,
% 3.40/1.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.40/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_425,plain,
% 3.40/1.00      ( m1_subset_1(X0,X1) | v1_xboole_0(X2) | X1 != X2 | sK0(X2) != X0 ),
% 3.40/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_4]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_426,plain,
% 3.40/1.00      ( m1_subset_1(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.40/1.00      inference(unflattening,[status(thm)],[c_425]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2312,plain,
% 3.40/1.00      ( m1_subset_1(sK0(X0),X0) = iProver_top
% 3.40/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.40/1.00      inference(predicate_to_equality,[status(thm)],[c_426]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_9,plain,
% 3.40/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.40/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.40/1.00      | m1_subset_1(X2,u1_struct_0(X1))
% 3.40/1.00      | v2_struct_0(X1)
% 3.40/1.00      | v2_struct_0(X0)
% 3.40/1.00      | ~ l1_pre_topc(X1) ),
% 3.40/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2324,plain,
% 3.40/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.40/1.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.40/1.00      | m1_subset_1(X2,u1_struct_0(X1)) = iProver_top
% 3.40/1.00      | v2_struct_0(X0) = iProver_top
% 3.40/1.00      | v2_struct_0(X1) = iProver_top
% 3.40/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.40/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_4321,plain,
% 3.40/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.40/1.00      | m1_subset_1(sK0(u1_struct_0(X0)),u1_struct_0(X1)) = iProver_top
% 3.40/1.00      | v2_struct_0(X0) = iProver_top
% 3.40/1.00      | v2_struct_0(X1) = iProver_top
% 3.40/1.00      | l1_pre_topc(X1) != iProver_top
% 3.40/1.00      | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
% 3.40/1.00      inference(superposition,[status(thm)],[c_2312,c_2324]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_8466,plain,
% 3.40/1.00      ( m1_pre_topc(sK1(sK3,sK4),X0) != iProver_top
% 3.40/1.00      | m1_subset_1(sK0(sK4),u1_struct_0(X0)) = iProver_top
% 3.40/1.00      | v2_struct_0(X0) = iProver_top
% 3.40/1.00      | v2_struct_0(sK1(sK3,sK4)) = iProver_top
% 3.40/1.00      | l1_pre_topc(X0) != iProver_top
% 3.40/1.00      | v1_xboole_0(u1_struct_0(sK1(sK3,sK4))) = iProver_top ),
% 3.40/1.00      inference(superposition,[status(thm)],[c_3367,c_4321]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_8638,plain,
% 3.40/1.00      ( m1_pre_topc(sK1(sK3,sK4),X0) != iProver_top
% 3.40/1.00      | m1_subset_1(sK0(sK4),u1_struct_0(X0)) = iProver_top
% 3.40/1.00      | v2_struct_0(X0) = iProver_top
% 3.40/1.00      | v2_struct_0(sK1(sK3,sK4)) = iProver_top
% 3.40/1.00      | l1_pre_topc(X0) != iProver_top
% 3.40/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.40/1.00      inference(light_normalisation,[status(thm)],[c_8466,c_3367]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_17,plain,
% 3.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.40/1.00      | v2_struct_0(X1)
% 3.40/1.00      | ~ v2_struct_0(sK1(X1,X0))
% 3.40/1.00      | ~ l1_pre_topc(X1)
% 3.40/1.00      | v1_xboole_0(X0) ),
% 3.40/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2619,plain,
% 3.40/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
% 3.40/1.00      | v2_struct_0(X0)
% 3.40/1.00      | ~ v2_struct_0(sK1(X0,sK4))
% 3.40/1.00      | ~ l1_pre_topc(X0)
% 3.40/1.00      | v1_xboole_0(sK4) ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2620,plain,
% 3.40/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.40/1.00      | v2_struct_0(X0) = iProver_top
% 3.40/1.00      | v2_struct_0(sK1(X0,sK4)) != iProver_top
% 3.40/1.00      | l1_pre_topc(X0) != iProver_top
% 3.40/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.40/1.00      inference(predicate_to_equality,[status(thm)],[c_2619]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2622,plain,
% 3.40/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.40/1.00      | v2_struct_0(sK1(sK3,sK4)) != iProver_top
% 3.40/1.00      | v2_struct_0(sK3) = iProver_top
% 3.40/1.00      | l1_pre_topc(sK3) != iProver_top
% 3.40/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_2620]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_8972,plain,
% 3.40/1.00      ( l1_pre_topc(X0) != iProver_top
% 3.40/1.00      | m1_pre_topc(sK1(sK3,sK4),X0) != iProver_top
% 3.40/1.00      | m1_subset_1(sK0(sK4),u1_struct_0(X0)) = iProver_top
% 3.40/1.00      | v2_struct_0(X0) = iProver_top ),
% 3.40/1.00      inference(global_propositional_subsumption,
% 3.40/1.00                [status(thm)],
% 3.40/1.00                [c_8638,c_32,c_35,c_36,c_37,c_2622]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_8973,plain,
% 3.40/1.00      ( m1_pre_topc(sK1(sK3,sK4),X0) != iProver_top
% 3.40/1.00      | m1_subset_1(sK0(sK4),u1_struct_0(X0)) = iProver_top
% 3.40/1.00      | v2_struct_0(X0) = iProver_top
% 3.40/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.40/1.00      inference(renaming,[status(thm)],[c_8972]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_8982,plain,
% 3.40/1.00      ( m1_subset_1(sK0(sK4),u1_struct_0(sK3)) = iProver_top
% 3.40/1.00      | v2_struct_0(sK3) = iProver_top
% 3.40/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 3.40/1.00      inference(superposition,[status(thm)],[c_3516,c_8973]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2552,plain,
% 3.40/1.00      ( m1_subset_1(sK0(sK4),sK4) | v1_xboole_0(sK4) ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_426]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2553,plain,
% 3.40/1.00      ( m1_subset_1(sK0(sK4),sK4) = iProver_top
% 3.40/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.40/1.00      inference(predicate_to_equality,[status(thm)],[c_2552]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_1740,plain,( X0 = X0 ),theory(equality) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_3024,plain,
% 3.40/1.00      ( sK0(sK4) = sK0(sK4) ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_1740]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_1744,plain,
% 3.40/1.00      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.40/1.00      theory(equality) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2667,plain,
% 3.40/1.00      ( m1_subset_1(X0,X1)
% 3.40/1.00      | ~ m1_subset_1(sK0(sK4),sK4)
% 3.40/1.00      | X0 != sK0(sK4)
% 3.40/1.00      | X1 != sK4 ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_1744]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2859,plain,
% 3.40/1.00      ( m1_subset_1(X0,u1_struct_0(sK1(X1,sK4)))
% 3.40/1.00      | ~ m1_subset_1(sK0(sK4),sK4)
% 3.40/1.00      | X0 != sK0(sK4)
% 3.40/1.00      | u1_struct_0(sK1(X1,sK4)) != sK4 ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_2667]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_3354,plain,
% 3.40/1.00      ( m1_subset_1(sK0(sK4),u1_struct_0(sK1(X0,sK4)))
% 3.40/1.00      | ~ m1_subset_1(sK0(sK4),sK4)
% 3.40/1.00      | u1_struct_0(sK1(X0,sK4)) != sK4
% 3.40/1.00      | sK0(sK4) != sK0(sK4) ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_2859]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_3357,plain,
% 3.40/1.00      ( u1_struct_0(sK1(X0,sK4)) != sK4
% 3.40/1.00      | sK0(sK4) != sK0(sK4)
% 3.40/1.00      | m1_subset_1(sK0(sK4),u1_struct_0(sK1(X0,sK4))) = iProver_top
% 3.40/1.00      | m1_subset_1(sK0(sK4),sK4) != iProver_top ),
% 3.40/1.00      inference(predicate_to_equality,[status(thm)],[c_3354]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_3359,plain,
% 3.40/1.00      ( u1_struct_0(sK1(sK3,sK4)) != sK4
% 3.40/1.00      | sK0(sK4) != sK0(sK4)
% 3.40/1.00      | m1_subset_1(sK0(sK4),u1_struct_0(sK1(sK3,sK4))) = iProver_top
% 3.40/1.00      | m1_subset_1(sK0(sK4),sK4) != iProver_top ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_3357]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2779,plain,
% 3.40/1.00      ( ~ m1_pre_topc(sK1(X0,sK4),X0)
% 3.40/1.00      | m1_subset_1(X1,u1_struct_0(X0))
% 3.40/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1(X0,sK4)))
% 3.40/1.00      | v2_struct_0(X0)
% 3.40/1.00      | v2_struct_0(sK1(X0,sK4))
% 3.40/1.00      | ~ l1_pre_topc(X0) ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_3749,plain,
% 3.40/1.00      ( ~ m1_pre_topc(sK1(X0,sK4),X0)
% 3.40/1.00      | m1_subset_1(sK0(sK4),u1_struct_0(X0))
% 3.40/1.00      | ~ m1_subset_1(sK0(sK4),u1_struct_0(sK1(X0,sK4)))
% 3.40/1.00      | v2_struct_0(X0)
% 3.40/1.00      | v2_struct_0(sK1(X0,sK4))
% 3.40/1.00      | ~ l1_pre_topc(X0) ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_2779]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_3750,plain,
% 3.40/1.00      ( m1_pre_topc(sK1(X0,sK4),X0) != iProver_top
% 3.40/1.00      | m1_subset_1(sK0(sK4),u1_struct_0(X0)) = iProver_top
% 3.40/1.00      | m1_subset_1(sK0(sK4),u1_struct_0(sK1(X0,sK4))) != iProver_top
% 3.40/1.00      | v2_struct_0(X0) = iProver_top
% 3.40/1.00      | v2_struct_0(sK1(X0,sK4)) = iProver_top
% 3.40/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.40/1.00      inference(predicate_to_equality,[status(thm)],[c_3749]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_3752,plain,
% 3.40/1.00      ( m1_pre_topc(sK1(sK3,sK4),sK3) != iProver_top
% 3.40/1.00      | m1_subset_1(sK0(sK4),u1_struct_0(sK1(sK3,sK4))) != iProver_top
% 3.40/1.00      | m1_subset_1(sK0(sK4),u1_struct_0(sK3)) = iProver_top
% 3.40/1.00      | v2_struct_0(sK1(sK3,sK4)) = iProver_top
% 3.40/1.00      | v2_struct_0(sK3) = iProver_top
% 3.40/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_3750]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_8985,plain,
% 3.40/1.00      ( m1_subset_1(sK0(sK4),u1_struct_0(sK3)) = iProver_top ),
% 3.40/1.00      inference(global_propositional_subsumption,
% 3.40/1.00                [status(thm)],
% 3.40/1.00                [c_8982,c_31,c_32,c_28,c_35,c_27,c_36,c_26,c_37,c_2553,
% 3.40/1.00                 c_2622,c_2631,c_2642,c_3024,c_3359,c_3752]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_11,plain,
% 3.40/1.00      ( ~ m1_subset_1(X0,X1)
% 3.40/1.00      | v1_xboole_0(X1)
% 3.40/1.00      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 3.40/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2322,plain,
% 3.40/1.00      ( k6_domain_1(X0,X1) = k1_tarski(X1)
% 3.40/1.00      | m1_subset_1(X1,X0) != iProver_top
% 3.40/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.40/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_8993,plain,
% 3.40/1.00      ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k1_tarski(sK0(sK4))
% 3.40/1.00      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.40/1.00      inference(superposition,[status(thm)],[c_8985,c_2322]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_25,negated_conjecture,
% 3.40/1.00      ( v2_tex_2(sK4,sK3) | v1_zfmisc_1(sK4) ),
% 3.40/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2317,plain,
% 3.40/1.00      ( v2_tex_2(sK4,sK3) = iProver_top
% 3.40/1.00      | v1_zfmisc_1(sK4) = iProver_top ),
% 3.40/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_19,plain,
% 3.40/1.00      ( ~ v2_tex_2(X0,X1)
% 3.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.40/1.00      | ~ v2_pre_topc(X1)
% 3.40/1.00      | v2_struct_0(X1)
% 3.40/1.00      | ~ l1_pre_topc(X1)
% 3.40/1.00      | v1_xboole_0(X0)
% 3.40/1.00      | u1_struct_0(sK2(X1,X0)) = X0 ),
% 3.40/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_30,negated_conjecture,
% 3.40/1.00      ( v2_pre_topc(sK3) ),
% 3.40/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_754,plain,
% 3.40/1.00      ( ~ v2_tex_2(X0,X1)
% 3.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.40/1.00      | v2_struct_0(X1)
% 3.40/1.00      | ~ l1_pre_topc(X1)
% 3.40/1.00      | v1_xboole_0(X0)
% 3.40/1.00      | u1_struct_0(sK2(X1,X0)) = X0
% 3.40/1.00      | sK3 != X1 ),
% 3.40/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_755,plain,
% 3.40/1.00      ( ~ v2_tex_2(X0,sK3)
% 3.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.40/1.00      | v2_struct_0(sK3)
% 3.40/1.00      | ~ l1_pre_topc(sK3)
% 3.40/1.00      | v1_xboole_0(X0)
% 3.40/1.00      | u1_struct_0(sK2(sK3,X0)) = X0 ),
% 3.40/1.00      inference(unflattening,[status(thm)],[c_754]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_759,plain,
% 3.40/1.00      ( ~ v2_tex_2(X0,sK3)
% 3.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.40/1.00      | v1_xboole_0(X0)
% 3.40/1.00      | u1_struct_0(sK2(sK3,X0)) = X0 ),
% 3.40/1.00      inference(global_propositional_subsumption,
% 3.40/1.00                [status(thm)],
% 3.40/1.00                [c_755,c_31,c_28]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2307,plain,
% 3.40/1.00      ( u1_struct_0(sK2(sK3,X0)) = X0
% 3.40/1.00      | v2_tex_2(X0,sK3) != iProver_top
% 3.40/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.40/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.40/1.00      inference(predicate_to_equality,[status(thm)],[c_759]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2995,plain,
% 3.40/1.00      ( u1_struct_0(sK2(sK3,sK4)) = sK4
% 3.40/1.00      | v2_tex_2(sK4,sK3) != iProver_top
% 3.40/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.40/1.00      inference(superposition,[status(thm)],[c_2316,c_2307]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_3039,plain,
% 3.40/1.00      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.40/1.00      | u1_struct_0(sK2(sK3,sK4)) = sK4 ),
% 3.40/1.00      inference(global_propositional_subsumption,
% 3.40/1.00                [status(thm)],
% 3.40/1.00                [c_2995,c_36]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_3040,plain,
% 3.40/1.00      ( u1_struct_0(sK2(sK3,sK4)) = sK4
% 3.40/1.00      | v2_tex_2(sK4,sK3) != iProver_top ),
% 3.40/1.00      inference(renaming,[status(thm)],[c_3039]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_3045,plain,
% 3.40/1.00      ( u1_struct_0(sK2(sK3,sK4)) = sK4
% 3.40/1.00      | v1_zfmisc_1(sK4) = iProver_top ),
% 3.40/1.00      inference(superposition,[status(thm)],[c_2317,c_3040]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_4326,plain,
% 3.40/1.00      ( k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0))
% 3.40/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.40/1.00      inference(superposition,[status(thm)],[c_2312,c_2322]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2315,plain,
% 3.40/1.00      ( v1_xboole_0(sK4) != iProver_top ),
% 3.40/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_4474,plain,
% 3.40/1.00      ( k6_domain_1(sK4,sK0(sK4)) = k1_tarski(sK0(sK4)) ),
% 3.40/1.00      inference(superposition,[status(thm)],[c_4326,c_2315]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_10,plain,
% 3.40/1.00      ( ~ m1_subset_1(X0,X1)
% 3.40/1.00      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 3.40/1.00      | v1_xboole_0(X1) ),
% 3.40/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2323,plain,
% 3.40/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 3.40/1.00      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
% 3.40/1.00      | v1_xboole_0(X1) = iProver_top ),
% 3.40/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_4511,plain,
% 3.40/1.00      ( m1_subset_1(k1_tarski(sK0(sK4)),k1_zfmisc_1(sK4)) = iProver_top
% 3.40/1.00      | m1_subset_1(sK0(sK4),sK4) != iProver_top
% 3.40/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.40/1.00      inference(superposition,[status(thm)],[c_4474,c_2323]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_4798,plain,
% 3.40/1.00      ( m1_subset_1(k1_tarski(sK0(sK4)),k1_zfmisc_1(sK4)) = iProver_top ),
% 3.40/1.00      inference(global_propositional_subsumption,
% 3.40/1.00                [status(thm)],
% 3.40/1.00                [c_4511,c_36,c_2553]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_5,plain,
% 3.40/1.00      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.40/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_18,plain,
% 3.40/1.00      ( ~ r1_tarski(X0,X1)
% 3.40/1.00      | ~ v1_zfmisc_1(X1)
% 3.40/1.00      | v1_xboole_0(X0)
% 3.40/1.00      | v1_xboole_0(X1)
% 3.40/1.00      | X1 = X0 ),
% 3.40/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_442,plain,
% 3.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.40/1.00      | ~ v1_zfmisc_1(X1)
% 3.40/1.00      | v1_xboole_0(X0)
% 3.40/1.00      | v1_xboole_0(X1)
% 3.40/1.00      | X1 = X0 ),
% 3.40/1.00      inference(resolution,[status(thm)],[c_5,c_18]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_3,plain,
% 3.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.40/1.00      | ~ v1_xboole_0(X1)
% 3.40/1.00      | v1_xboole_0(X0) ),
% 3.40/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_446,plain,
% 3.40/1.00      ( v1_xboole_0(X0)
% 3.40/1.00      | ~ v1_zfmisc_1(X1)
% 3.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.40/1.00      | X1 = X0 ),
% 3.40/1.00      inference(global_propositional_subsumption,
% 3.40/1.00                [status(thm)],
% 3.40/1.00                [c_442,c_3]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_447,plain,
% 3.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.40/1.00      | ~ v1_zfmisc_1(X1)
% 3.40/1.00      | v1_xboole_0(X0)
% 3.40/1.00      | X1 = X0 ),
% 3.40/1.00      inference(renaming,[status(thm)],[c_446]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2311,plain,
% 3.40/1.00      ( X0 = X1
% 3.40/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 3.40/1.00      | v1_zfmisc_1(X0) != iProver_top
% 3.40/1.00      | v1_xboole_0(X1) = iProver_top ),
% 3.40/1.00      inference(predicate_to_equality,[status(thm)],[c_447]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_4806,plain,
% 3.40/1.00      ( k1_tarski(sK0(sK4)) = sK4
% 3.40/1.00      | v1_zfmisc_1(sK4) != iProver_top
% 3.40/1.00      | v1_xboole_0(k1_tarski(sK0(sK4))) = iProver_top ),
% 3.40/1.00      inference(superposition,[status(thm)],[c_4798,c_2311]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2,plain,
% 3.40/1.00      ( ~ v1_xboole_0(k1_tarski(X0)) ),
% 3.40/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2327,plain,
% 3.40/1.00      ( v1_xboole_0(k1_tarski(X0)) != iProver_top ),
% 3.40/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_5561,plain,
% 3.40/1.00      ( k1_tarski(sK0(sK4)) = sK4 | v1_zfmisc_1(sK4) != iProver_top ),
% 3.40/1.00      inference(forward_subsumption_resolution,
% 3.40/1.00                [status(thm)],
% 3.40/1.00                [c_4806,c_2327]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_5563,plain,
% 3.40/1.00      ( u1_struct_0(sK2(sK3,sK4)) = sK4 | k1_tarski(sK0(sK4)) = sK4 ),
% 3.40/1.00      inference(superposition,[status(thm)],[c_3045,c_5561]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_13,plain,
% 3.40/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.40/1.00      | ~ v1_tdlat_3(X0)
% 3.40/1.00      | ~ v2_tdlat_3(X1)
% 3.40/1.00      | ~ v2_pre_topc(X1)
% 3.40/1.00      | v2_struct_0(X1)
% 3.40/1.00      | v2_struct_0(X0)
% 3.40/1.00      | v7_struct_0(X0)
% 3.40/1.00      | ~ l1_pre_topc(X1) ),
% 3.40/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_6,plain,
% 3.40/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.40/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_8,plain,
% 3.40/1.00      ( ~ v7_struct_0(X0)
% 3.40/1.00      | v1_zfmisc_1(u1_struct_0(X0))
% 3.40/1.00      | ~ l1_struct_0(X0) ),
% 3.40/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_407,plain,
% 3.40/1.00      ( ~ v7_struct_0(X0)
% 3.40/1.00      | v1_zfmisc_1(u1_struct_0(X0))
% 3.40/1.00      | ~ l1_pre_topc(X0) ),
% 3.40/1.00      inference(resolution,[status(thm)],[c_6,c_8]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_468,plain,
% 3.40/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.40/1.00      | ~ v1_tdlat_3(X0)
% 3.40/1.00      | ~ v2_tdlat_3(X1)
% 3.40/1.00      | ~ v2_pre_topc(X1)
% 3.40/1.00      | v2_struct_0(X0)
% 3.40/1.00      | v2_struct_0(X1)
% 3.40/1.00      | v1_zfmisc_1(u1_struct_0(X0))
% 3.40/1.00      | ~ l1_pre_topc(X0)
% 3.40/1.00      | ~ l1_pre_topc(X1) ),
% 3.40/1.00      inference(resolution,[status(thm)],[c_13,c_407]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_7,plain,
% 3.40/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.40/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_472,plain,
% 3.40/1.00      ( v1_zfmisc_1(u1_struct_0(X0))
% 3.40/1.00      | v2_struct_0(X1)
% 3.40/1.00      | v2_struct_0(X0)
% 3.40/1.00      | ~ v2_pre_topc(X1)
% 3.40/1.00      | ~ v2_tdlat_3(X1)
% 3.40/1.00      | ~ v1_tdlat_3(X0)
% 3.40/1.00      | ~ m1_pre_topc(X0,X1)
% 3.40/1.00      | ~ l1_pre_topc(X1) ),
% 3.40/1.00      inference(global_propositional_subsumption,
% 3.40/1.00                [status(thm)],
% 3.40/1.00                [c_468,c_7]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_473,plain,
% 3.40/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.40/1.00      | ~ v1_tdlat_3(X0)
% 3.40/1.00      | ~ v2_tdlat_3(X1)
% 3.40/1.00      | ~ v2_pre_topc(X1)
% 3.40/1.00      | v2_struct_0(X0)
% 3.40/1.00      | v2_struct_0(X1)
% 3.40/1.00      | v1_zfmisc_1(u1_struct_0(X0))
% 3.40/1.00      | ~ l1_pre_topc(X1) ),
% 3.40/1.00      inference(renaming,[status(thm)],[c_472]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_12,plain,
% 3.40/1.00      ( ~ v2_tdlat_3(X0) | v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 3.40/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_492,plain,
% 3.40/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.40/1.00      | ~ v1_tdlat_3(X0)
% 3.40/1.00      | ~ v2_tdlat_3(X1)
% 3.40/1.00      | v2_struct_0(X0)
% 3.40/1.00      | v2_struct_0(X1)
% 3.40/1.00      | v1_zfmisc_1(u1_struct_0(X0))
% 3.40/1.00      | ~ l1_pre_topc(X1) ),
% 3.40/1.00      inference(forward_subsumption_resolution,
% 3.40/1.00                [status(thm)],
% 3.40/1.00                [c_473,c_12]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_29,negated_conjecture,
% 3.40/1.00      ( v2_tdlat_3(sK3) ),
% 3.40/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_513,plain,
% 3.40/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.40/1.00      | ~ v1_tdlat_3(X0)
% 3.40/1.00      | v2_struct_0(X0)
% 3.40/1.00      | v2_struct_0(X1)
% 3.40/1.00      | v1_zfmisc_1(u1_struct_0(X0))
% 3.40/1.00      | ~ l1_pre_topc(X1)
% 3.40/1.00      | sK3 != X1 ),
% 3.40/1.00      inference(resolution_lifted,[status(thm)],[c_492,c_29]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_514,plain,
% 3.40/1.00      ( ~ m1_pre_topc(X0,sK3)
% 3.40/1.00      | ~ v1_tdlat_3(X0)
% 3.40/1.00      | v2_struct_0(X0)
% 3.40/1.00      | v2_struct_0(sK3)
% 3.40/1.00      | v1_zfmisc_1(u1_struct_0(X0))
% 3.40/1.00      | ~ l1_pre_topc(sK3) ),
% 3.40/1.00      inference(unflattening,[status(thm)],[c_513]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_518,plain,
% 3.40/1.00      ( v1_zfmisc_1(u1_struct_0(X0))
% 3.40/1.00      | ~ m1_pre_topc(X0,sK3)
% 3.40/1.00      | ~ v1_tdlat_3(X0)
% 3.40/1.00      | v2_struct_0(X0) ),
% 3.40/1.00      inference(global_propositional_subsumption,
% 3.40/1.00                [status(thm)],
% 3.40/1.00                [c_514,c_31,c_28]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_519,plain,
% 3.40/1.00      ( ~ m1_pre_topc(X0,sK3)
% 3.40/1.00      | ~ v1_tdlat_3(X0)
% 3.40/1.00      | v2_struct_0(X0)
% 3.40/1.00      | v1_zfmisc_1(u1_struct_0(X0)) ),
% 3.40/1.00      inference(renaming,[status(thm)],[c_518]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_21,plain,
% 3.40/1.00      ( ~ v2_tex_2(X0,X1)
% 3.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.40/1.00      | v1_tdlat_3(sK2(X1,X0))
% 3.40/1.00      | ~ v2_pre_topc(X1)
% 3.40/1.00      | v2_struct_0(X1)
% 3.40/1.00      | ~ l1_pre_topc(X1)
% 3.40/1.00      | v1_xboole_0(X0) ),
% 3.40/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_706,plain,
% 3.40/1.00      ( ~ v2_tex_2(X0,X1)
% 3.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.40/1.00      | v1_tdlat_3(sK2(X1,X0))
% 3.40/1.00      | v2_struct_0(X1)
% 3.40/1.00      | ~ l1_pre_topc(X1)
% 3.40/1.00      | v1_xboole_0(X0)
% 3.40/1.00      | sK3 != X1 ),
% 3.40/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_30]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_707,plain,
% 3.40/1.00      ( ~ v2_tex_2(X0,sK3)
% 3.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.40/1.00      | v1_tdlat_3(sK2(sK3,X0))
% 3.40/1.00      | v2_struct_0(sK3)
% 3.40/1.00      | ~ l1_pre_topc(sK3)
% 3.40/1.00      | v1_xboole_0(X0) ),
% 3.40/1.00      inference(unflattening,[status(thm)],[c_706]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_711,plain,
% 3.40/1.00      ( ~ v2_tex_2(X0,sK3)
% 3.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.40/1.00      | v1_tdlat_3(sK2(sK3,X0))
% 3.40/1.00      | v1_xboole_0(X0) ),
% 3.40/1.00      inference(global_propositional_subsumption,
% 3.40/1.00                [status(thm)],
% 3.40/1.00                [c_707,c_31,c_28]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_801,plain,
% 3.40/1.00      ( ~ v2_tex_2(X0,sK3)
% 3.40/1.00      | ~ m1_pre_topc(X1,sK3)
% 3.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.40/1.00      | v2_struct_0(X1)
% 3.40/1.00      | v1_zfmisc_1(u1_struct_0(X1))
% 3.40/1.00      | v1_xboole_0(X0)
% 3.40/1.00      | sK2(sK3,X0) != X1 ),
% 3.40/1.00      inference(resolution_lifted,[status(thm)],[c_519,c_711]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_802,plain,
% 3.40/1.00      ( ~ v2_tex_2(X0,sK3)
% 3.40/1.00      | ~ m1_pre_topc(sK2(sK3,X0),sK3)
% 3.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.40/1.00      | v2_struct_0(sK2(sK3,X0))
% 3.40/1.00      | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
% 3.40/1.00      | v1_xboole_0(X0) ),
% 3.40/1.00      inference(unflattening,[status(thm)],[c_801]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_22,plain,
% 3.40/1.00      ( ~ v2_tex_2(X0,X1)
% 3.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.40/1.00      | ~ v2_pre_topc(X1)
% 3.40/1.00      | v2_struct_0(X1)
% 3.40/1.00      | ~ v2_struct_0(sK2(X1,X0))
% 3.40/1.00      | ~ l1_pre_topc(X1)
% 3.40/1.00      | v1_xboole_0(X0) ),
% 3.40/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_682,plain,
% 3.40/1.00      ( ~ v2_tex_2(X0,X1)
% 3.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.40/1.00      | v2_struct_0(X1)
% 3.40/1.00      | ~ v2_struct_0(sK2(X1,X0))
% 3.40/1.00      | ~ l1_pre_topc(X1)
% 3.40/1.00      | v1_xboole_0(X0)
% 3.40/1.00      | sK3 != X1 ),
% 3.40/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_30]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_683,plain,
% 3.40/1.00      ( ~ v2_tex_2(X0,sK3)
% 3.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.40/1.00      | ~ v2_struct_0(sK2(sK3,X0))
% 3.40/1.00      | v2_struct_0(sK3)
% 3.40/1.00      | ~ l1_pre_topc(sK3)
% 3.40/1.00      | v1_xboole_0(X0) ),
% 3.40/1.00      inference(unflattening,[status(thm)],[c_682]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_687,plain,
% 3.40/1.00      ( ~ v2_tex_2(X0,sK3)
% 3.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.40/1.00      | ~ v2_struct_0(sK2(sK3,X0))
% 3.40/1.00      | v1_xboole_0(X0) ),
% 3.40/1.00      inference(global_propositional_subsumption,
% 3.40/1.00                [status(thm)],
% 3.40/1.00                [c_683,c_31,c_28]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_20,plain,
% 3.40/1.00      ( ~ v2_tex_2(X0,X1)
% 3.40/1.00      | m1_pre_topc(sK2(X1,X0),X1)
% 3.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.40/1.00      | ~ v2_pre_topc(X1)
% 3.40/1.00      | v2_struct_0(X1)
% 3.40/1.00      | ~ l1_pre_topc(X1)
% 3.40/1.00      | v1_xboole_0(X0) ),
% 3.40/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_730,plain,
% 3.40/1.00      ( ~ v2_tex_2(X0,X1)
% 3.40/1.00      | m1_pre_topc(sK2(X1,X0),X1)
% 3.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.40/1.00      | v2_struct_0(X1)
% 3.40/1.00      | ~ l1_pre_topc(X1)
% 3.40/1.00      | v1_xboole_0(X0)
% 3.40/1.00      | sK3 != X1 ),
% 3.40/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_30]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_731,plain,
% 3.40/1.00      ( ~ v2_tex_2(X0,sK3)
% 3.40/1.00      | m1_pre_topc(sK2(sK3,X0),sK3)
% 3.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.40/1.00      | v2_struct_0(sK3)
% 3.40/1.00      | ~ l1_pre_topc(sK3)
% 3.40/1.00      | v1_xboole_0(X0) ),
% 3.40/1.00      inference(unflattening,[status(thm)],[c_730]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_735,plain,
% 3.40/1.00      ( ~ v2_tex_2(X0,sK3)
% 3.40/1.00      | m1_pre_topc(sK2(sK3,X0),sK3)
% 3.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.40/1.00      | v1_xboole_0(X0) ),
% 3.40/1.00      inference(global_propositional_subsumption,
% 3.40/1.00                [status(thm)],
% 3.40/1.00                [c_731,c_31,c_28]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_806,plain,
% 3.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.40/1.00      | ~ v2_tex_2(X0,sK3)
% 3.40/1.00      | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
% 3.40/1.00      | v1_xboole_0(X0) ),
% 3.40/1.00      inference(global_propositional_subsumption,
% 3.40/1.00                [status(thm)],
% 3.40/1.00                [c_802,c_687,c_735]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_807,plain,
% 3.40/1.00      ( ~ v2_tex_2(X0,sK3)
% 3.40/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.40/1.00      | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
% 3.40/1.00      | v1_xboole_0(X0) ),
% 3.40/1.00      inference(renaming,[status(thm)],[c_806]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2306,plain,
% 3.40/1.00      ( v2_tex_2(X0,sK3) != iProver_top
% 3.40/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.40/1.00      | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0))) = iProver_top
% 3.40/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.40/1.00      inference(predicate_to_equality,[status(thm)],[c_807]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2665,plain,
% 3.40/1.00      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.40/1.00      | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) = iProver_top
% 3.40/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.40/1.00      inference(superposition,[status(thm)],[c_2316,c_2306]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2984,plain,
% 3.40/1.00      ( v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) = iProver_top
% 3.40/1.00      | v2_tex_2(sK4,sK3) != iProver_top ),
% 3.40/1.00      inference(global_propositional_subsumption,
% 3.40/1.00                [status(thm)],
% 3.40/1.00                [c_2665,c_36]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2985,plain,
% 3.40/1.00      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.40/1.00      | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) = iProver_top ),
% 3.40/1.00      inference(renaming,[status(thm)],[c_2984]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_5623,plain,
% 3.40/1.00      ( k1_tarski(sK0(sK4)) = sK4
% 3.40/1.00      | v2_tex_2(sK4,sK3) != iProver_top
% 3.40/1.00      | v1_zfmisc_1(sK4) = iProver_top ),
% 3.40/1.00      inference(superposition,[status(thm)],[c_5563,c_2985]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_38,plain,
% 3.40/1.00      ( v2_tex_2(sK4,sK3) = iProver_top
% 3.40/1.00      | v1_zfmisc_1(sK4) = iProver_top ),
% 3.40/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_5694,plain,
% 3.40/1.00      ( k1_tarski(sK0(sK4)) = sK4 ),
% 3.40/1.00      inference(global_propositional_subsumption,
% 3.40/1.00                [status(thm)],
% 3.40/1.00                [c_5623,c_38,c_5561]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_8996,plain,
% 3.40/1.00      ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = sK4
% 3.40/1.00      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.40/1.00      inference(light_normalisation,[status(thm)],[c_8993,c_5694]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2560,plain,
% 3.40/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
% 3.40/1.00      | ~ v1_xboole_0(X0)
% 3.40/1.00      | v1_xboole_0(sK4) ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2672,plain,
% 3.40/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.40/1.00      | ~ v1_xboole_0(u1_struct_0(sK3))
% 3.40/1.00      | v1_xboole_0(sK4) ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_2560]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2673,plain,
% 3.40/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.40/1.00      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top
% 3.40/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.40/1.00      inference(predicate_to_equality,[status(thm)],[c_2672]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_9605,plain,
% 3.40/1.00      ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = sK4 ),
% 3.40/1.00      inference(global_propositional_subsumption,
% 3.40/1.00                [status(thm)],
% 3.40/1.00                [c_8996,c_36,c_37,c_2673]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_23,plain,
% 3.40/1.00      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 3.40/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.40/1.00      | ~ v2_pre_topc(X0)
% 3.40/1.00      | v2_struct_0(X0)
% 3.40/1.00      | ~ l1_pre_topc(X0) ),
% 3.40/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_664,plain,
% 3.40/1.00      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 3.40/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.40/1.00      | v2_struct_0(X0)
% 3.40/1.00      | ~ l1_pre_topc(X0)
% 3.40/1.00      | sK3 != X0 ),
% 3.40/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_30]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_665,plain,
% 3.40/1.00      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
% 3.40/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.40/1.00      | v2_struct_0(sK3)
% 3.40/1.00      | ~ l1_pre_topc(sK3) ),
% 3.40/1.00      inference(unflattening,[status(thm)],[c_664]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_669,plain,
% 3.40/1.00      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
% 3.40/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 3.40/1.00      inference(global_propositional_subsumption,
% 3.40/1.00                [status(thm)],
% 3.40/1.00                [c_665,c_31,c_28]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2310,plain,
% 3.40/1.00      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) = iProver_top
% 3.40/1.00      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.40/1.00      inference(predicate_to_equality,[status(thm)],[c_669]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_9617,plain,
% 3.40/1.00      ( v2_tex_2(sK4,sK3) = iProver_top
% 3.40/1.00      | m1_subset_1(sK0(sK4),u1_struct_0(sK3)) != iProver_top ),
% 3.40/1.00      inference(superposition,[status(thm)],[c_9605,c_2310]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_1748,plain,
% 3.40/1.00      ( ~ v1_zfmisc_1(X0) | v1_zfmisc_1(X1) | X1 != X0 ),
% 3.40/1.00      theory(equality) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2834,plain,
% 3.40/1.00      ( v1_zfmisc_1(X0)
% 3.40/1.00      | ~ v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
% 3.40/1.00      | X0 != u1_struct_0(sK2(sK3,sK4)) ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_1748]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_7190,plain,
% 3.40/1.00      ( ~ v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
% 3.40/1.00      | v1_zfmisc_1(sK4)
% 3.40/1.00      | sK4 != u1_struct_0(sK2(sK3,sK4)) ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_2834]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_7191,plain,
% 3.40/1.00      ( sK4 != u1_struct_0(sK2(sK3,sK4))
% 3.40/1.00      | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) != iProver_top
% 3.40/1.00      | v1_zfmisc_1(sK4) = iProver_top ),
% 3.40/1.00      inference(predicate_to_equality,[status(thm)],[c_7190]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_1741,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2675,plain,
% 3.40/1.00      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_1741]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2872,plain,
% 3.40/1.00      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_2675]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_3031,plain,
% 3.40/1.00      ( u1_struct_0(sK2(sK3,sK4)) != sK4
% 3.40/1.00      | sK4 = u1_struct_0(sK2(sK3,sK4))
% 3.40/1.00      | sK4 != sK4 ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_2872]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_2696,plain,
% 3.40/1.00      ( sK4 = sK4 ),
% 3.40/1.00      inference(instantiation,[status(thm)],[c_1740]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_24,negated_conjecture,
% 3.40/1.00      ( ~ v2_tex_2(sK4,sK3) | ~ v1_zfmisc_1(sK4) ),
% 3.40/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(c_39,plain,
% 3.40/1.00      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.40/1.00      | v1_zfmisc_1(sK4) != iProver_top ),
% 3.40/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.40/1.00  
% 3.40/1.00  cnf(contradiction,plain,
% 3.40/1.00      ( $false ),
% 3.40/1.00      inference(minisat,
% 3.40/1.00                [status(thm)],
% 3.40/1.00                [c_9617,c_7191,c_3752,c_3359,c_3031,c_3024,c_2995,c_2696,
% 3.40/1.00                 c_2665,c_2642,c_2631,c_2622,c_2553,c_39,c_37,c_26,c_36,
% 3.40/1.00                 c_27,c_35,c_28,c_32,c_31]) ).
% 3.40/1.00  
% 3.40/1.00  
% 3.40/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.40/1.00  
% 3.40/1.00  ------                               Statistics
% 3.40/1.00  
% 3.40/1.00  ------ General
% 3.40/1.00  
% 3.40/1.00  abstr_ref_over_cycles:                  0
% 3.40/1.00  abstr_ref_under_cycles:                 0
% 3.40/1.00  gc_basic_clause_elim:                   0
% 3.40/1.00  forced_gc_time:                         0
% 3.40/1.00  parsing_time:                           0.008
% 3.40/1.00  unif_index_cands_time:                  0.
% 3.40/1.00  unif_index_add_time:                    0.
% 3.40/1.00  orderings_time:                         0.
% 3.40/1.00  out_proof_time:                         0.012
% 3.40/1.00  total_time:                             0.265
% 3.40/1.00  num_of_symbols:                         54
% 3.40/1.00  num_of_terms:                           6221
% 3.40/1.00  
% 3.40/1.00  ------ Preprocessing
% 3.40/1.00  
% 3.40/1.00  num_of_splits:                          0
% 3.40/1.00  num_of_split_atoms:                     0
% 3.40/1.00  num_of_reused_defs:                     0
% 3.40/1.01  num_eq_ax_congr_red:                    25
% 3.40/1.01  num_of_sem_filtered_clauses:            1
% 3.40/1.01  num_of_subtypes:                        0
% 3.40/1.01  monotx_restored_types:                  0
% 3.40/1.01  sat_num_of_epr_types:                   0
% 3.40/1.01  sat_num_of_non_cyclic_types:            0
% 3.40/1.01  sat_guarded_non_collapsed_types:        0
% 3.40/1.01  num_pure_diseq_elim:                    0
% 3.40/1.01  simp_replaced_by:                       0
% 3.40/1.01  res_preprocessed:                       124
% 3.40/1.01  prep_upred:                             0
% 3.40/1.01  prep_unflattend:                        51
% 3.40/1.01  smt_new_axioms:                         0
% 3.40/1.01  pred_elim_cands:                        7
% 3.40/1.01  pred_elim:                              7
% 3.40/1.01  pred_elim_cl:                           9
% 3.40/1.01  pred_elim_cycles:                       15
% 3.40/1.01  merged_defs:                            8
% 3.40/1.01  merged_defs_ncl:                        0
% 3.40/1.01  bin_hyper_res:                          8
% 3.40/1.01  prep_cycles:                            4
% 3.40/1.01  pred_elim_time:                         0.022
% 3.40/1.01  splitting_time:                         0.
% 3.40/1.01  sem_filter_time:                        0.
% 3.40/1.01  monotx_time:                            0.001
% 3.40/1.01  subtype_inf_time:                       0.
% 3.40/1.01  
% 3.40/1.01  ------ Problem properties
% 3.40/1.01  
% 3.40/1.01  clauses:                                22
% 3.40/1.01  conjectures:                            6
% 3.40/1.01  epr:                                    6
% 3.40/1.01  horn:                                   10
% 3.40/1.01  ground:                                 6
% 3.40/1.01  unary:                                  5
% 3.40/1.01  binary:                                 4
% 3.40/1.01  lits:                                   66
% 3.40/1.01  lits_eq:                                4
% 3.40/1.01  fd_pure:                                0
% 3.40/1.01  fd_pseudo:                              0
% 3.40/1.01  fd_cond:                                0
% 3.40/1.01  fd_pseudo_cond:                         1
% 3.40/1.01  ac_symbols:                             0
% 3.40/1.01  
% 3.40/1.01  ------ Propositional Solver
% 3.40/1.01  
% 3.40/1.01  prop_solver_calls:                      30
% 3.40/1.01  prop_fast_solver_calls:                 1643
% 3.40/1.01  smt_solver_calls:                       0
% 3.40/1.01  smt_fast_solver_calls:                  0
% 3.40/1.01  prop_num_of_clauses:                    2927
% 3.40/1.01  prop_preprocess_simplified:             7859
% 3.40/1.01  prop_fo_subsumed:                       151
% 3.40/1.01  prop_solver_time:                       0.
% 3.40/1.01  smt_solver_time:                        0.
% 3.40/1.01  smt_fast_solver_time:                   0.
% 3.40/1.01  prop_fast_solver_time:                  0.
% 3.40/1.01  prop_unsat_core_time:                   0.
% 3.40/1.01  
% 3.40/1.01  ------ QBF
% 3.40/1.01  
% 3.40/1.01  qbf_q_res:                              0
% 3.40/1.01  qbf_num_tautologies:                    0
% 3.40/1.01  qbf_prep_cycles:                        0
% 3.40/1.01  
% 3.40/1.01  ------ BMC1
% 3.40/1.01  
% 3.40/1.01  bmc1_current_bound:                     -1
% 3.40/1.01  bmc1_last_solved_bound:                 -1
% 3.40/1.01  bmc1_unsat_core_size:                   -1
% 3.40/1.01  bmc1_unsat_core_parents_size:           -1
% 3.40/1.01  bmc1_merge_next_fun:                    0
% 3.40/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.40/1.01  
% 3.40/1.01  ------ Instantiation
% 3.40/1.01  
% 3.40/1.01  inst_num_of_clauses:                    864
% 3.40/1.01  inst_num_in_passive:                    95
% 3.40/1.01  inst_num_in_active:                     509
% 3.40/1.01  inst_num_in_unprocessed:                260
% 3.40/1.01  inst_num_of_loops:                      570
% 3.40/1.01  inst_num_of_learning_restarts:          0
% 3.40/1.01  inst_num_moves_active_passive:          56
% 3.40/1.01  inst_lit_activity:                      0
% 3.40/1.01  inst_lit_activity_moves:                0
% 3.40/1.01  inst_num_tautologies:                   0
% 3.40/1.01  inst_num_prop_implied:                  0
% 3.40/1.01  inst_num_existing_simplified:           0
% 3.40/1.01  inst_num_eq_res_simplified:             0
% 3.40/1.01  inst_num_child_elim:                    0
% 3.40/1.01  inst_num_of_dismatching_blockings:      298
% 3.40/1.01  inst_num_of_non_proper_insts:           1012
% 3.40/1.01  inst_num_of_duplicates:                 0
% 3.40/1.01  inst_inst_num_from_inst_to_res:         0
% 3.40/1.01  inst_dismatching_checking_time:         0.
% 3.40/1.01  
% 3.40/1.01  ------ Resolution
% 3.40/1.01  
% 3.40/1.01  res_num_of_clauses:                     0
% 3.40/1.01  res_num_in_passive:                     0
% 3.40/1.01  res_num_in_active:                      0
% 3.40/1.01  res_num_of_loops:                       128
% 3.40/1.01  res_forward_subset_subsumed:            140
% 3.40/1.01  res_backward_subset_subsumed:           4
% 3.40/1.01  res_forward_subsumed:                   0
% 3.40/1.01  res_backward_subsumed:                  0
% 3.40/1.01  res_forward_subsumption_resolution:     2
% 3.40/1.01  res_backward_subsumption_resolution:    0
% 3.40/1.01  res_clause_to_clause_subsumption:       443
% 3.40/1.01  res_orphan_elimination:                 0
% 3.40/1.01  res_tautology_del:                      203
% 3.40/1.01  res_num_eq_res_simplified:              0
% 3.40/1.01  res_num_sel_changes:                    0
% 3.40/1.01  res_moves_from_active_to_pass:          0
% 3.40/1.01  
% 3.40/1.01  ------ Superposition
% 3.40/1.01  
% 3.40/1.01  sup_time_total:                         0.
% 3.40/1.01  sup_time_generating:                    0.
% 3.40/1.01  sup_time_sim_full:                      0.
% 3.40/1.01  sup_time_sim_immed:                     0.
% 3.40/1.01  
% 3.40/1.01  sup_num_of_clauses:                     197
% 3.40/1.01  sup_num_in_active:                      110
% 3.40/1.01  sup_num_in_passive:                     87
% 3.40/1.01  sup_num_of_loops:                       113
% 3.40/1.01  sup_fw_superposition:                   93
% 3.40/1.01  sup_bw_superposition:                   141
% 3.40/1.01  sup_immediate_simplified:               80
% 3.40/1.01  sup_given_eliminated:                   0
% 3.40/1.01  comparisons_done:                       0
% 3.40/1.01  comparisons_avoided:                    0
% 3.40/1.01  
% 3.40/1.01  ------ Simplifications
% 3.40/1.01  
% 3.40/1.01  
% 3.40/1.01  sim_fw_subset_subsumed:                 21
% 3.40/1.01  sim_bw_subset_subsumed:                 11
% 3.40/1.01  sim_fw_subsumed:                        4
% 3.40/1.01  sim_bw_subsumed:                        0
% 3.40/1.01  sim_fw_subsumption_res:                 5
% 3.40/1.01  sim_bw_subsumption_res:                 0
% 3.40/1.01  sim_tautology_del:                      7
% 3.40/1.01  sim_eq_tautology_del:                   3
% 3.40/1.01  sim_eq_res_simp:                        0
% 3.40/1.01  sim_fw_demodulated:                     3
% 3.40/1.01  sim_bw_demodulated:                     3
% 3.40/1.01  sim_light_normalised:                   59
% 3.40/1.01  sim_joinable_taut:                      0
% 3.40/1.01  sim_joinable_simp:                      0
% 3.40/1.01  sim_ac_normalised:                      0
% 3.40/1.01  sim_smt_subsumption:                    0
% 3.40/1.01  
%------------------------------------------------------------------------------
