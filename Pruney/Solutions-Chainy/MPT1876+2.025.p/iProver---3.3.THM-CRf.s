%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:52 EST 2020

% Result     : Theorem 3.81s
% Output     : CNFRefutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :  247 (1463 expanded)
%              Number of clauses        :  156 ( 377 expanded)
%              Number of leaves         :   28 ( 335 expanded)
%              Depth                    :   24
%              Number of atoms          : 1028 (10452 expanded)
%              Number of equality atoms :  244 ( 547 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    5 (   1 average)

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
    inference(ennf_transformation,[],[f19])).

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

fof(f57,plain,(
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
    inference(flattening,[],[f57])).

fof(f60,plain,(
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

fof(f59,plain,
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

fof(f61,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f58,f60,f59])).

fof(f91,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f61])).

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
    inference(ennf_transformation,[],[f22])).

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

fof(f55,plain,(
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

fof(f56,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f44,f55])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK2(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f87,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f86,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f89,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f90,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f61])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f63,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f93,plain,
    ( ~ v1_zfmisc_1(sK4)
    | ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f61])).

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
    inference(ennf_transformation,[],[f13])).

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

fof(f76,plain,(
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

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f69,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f71,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f70,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f74,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f88,plain,(
    v2_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f84,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK2(X0,X1)) = X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

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

fof(f39,plain,(
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
    inference(flattening,[],[f39])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK1(X0,X1)) = X1
        & m1_pre_topc(sK1(X0,X1),X0)
        & ~ v2_struct_0(sK1(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK1(X0,X1)) = X1
            & m1_pre_topc(sK1(X0,X1),X0)
            & ~ v2_struct_0(sK1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f40,f53])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f79,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f80,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f92,plain,
    ( v1_zfmisc_1(sK4)
    | v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1771,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_11549,plain,
    ( v2_tex_2(X0,X1)
    | ~ v2_tex_2(k1_tarski(sK0(sK4)),X2)
    | X1 != X2
    | X0 != k1_tarski(sK0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1771])).

cnf(c_15262,plain,
    ( ~ v2_tex_2(k1_tarski(sK0(sK4)),X0)
    | v2_tex_2(sK4,X1)
    | X1 != X0
    | sK4 != k1_tarski(sK0(sK4)) ),
    inference(instantiation,[status(thm)],[c_11549])).

cnf(c_15264,plain,
    ( ~ v2_tex_2(k1_tarski(sK0(sK4)),sK3)
    | v2_tex_2(sK4,sK3)
    | sK3 != sK3
    | sK4 != k1_tarski(sK0(sK4)) ),
    inference(instantiation,[status(thm)],[c_15262])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2341,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_20,plain,
    ( ~ v2_tex_2(X0,X1)
    | m1_pre_topc(sK2(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_746,plain,
    ( ~ v2_tex_2(X0,X1)
    | m1_pre_topc(sK2(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_30])).

cnf(c_747,plain,
    ( ~ v2_tex_2(X0,sK3)
    | m1_pre_topc(sK2(sK3,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_746])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_751,plain,
    ( ~ v2_tex_2(X0,sK3)
    | m1_pre_topc(sK2(sK3,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_747,c_31,c_28])).

cnf(c_2332,plain,
    ( v2_tex_2(X0,sK3) != iProver_top
    | m1_pre_topc(sK2(sK3,X0),sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_751])).

cnf(c_3128,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | m1_pre_topc(sK2(sK3,sK4),sK3) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2341,c_2332])).

cnf(c_27,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_36,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3240,plain,
    ( m1_pre_topc(sK2(sK3,sK4),sK3) = iProver_top
    | v2_tex_2(sK4,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3128,c_36])).

cnf(c_3241,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | m1_pre_topc(sK2(sK3,sK4),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_3240])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_5,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_452,plain,
    ( m1_subset_1(X0,X1)
    | v1_xboole_0(X2)
    | X1 != X2
    | sK0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_5])).

cnf(c_453,plain,
    ( m1_subset_1(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_452])).

cnf(c_2336,plain,
    ( m1_subset_1(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_453])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2348,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4285,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(X0)),u1_struct_0(X1)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2336,c_2348])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2347,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6091,plain,
    ( k6_domain_1(u1_struct_0(X0),sK0(u1_struct_0(X1))) = k1_tarski(sK0(u1_struct_0(X1)))
    | m1_pre_topc(X1,X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X1)) = iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4285,c_2347])).

cnf(c_8219,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(u1_struct_0(sK2(sK3,sK4)))) = k1_tarski(sK0(u1_struct_0(sK2(sK3,sK4))))
    | v2_tex_2(sK4,sK3) != iProver_top
    | v2_struct_0(sK2(sK3,sK4)) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2(sK3,sK4))) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3241,c_6091])).

cnf(c_24,negated_conjecture,
    ( ~ v2_tex_2(sK4,sK3)
    | ~ v1_zfmisc_1(sK4) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_39,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v1_zfmisc_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_7,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_9,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_408,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_7,c_9])).

cnf(c_484,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_13,c_408])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_488,plain,
    ( v1_zfmisc_1(u1_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v1_tdlat_3(X0)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_484,c_8])).

cnf(c_489,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_488])).

cnf(c_12,plain,
    ( ~ v2_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_508,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_489,c_12])).

cnf(c_29,negated_conjecture,
    ( v2_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_529,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_508,c_29])).

cnf(c_530,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_529])).

cnf(c_534,plain,
    ( v1_zfmisc_1(u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK3)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_530,c_31,c_28])).

cnf(c_535,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0)) ),
    inference(renaming,[status(thm)],[c_534])).

cnf(c_21,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tdlat_3(sK2(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_722,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tdlat_3(sK2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_30])).

cnf(c_723,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_tdlat_3(sK2(sK3,X0))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_722])).

cnf(c_727,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_tdlat_3(sK2(sK3,X0))
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_723,c_31,c_28])).

cnf(c_817,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_pre_topc(X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(X1)
    | v1_zfmisc_1(u1_struct_0(X1))
    | v1_xboole_0(X0)
    | sK2(sK3,X0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_535,c_727])).

cnf(c_818,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_pre_topc(sK2(sK3,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK2(sK3,X0))
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_817])).

cnf(c_22,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK2(X1,X0))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_698,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK2(X1,X0))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_30])).

cnf(c_699,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_struct_0(sK2(sK3,X0))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_698])).

cnf(c_703,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_struct_0(sK2(sK3,X0))
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_699,c_31,c_28])).

cnf(c_822,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_tex_2(X0,sK3)
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_818,c_703,c_751])).

cnf(c_823,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_822])).

cnf(c_2330,plain,
    ( v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0))) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_823])).

cnf(c_2685,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2341,c_2330])).

cnf(c_1758,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2724,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1758])).

cnf(c_19,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK2(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_770,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK2(X1,X0)) = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_771,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(X0)
    | u1_struct_0(sK2(sK3,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_770])).

cnf(c_775,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(X0)
    | u1_struct_0(sK2(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_771,c_31,c_28])).

cnf(c_2331,plain,
    ( u1_struct_0(sK2(sK3,X0)) = X0
    | v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_775])).

cnf(c_3035,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | v2_tex_2(sK4,sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2341,c_2331])).

cnf(c_1759,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2700,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_1759])).

cnf(c_2917,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2700])).

cnf(c_3075,plain,
    ( u1_struct_0(sK2(sK3,sK4)) != sK4
    | sK4 = u1_struct_0(sK2(sK3,sK4))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2917])).

cnf(c_1767,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_zfmisc_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2851,plain,
    ( v1_zfmisc_1(X0)
    | ~ v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
    | X0 != u1_struct_0(sK2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1767])).

cnf(c_4078,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
    | v1_zfmisc_1(sK4)
    | sK4 != u1_struct_0(sK2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2851])).

cnf(c_4079,plain,
    ( sK4 != u1_struct_0(sK2(sK3,sK4))
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) != iProver_top
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4078])).

cnf(c_8542,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8219,c_36,c_39,c_2685,c_2724,c_3035,c_3075,c_4079])).

cnf(c_8544,plain,
    ( ~ v2_tex_2(sK4,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8542])).

cnf(c_16,plain,
    ( m1_pre_topc(sK1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2345,plain,
    ( m1_pre_topc(sK1(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3210,plain,
    ( m1_pre_topc(sK1(sK3,sK4),sK3) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2341,c_2345])).

cnf(c_32,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_35,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_37,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2659,plain,
    ( m1_pre_topc(sK1(X0,sK4),X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2660,plain,
    ( m1_pre_topc(sK1(X0,sK4),X0) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2659])).

cnf(c_2662,plain,
    ( m1_pre_topc(sK1(sK3,sK4),sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2660])).

cnf(c_3425,plain,
    ( m1_pre_topc(sK1(sK3,sK4),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3210,c_32,c_35,c_36,c_37,c_2662])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2346,plain,
    ( u1_struct_0(sK1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3136,plain,
    ( u1_struct_0(sK1(sK3,sK4)) = sK4
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2341,c_2346])).

cnf(c_2649,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(sK4)
    | u1_struct_0(sK1(X0,sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2651,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(sK4)
    | u1_struct_0(sK1(sK3,sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_2649])).

cnf(c_3284,plain,
    ( u1_struct_0(sK1(sK3,sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3136,c_31,c_28,c_27,c_26,c_2651])).

cnf(c_3287,plain,
    ( m1_pre_topc(sK1(sK3,sK4),X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) = iProver_top
    | m1_subset_1(X1,sK4) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1(sK3,sK4)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3284,c_2348])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK1(X1,X0))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2639,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK1(X0,sK4))
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2640,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1(X0,sK4)) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2639])).

cnf(c_2642,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK1(sK3,sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2640])).

cnf(c_4245,plain,
    ( v2_struct_0(X0) = iProver_top
    | m1_subset_1(X1,sK4) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) = iProver_top
    | m1_pre_topc(sK1(sK3,sK4),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3287,c_32,c_35,c_36,c_37,c_2642])).

cnf(c_4246,plain,
    ( m1_pre_topc(sK1(sK3,sK4),X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) = iProver_top
    | m1_subset_1(X1,sK4) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4245])).

cnf(c_4256,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(X0,sK4) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3425,c_4246])).

cnf(c_4514,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4256,c_32,c_35])).

cnf(c_4523,plain,
    ( k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0)
    | m1_subset_1(X0,sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4514,c_2347])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2590,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2697,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2590])).

cnf(c_2698,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2697])).

cnf(c_4996,plain,
    ( m1_subset_1(X0,sK4) != iProver_top
    | k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4523,c_36,c_37,c_2698])).

cnf(c_4997,plain,
    ( k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0)
    | m1_subset_1(X0,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_4996])).

cnf(c_5004,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k1_tarski(sK0(sK4))
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2336,c_4997])).

cnf(c_2574,plain,
    ( m1_subset_1(sK0(sK4),sK4)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_453])).

cnf(c_2641,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_struct_0(sK1(sK3,sK4))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2639])).

cnf(c_2661,plain,
    ( m1_pre_topc(sK1(sK3,sK4),sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2659])).

cnf(c_3068,plain,
    ( sK0(sK4) = sK0(sK4) ),
    inference(instantiation,[status(thm)],[c_1758])).

cnf(c_1763,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2687,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK0(sK4),sK4)
    | X0 != sK0(sK4)
    | X1 != sK4 ),
    inference(instantiation,[status(thm)],[c_1763])).

cnf(c_2876,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1(X1,sK4)))
    | ~ m1_subset_1(sK0(sK4),sK4)
    | X0 != sK0(sK4)
    | u1_struct_0(sK1(X1,sK4)) != sK4 ),
    inference(instantiation,[status(thm)],[c_2687])).

cnf(c_3249,plain,
    ( m1_subset_1(sK0(sK4),u1_struct_0(sK1(X0,sK4)))
    | ~ m1_subset_1(sK0(sK4),sK4)
    | u1_struct_0(sK1(X0,sK4)) != sK4
    | sK0(sK4) != sK0(sK4) ),
    inference(instantiation,[status(thm)],[c_2876])).

cnf(c_3253,plain,
    ( m1_subset_1(sK0(sK4),u1_struct_0(sK1(sK3,sK4)))
    | ~ m1_subset_1(sK0(sK4),sK4)
    | u1_struct_0(sK1(sK3,sK4)) != sK4
    | sK0(sK4) != sK0(sK4) ),
    inference(instantiation,[status(thm)],[c_3249])).

cnf(c_2803,plain,
    ( ~ m1_pre_topc(sK1(X0,sK4),X0)
    | m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK1(X0,sK4)))
    | v2_struct_0(X0)
    | v2_struct_0(sK1(X0,sK4))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3811,plain,
    ( ~ m1_pre_topc(sK1(X0,sK4),X0)
    | m1_subset_1(sK0(sK4),u1_struct_0(X0))
    | ~ m1_subset_1(sK0(sK4),u1_struct_0(sK1(X0,sK4)))
    | v2_struct_0(X0)
    | v2_struct_0(sK1(X0,sK4))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_2803])).

cnf(c_3813,plain,
    ( ~ m1_pre_topc(sK1(sK3,sK4),sK3)
    | ~ m1_subset_1(sK0(sK4),u1_struct_0(sK1(sK3,sK4)))
    | m1_subset_1(sK0(sK4),u1_struct_0(sK3))
    | v2_struct_0(sK1(sK3,sK4))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_3811])).

cnf(c_2781,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_4441,plain,
    ( ~ m1_subset_1(sK0(sK4),u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k1_tarski(sK0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2781])).

cnf(c_5712,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k1_tarski(sK0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5004,c_31,c_28,c_27,c_26,c_2574,c_2641,c_2651,c_2661,c_2697,c_3068,c_3253,c_3813,c_4441])).

cnf(c_23,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_680,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_681,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_680])).

cnf(c_685,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_681,c_31,c_28])).

cnf(c_2334,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_685])).

cnf(c_5715,plain,
    ( v2_tex_2(k1_tarski(sK0(sK4)),sK3) = iProver_top
    | m1_subset_1(sK0(sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5712,c_2334])).

cnf(c_5716,plain,
    ( v2_tex_2(k1_tarski(sK0(sK4)),sK3)
    | ~ m1_subset_1(sK0(sK4),u1_struct_0(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5715])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_4221,plain,
    ( ~ v1_xboole_0(k1_tarski(sK0(sK4))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4222,plain,
    ( v1_xboole_0(k1_tarski(sK0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4221])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_426,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_6,c_18])).

cnf(c_430,plain,
    ( v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_426,c_4])).

cnf(c_431,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | X1 = X0 ),
    inference(renaming,[status(thm)],[c_430])).

cnf(c_2624,plain,
    ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(k1_tarski(X0))
    | X1 = k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_431])).

cnf(c_3166,plain,
    ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK4))
    | ~ v1_zfmisc_1(sK4)
    | v1_xboole_0(k1_tarski(X0))
    | sK4 = k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_2624])).

cnf(c_3738,plain,
    ( ~ m1_subset_1(k1_tarski(sK0(sK4)),k1_zfmisc_1(sK4))
    | ~ v1_zfmisc_1(sK4)
    | v1_xboole_0(k1_tarski(sK0(sK4)))
    | sK4 = k1_tarski(sK0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3166])).

cnf(c_3741,plain,
    ( sK4 = k1_tarski(sK0(sK4))
    | m1_subset_1(k1_tarski(sK0(sK4)),k1_zfmisc_1(sK4)) != iProver_top
    | v1_zfmisc_1(sK4) != iProver_top
    | v1_xboole_0(k1_tarski(sK0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3738])).

cnf(c_3,plain,
    ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_464,plain,
    ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X2)
    | X1 != X2
    | sK0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_3])).

cnf(c_465,plain,
    ( m1_subset_1(k1_tarski(sK0(X0)),k1_zfmisc_1(X0))
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_464])).

cnf(c_2582,plain,
    ( m1_subset_1(k1_tarski(sK0(sK4)),k1_zfmisc_1(sK4))
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_465])).

cnf(c_2583,plain,
    ( m1_subset_1(k1_tarski(sK0(sK4)),k1_zfmisc_1(sK4)) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2582])).

cnf(c_1785,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1758])).

cnf(c_25,negated_conjecture,
    ( v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_38,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15264,c_8544,c_8542,c_5716,c_4222,c_3813,c_3741,c_3253,c_3068,c_2661,c_2651,c_2641,c_2583,c_2574,c_1785,c_38,c_26,c_36,c_27,c_28,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:55:36 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.81/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.81/0.98  
% 3.81/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.81/0.98  
% 3.81/0.98  ------  iProver source info
% 3.81/0.98  
% 3.81/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.81/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.81/0.98  git: non_committed_changes: false
% 3.81/0.98  git: last_make_outside_of_git: false
% 3.81/0.98  
% 3.81/0.98  ------ 
% 3.81/0.98  
% 3.81/0.98  ------ Input Options
% 3.81/0.98  
% 3.81/0.98  --out_options                           all
% 3.81/0.98  --tptp_safe_out                         true
% 3.81/0.98  --problem_path                          ""
% 3.81/0.98  --include_path                          ""
% 3.81/0.98  --clausifier                            res/vclausify_rel
% 3.81/0.98  --clausifier_options                    --mode clausify
% 3.81/0.98  --stdin                                 false
% 3.81/0.98  --stats_out                             all
% 3.81/0.98  
% 3.81/0.98  ------ General Options
% 3.81/0.98  
% 3.81/0.98  --fof                                   false
% 3.81/0.98  --time_out_real                         305.
% 3.81/0.98  --time_out_virtual                      -1.
% 3.81/0.98  --symbol_type_check                     false
% 3.81/0.98  --clausify_out                          false
% 3.81/0.98  --sig_cnt_out                           false
% 3.81/0.98  --trig_cnt_out                          false
% 3.81/0.98  --trig_cnt_out_tolerance                1.
% 3.81/0.98  --trig_cnt_out_sk_spl                   false
% 3.81/0.98  --abstr_cl_out                          false
% 3.81/0.98  
% 3.81/0.98  ------ Global Options
% 3.81/0.98  
% 3.81/0.98  --schedule                              default
% 3.81/0.98  --add_important_lit                     false
% 3.81/0.98  --prop_solver_per_cl                    1000
% 3.81/0.98  --min_unsat_core                        false
% 3.81/0.98  --soft_assumptions                      false
% 3.81/0.98  --soft_lemma_size                       3
% 3.81/0.98  --prop_impl_unit_size                   0
% 3.81/0.98  --prop_impl_unit                        []
% 3.81/0.98  --share_sel_clauses                     true
% 3.81/0.98  --reset_solvers                         false
% 3.81/0.98  --bc_imp_inh                            [conj_cone]
% 3.81/0.98  --conj_cone_tolerance                   3.
% 3.81/0.98  --extra_neg_conj                        none
% 3.81/0.98  --large_theory_mode                     true
% 3.81/0.98  --prolific_symb_bound                   200
% 3.81/0.98  --lt_threshold                          2000
% 3.81/0.98  --clause_weak_htbl                      true
% 3.81/0.98  --gc_record_bc_elim                     false
% 3.81/0.98  
% 3.81/0.98  ------ Preprocessing Options
% 3.81/0.98  
% 3.81/0.98  --preprocessing_flag                    true
% 3.81/0.98  --time_out_prep_mult                    0.1
% 3.81/0.98  --splitting_mode                        input
% 3.81/0.98  --splitting_grd                         true
% 3.81/0.98  --splitting_cvd                         false
% 3.81/0.98  --splitting_cvd_svl                     false
% 3.81/0.98  --splitting_nvd                         32
% 3.81/0.98  --sub_typing                            true
% 3.81/0.98  --prep_gs_sim                           true
% 3.81/0.98  --prep_unflatten                        true
% 3.81/0.98  --prep_res_sim                          true
% 3.81/0.98  --prep_upred                            true
% 3.81/0.98  --prep_sem_filter                       exhaustive
% 3.81/0.98  --prep_sem_filter_out                   false
% 3.81/0.98  --pred_elim                             true
% 3.81/0.98  --res_sim_input                         true
% 3.81/0.98  --eq_ax_congr_red                       true
% 3.81/0.98  --pure_diseq_elim                       true
% 3.81/0.98  --brand_transform                       false
% 3.81/0.98  --non_eq_to_eq                          false
% 3.81/0.98  --prep_def_merge                        true
% 3.81/0.98  --prep_def_merge_prop_impl              false
% 3.81/0.98  --prep_def_merge_mbd                    true
% 3.81/0.98  --prep_def_merge_tr_red                 false
% 3.81/0.98  --prep_def_merge_tr_cl                  false
% 3.81/0.98  --smt_preprocessing                     true
% 3.81/0.98  --smt_ac_axioms                         fast
% 3.81/0.98  --preprocessed_out                      false
% 3.81/0.98  --preprocessed_stats                    false
% 3.81/0.98  
% 3.81/0.98  ------ Abstraction refinement Options
% 3.81/0.98  
% 3.81/0.98  --abstr_ref                             []
% 3.81/0.98  --abstr_ref_prep                        false
% 3.81/0.98  --abstr_ref_until_sat                   false
% 3.81/0.98  --abstr_ref_sig_restrict                funpre
% 3.81/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.81/0.98  --abstr_ref_under                       []
% 3.81/0.98  
% 3.81/0.98  ------ SAT Options
% 3.81/0.98  
% 3.81/0.98  --sat_mode                              false
% 3.81/0.98  --sat_fm_restart_options                ""
% 3.81/0.98  --sat_gr_def                            false
% 3.81/0.98  --sat_epr_types                         true
% 3.81/0.98  --sat_non_cyclic_types                  false
% 3.81/0.98  --sat_finite_models                     false
% 3.81/0.98  --sat_fm_lemmas                         false
% 3.81/0.98  --sat_fm_prep                           false
% 3.81/0.98  --sat_fm_uc_incr                        true
% 3.81/0.98  --sat_out_model                         small
% 3.81/0.98  --sat_out_clauses                       false
% 3.81/0.98  
% 3.81/0.98  ------ QBF Options
% 3.81/0.98  
% 3.81/0.98  --qbf_mode                              false
% 3.81/0.98  --qbf_elim_univ                         false
% 3.81/0.98  --qbf_dom_inst                          none
% 3.81/0.98  --qbf_dom_pre_inst                      false
% 3.81/0.98  --qbf_sk_in                             false
% 3.81/0.98  --qbf_pred_elim                         true
% 3.81/0.98  --qbf_split                             512
% 3.81/0.98  
% 3.81/0.98  ------ BMC1 Options
% 3.81/0.98  
% 3.81/0.98  --bmc1_incremental                      false
% 3.81/0.98  --bmc1_axioms                           reachable_all
% 3.81/0.98  --bmc1_min_bound                        0
% 3.81/0.98  --bmc1_max_bound                        -1
% 3.81/0.98  --bmc1_max_bound_default                -1
% 3.81/0.98  --bmc1_symbol_reachability              true
% 3.81/0.98  --bmc1_property_lemmas                  false
% 3.81/0.98  --bmc1_k_induction                      false
% 3.81/0.98  --bmc1_non_equiv_states                 false
% 3.81/0.98  --bmc1_deadlock                         false
% 3.81/0.98  --bmc1_ucm                              false
% 3.81/0.98  --bmc1_add_unsat_core                   none
% 3.81/0.98  --bmc1_unsat_core_children              false
% 3.81/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.81/0.98  --bmc1_out_stat                         full
% 3.81/0.98  --bmc1_ground_init                      false
% 3.81/0.98  --bmc1_pre_inst_next_state              false
% 3.81/0.98  --bmc1_pre_inst_state                   false
% 3.81/0.98  --bmc1_pre_inst_reach_state             false
% 3.81/0.98  --bmc1_out_unsat_core                   false
% 3.81/0.98  --bmc1_aig_witness_out                  false
% 3.81/0.98  --bmc1_verbose                          false
% 3.81/0.98  --bmc1_dump_clauses_tptp                false
% 3.81/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.81/0.98  --bmc1_dump_file                        -
% 3.81/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.81/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.81/0.98  --bmc1_ucm_extend_mode                  1
% 3.81/0.98  --bmc1_ucm_init_mode                    2
% 3.81/0.98  --bmc1_ucm_cone_mode                    none
% 3.81/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.81/0.98  --bmc1_ucm_relax_model                  4
% 3.81/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.81/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.81/0.98  --bmc1_ucm_layered_model                none
% 3.81/0.98  --bmc1_ucm_max_lemma_size               10
% 3.81/0.98  
% 3.81/0.98  ------ AIG Options
% 3.81/0.98  
% 3.81/0.98  --aig_mode                              false
% 3.81/0.98  
% 3.81/0.98  ------ Instantiation Options
% 3.81/0.98  
% 3.81/0.98  --instantiation_flag                    true
% 3.81/0.98  --inst_sos_flag                         false
% 3.81/0.98  --inst_sos_phase                        true
% 3.81/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.81/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.81/0.98  --inst_lit_sel_side                     num_symb
% 3.81/0.98  --inst_solver_per_active                1400
% 3.81/0.98  --inst_solver_calls_frac                1.
% 3.81/0.98  --inst_passive_queue_type               priority_queues
% 3.81/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.81/0.98  --inst_passive_queues_freq              [25;2]
% 3.81/0.98  --inst_dismatching                      true
% 3.81/0.98  --inst_eager_unprocessed_to_passive     true
% 3.81/0.98  --inst_prop_sim_given                   true
% 3.81/0.98  --inst_prop_sim_new                     false
% 3.81/0.98  --inst_subs_new                         false
% 3.81/0.98  --inst_eq_res_simp                      false
% 3.81/0.98  --inst_subs_given                       false
% 3.81/0.98  --inst_orphan_elimination               true
% 3.81/0.98  --inst_learning_loop_flag               true
% 3.81/0.98  --inst_learning_start                   3000
% 3.81/0.98  --inst_learning_factor                  2
% 3.81/0.98  --inst_start_prop_sim_after_learn       3
% 3.81/0.98  --inst_sel_renew                        solver
% 3.81/0.98  --inst_lit_activity_flag                true
% 3.81/0.98  --inst_restr_to_given                   false
% 3.81/0.98  --inst_activity_threshold               500
% 3.81/0.98  --inst_out_proof                        true
% 3.81/0.98  
% 3.81/0.98  ------ Resolution Options
% 3.81/0.98  
% 3.81/0.98  --resolution_flag                       true
% 3.81/0.98  --res_lit_sel                           adaptive
% 3.81/0.98  --res_lit_sel_side                      none
% 3.81/0.98  --res_ordering                          kbo
% 3.81/0.98  --res_to_prop_solver                    active
% 3.81/0.98  --res_prop_simpl_new                    false
% 3.81/0.98  --res_prop_simpl_given                  true
% 3.81/0.98  --res_passive_queue_type                priority_queues
% 3.81/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.81/0.98  --res_passive_queues_freq               [15;5]
% 3.81/0.98  --res_forward_subs                      full
% 3.81/0.98  --res_backward_subs                     full
% 3.81/0.98  --res_forward_subs_resolution           true
% 3.81/0.98  --res_backward_subs_resolution          true
% 3.81/0.98  --res_orphan_elimination                true
% 3.81/0.98  --res_time_limit                        2.
% 3.81/0.98  --res_out_proof                         true
% 3.81/0.98  
% 3.81/0.98  ------ Superposition Options
% 3.81/0.98  
% 3.81/0.98  --superposition_flag                    true
% 3.81/0.98  --sup_passive_queue_type                priority_queues
% 3.81/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.81/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.81/0.98  --demod_completeness_check              fast
% 3.81/0.98  --demod_use_ground                      true
% 3.81/0.98  --sup_to_prop_solver                    passive
% 3.81/0.98  --sup_prop_simpl_new                    true
% 3.81/0.98  --sup_prop_simpl_given                  true
% 3.81/0.98  --sup_fun_splitting                     false
% 3.81/0.98  --sup_smt_interval                      50000
% 3.81/0.98  
% 3.81/0.98  ------ Superposition Simplification Setup
% 3.81/0.98  
% 3.81/0.98  --sup_indices_passive                   []
% 3.81/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.81/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/0.98  --sup_full_bw                           [BwDemod]
% 3.81/0.98  --sup_immed_triv                        [TrivRules]
% 3.81/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.81/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/0.98  --sup_immed_bw_main                     []
% 3.81/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.81/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.81/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.81/0.98  
% 3.81/0.98  ------ Combination Options
% 3.81/0.98  
% 3.81/0.98  --comb_res_mult                         3
% 3.81/0.98  --comb_sup_mult                         2
% 3.81/0.98  --comb_inst_mult                        10
% 3.81/0.98  
% 3.81/0.98  ------ Debug Options
% 3.81/0.98  
% 3.81/0.98  --dbg_backtrace                         false
% 3.81/0.98  --dbg_dump_prop_clauses                 false
% 3.81/0.98  --dbg_dump_prop_clauses_file            -
% 3.81/0.98  --dbg_out_stat                          false
% 3.81/0.98  ------ Parsing...
% 3.81/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.81/0.98  
% 3.81/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.81/0.98  
% 3.81/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.81/0.98  
% 3.81/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.81/0.98  ------ Proving...
% 3.81/0.98  ------ Problem Properties 
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  clauses                                 22
% 3.81/0.98  conjectures                             6
% 3.81/0.98  EPR                                     6
% 3.81/0.98  Horn                                    10
% 3.81/0.98  unary                                   5
% 3.81/0.98  binary                                  5
% 3.81/0.98  lits                                    65
% 3.81/0.98  lits eq                                 4
% 3.81/0.98  fd_pure                                 0
% 3.81/0.98  fd_pseudo                               0
% 3.81/0.98  fd_cond                                 0
% 3.81/0.98  fd_pseudo_cond                          1
% 3.81/0.98  AC symbols                              0
% 3.81/0.98  
% 3.81/0.98  ------ Schedule dynamic 5 is on 
% 3.81/0.98  
% 3.81/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  ------ 
% 3.81/0.98  Current options:
% 3.81/0.98  ------ 
% 3.81/0.98  
% 3.81/0.98  ------ Input Options
% 3.81/0.98  
% 3.81/0.98  --out_options                           all
% 3.81/0.98  --tptp_safe_out                         true
% 3.81/0.98  --problem_path                          ""
% 3.81/0.98  --include_path                          ""
% 3.81/0.98  --clausifier                            res/vclausify_rel
% 3.81/0.98  --clausifier_options                    --mode clausify
% 3.81/0.98  --stdin                                 false
% 3.81/0.98  --stats_out                             all
% 3.81/0.98  
% 3.81/0.98  ------ General Options
% 3.81/0.98  
% 3.81/0.98  --fof                                   false
% 3.81/0.98  --time_out_real                         305.
% 3.81/0.98  --time_out_virtual                      -1.
% 3.81/0.98  --symbol_type_check                     false
% 3.81/0.98  --clausify_out                          false
% 3.81/0.98  --sig_cnt_out                           false
% 3.81/0.98  --trig_cnt_out                          false
% 3.81/0.98  --trig_cnt_out_tolerance                1.
% 3.81/0.98  --trig_cnt_out_sk_spl                   false
% 3.81/0.98  --abstr_cl_out                          false
% 3.81/0.98  
% 3.81/0.98  ------ Global Options
% 3.81/0.98  
% 3.81/0.98  --schedule                              default
% 3.81/0.98  --add_important_lit                     false
% 3.81/0.98  --prop_solver_per_cl                    1000
% 3.81/0.98  --min_unsat_core                        false
% 3.81/0.98  --soft_assumptions                      false
% 3.81/0.98  --soft_lemma_size                       3
% 3.81/0.98  --prop_impl_unit_size                   0
% 3.81/0.98  --prop_impl_unit                        []
% 3.81/0.98  --share_sel_clauses                     true
% 3.81/0.98  --reset_solvers                         false
% 3.81/0.98  --bc_imp_inh                            [conj_cone]
% 3.81/0.98  --conj_cone_tolerance                   3.
% 3.81/0.98  --extra_neg_conj                        none
% 3.81/0.98  --large_theory_mode                     true
% 3.81/0.98  --prolific_symb_bound                   200
% 3.81/0.98  --lt_threshold                          2000
% 3.81/0.98  --clause_weak_htbl                      true
% 3.81/0.98  --gc_record_bc_elim                     false
% 3.81/0.98  
% 3.81/0.98  ------ Preprocessing Options
% 3.81/0.98  
% 3.81/0.98  --preprocessing_flag                    true
% 3.81/0.98  --time_out_prep_mult                    0.1
% 3.81/0.98  --splitting_mode                        input
% 3.81/0.98  --splitting_grd                         true
% 3.81/0.98  --splitting_cvd                         false
% 3.81/0.98  --splitting_cvd_svl                     false
% 3.81/0.98  --splitting_nvd                         32
% 3.81/0.98  --sub_typing                            true
% 3.81/0.98  --prep_gs_sim                           true
% 3.81/0.98  --prep_unflatten                        true
% 3.81/0.98  --prep_res_sim                          true
% 3.81/0.98  --prep_upred                            true
% 3.81/0.98  --prep_sem_filter                       exhaustive
% 3.81/0.98  --prep_sem_filter_out                   false
% 3.81/0.98  --pred_elim                             true
% 3.81/0.98  --res_sim_input                         true
% 3.81/0.98  --eq_ax_congr_red                       true
% 3.81/0.98  --pure_diseq_elim                       true
% 3.81/0.98  --brand_transform                       false
% 3.81/0.98  --non_eq_to_eq                          false
% 3.81/0.98  --prep_def_merge                        true
% 3.81/0.98  --prep_def_merge_prop_impl              false
% 3.81/0.98  --prep_def_merge_mbd                    true
% 3.81/0.98  --prep_def_merge_tr_red                 false
% 3.81/0.98  --prep_def_merge_tr_cl                  false
% 3.81/0.98  --smt_preprocessing                     true
% 3.81/0.98  --smt_ac_axioms                         fast
% 3.81/0.98  --preprocessed_out                      false
% 3.81/0.98  --preprocessed_stats                    false
% 3.81/0.98  
% 3.81/0.98  ------ Abstraction refinement Options
% 3.81/0.98  
% 3.81/0.98  --abstr_ref                             []
% 3.81/0.98  --abstr_ref_prep                        false
% 3.81/0.98  --abstr_ref_until_sat                   false
% 3.81/0.98  --abstr_ref_sig_restrict                funpre
% 3.81/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.81/0.98  --abstr_ref_under                       []
% 3.81/0.98  
% 3.81/0.98  ------ SAT Options
% 3.81/0.98  
% 3.81/0.98  --sat_mode                              false
% 3.81/0.98  --sat_fm_restart_options                ""
% 3.81/0.98  --sat_gr_def                            false
% 3.81/0.98  --sat_epr_types                         true
% 3.81/0.98  --sat_non_cyclic_types                  false
% 3.81/0.98  --sat_finite_models                     false
% 3.81/0.98  --sat_fm_lemmas                         false
% 3.81/0.98  --sat_fm_prep                           false
% 3.81/0.98  --sat_fm_uc_incr                        true
% 3.81/0.98  --sat_out_model                         small
% 3.81/0.98  --sat_out_clauses                       false
% 3.81/0.98  
% 3.81/0.98  ------ QBF Options
% 3.81/0.98  
% 3.81/0.98  --qbf_mode                              false
% 3.81/0.98  --qbf_elim_univ                         false
% 3.81/0.98  --qbf_dom_inst                          none
% 3.81/0.98  --qbf_dom_pre_inst                      false
% 3.81/0.98  --qbf_sk_in                             false
% 3.81/0.98  --qbf_pred_elim                         true
% 3.81/0.98  --qbf_split                             512
% 3.81/0.98  
% 3.81/0.98  ------ BMC1 Options
% 3.81/0.98  
% 3.81/0.98  --bmc1_incremental                      false
% 3.81/0.98  --bmc1_axioms                           reachable_all
% 3.81/0.98  --bmc1_min_bound                        0
% 3.81/0.98  --bmc1_max_bound                        -1
% 3.81/0.98  --bmc1_max_bound_default                -1
% 3.81/0.98  --bmc1_symbol_reachability              true
% 3.81/0.98  --bmc1_property_lemmas                  false
% 3.81/0.98  --bmc1_k_induction                      false
% 3.81/0.98  --bmc1_non_equiv_states                 false
% 3.81/0.98  --bmc1_deadlock                         false
% 3.81/0.98  --bmc1_ucm                              false
% 3.81/0.98  --bmc1_add_unsat_core                   none
% 3.81/0.98  --bmc1_unsat_core_children              false
% 3.81/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.81/0.98  --bmc1_out_stat                         full
% 3.81/0.98  --bmc1_ground_init                      false
% 3.81/0.98  --bmc1_pre_inst_next_state              false
% 3.81/0.98  --bmc1_pre_inst_state                   false
% 3.81/0.98  --bmc1_pre_inst_reach_state             false
% 3.81/0.98  --bmc1_out_unsat_core                   false
% 3.81/0.98  --bmc1_aig_witness_out                  false
% 3.81/0.98  --bmc1_verbose                          false
% 3.81/0.98  --bmc1_dump_clauses_tptp                false
% 3.81/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.81/0.98  --bmc1_dump_file                        -
% 3.81/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.81/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.81/0.98  --bmc1_ucm_extend_mode                  1
% 3.81/0.98  --bmc1_ucm_init_mode                    2
% 3.81/0.98  --bmc1_ucm_cone_mode                    none
% 3.81/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.81/0.98  --bmc1_ucm_relax_model                  4
% 3.81/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.81/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.81/0.98  --bmc1_ucm_layered_model                none
% 3.81/0.98  --bmc1_ucm_max_lemma_size               10
% 3.81/0.98  
% 3.81/0.98  ------ AIG Options
% 3.81/0.98  
% 3.81/0.98  --aig_mode                              false
% 3.81/0.98  
% 3.81/0.98  ------ Instantiation Options
% 3.81/0.98  
% 3.81/0.98  --instantiation_flag                    true
% 3.81/0.98  --inst_sos_flag                         false
% 3.81/0.98  --inst_sos_phase                        true
% 3.81/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.81/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.81/0.98  --inst_lit_sel_side                     none
% 3.81/0.98  --inst_solver_per_active                1400
% 3.81/0.98  --inst_solver_calls_frac                1.
% 3.81/0.98  --inst_passive_queue_type               priority_queues
% 3.81/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.81/0.98  --inst_passive_queues_freq              [25;2]
% 3.81/0.98  --inst_dismatching                      true
% 3.81/0.98  --inst_eager_unprocessed_to_passive     true
% 3.81/0.98  --inst_prop_sim_given                   true
% 3.81/0.98  --inst_prop_sim_new                     false
% 3.81/0.98  --inst_subs_new                         false
% 3.81/0.98  --inst_eq_res_simp                      false
% 3.81/0.98  --inst_subs_given                       false
% 3.81/0.98  --inst_orphan_elimination               true
% 3.81/0.98  --inst_learning_loop_flag               true
% 3.81/0.98  --inst_learning_start                   3000
% 3.81/0.98  --inst_learning_factor                  2
% 3.81/0.98  --inst_start_prop_sim_after_learn       3
% 3.81/0.98  --inst_sel_renew                        solver
% 3.81/0.98  --inst_lit_activity_flag                true
% 3.81/0.98  --inst_restr_to_given                   false
% 3.81/0.98  --inst_activity_threshold               500
% 3.81/0.98  --inst_out_proof                        true
% 3.81/0.98  
% 3.81/0.98  ------ Resolution Options
% 3.81/0.98  
% 3.81/0.98  --resolution_flag                       false
% 3.81/0.98  --res_lit_sel                           adaptive
% 3.81/0.98  --res_lit_sel_side                      none
% 3.81/0.98  --res_ordering                          kbo
% 3.81/0.98  --res_to_prop_solver                    active
% 3.81/0.98  --res_prop_simpl_new                    false
% 3.81/0.98  --res_prop_simpl_given                  true
% 3.81/0.98  --res_passive_queue_type                priority_queues
% 3.81/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.81/0.98  --res_passive_queues_freq               [15;5]
% 3.81/0.98  --res_forward_subs                      full
% 3.81/0.98  --res_backward_subs                     full
% 3.81/0.98  --res_forward_subs_resolution           true
% 3.81/0.98  --res_backward_subs_resolution          true
% 3.81/0.98  --res_orphan_elimination                true
% 3.81/0.98  --res_time_limit                        2.
% 3.81/0.98  --res_out_proof                         true
% 3.81/0.98  
% 3.81/0.98  ------ Superposition Options
% 3.81/0.98  
% 3.81/0.98  --superposition_flag                    true
% 3.81/0.98  --sup_passive_queue_type                priority_queues
% 3.81/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.81/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.81/0.98  --demod_completeness_check              fast
% 3.81/0.98  --demod_use_ground                      true
% 3.81/0.98  --sup_to_prop_solver                    passive
% 3.81/0.98  --sup_prop_simpl_new                    true
% 3.81/0.98  --sup_prop_simpl_given                  true
% 3.81/0.98  --sup_fun_splitting                     false
% 3.81/0.98  --sup_smt_interval                      50000
% 3.81/0.98  
% 3.81/0.98  ------ Superposition Simplification Setup
% 3.81/0.98  
% 3.81/0.98  --sup_indices_passive                   []
% 3.81/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.81/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/0.98  --sup_full_bw                           [BwDemod]
% 3.81/0.98  --sup_immed_triv                        [TrivRules]
% 3.81/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.81/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/0.98  --sup_immed_bw_main                     []
% 3.81/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.81/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.81/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.81/0.98  
% 3.81/0.98  ------ Combination Options
% 3.81/0.98  
% 3.81/0.98  --comb_res_mult                         3
% 3.81/0.98  --comb_sup_mult                         2
% 3.81/0.98  --comb_inst_mult                        10
% 3.81/0.98  
% 3.81/0.98  ------ Debug Options
% 3.81/0.98  
% 3.81/0.98  --dbg_backtrace                         false
% 3.81/0.98  --dbg_dump_prop_clauses                 false
% 3.81/0.98  --dbg_dump_prop_clauses_file            -
% 3.81/0.98  --dbg_out_stat                          false
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  ------ Proving...
% 3.81/0.98  
% 3.81/0.98  
% 3.81/0.98  % SZS status Theorem for theBenchmark.p
% 3.81/0.98  
% 3.81/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.81/0.98  
% 3.81/0.98  fof(f18,conjecture,(
% 3.81/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 3.81/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f19,negated_conjecture,(
% 3.81/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 3.81/0.98    inference(negated_conjecture,[],[f18])).
% 3.81/0.98  
% 3.81/0.98  fof(f47,plain,(
% 3.81/0.98    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.81/0.98    inference(ennf_transformation,[],[f19])).
% 3.81/0.98  
% 3.81/0.98  fof(f48,plain,(
% 3.81/0.98    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.81/0.98    inference(flattening,[],[f47])).
% 3.81/0.98  
% 3.81/0.98  fof(f57,plain,(
% 3.81/0.98    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.81/0.98    inference(nnf_transformation,[],[f48])).
% 3.81/0.98  
% 3.81/0.98  fof(f58,plain,(
% 3.81/0.98    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.81/0.98    inference(flattening,[],[f57])).
% 3.81/0.98  
% 3.81/0.98  fof(f60,plain,(
% 3.81/0.98    ( ! [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,X0)) & (v1_zfmisc_1(sK4) | v2_tex_2(sK4,X0)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK4))) )),
% 3.81/0.98    introduced(choice_axiom,[])).
% 3.81/0.98  
% 3.81/0.98  fof(f59,plain,(
% 3.81/0.98    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK3)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 3.81/0.98    introduced(choice_axiom,[])).
% 3.81/0.98  
% 3.81/0.98  fof(f61,plain,(
% 3.81/0.98    ((~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3)) & (v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 3.81/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f58,f60,f59])).
% 3.81/0.98  
% 3.81/0.98  fof(f91,plain,(
% 3.81/0.98    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 3.81/0.98    inference(cnf_transformation,[],[f61])).
% 3.81/0.98  
% 3.81/0.98  fof(f16,axiom,(
% 3.81/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 3.81/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f22,plain,(
% 3.81/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 3.81/0.98    inference(pure_predicate_removal,[],[f16])).
% 3.81/0.98  
% 3.81/0.98  fof(f43,plain,(
% 3.81/0.98    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.81/0.98    inference(ennf_transformation,[],[f22])).
% 3.81/0.98  
% 3.81/0.98  fof(f44,plain,(
% 3.81/0.98    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.81/0.98    inference(flattening,[],[f43])).
% 3.81/0.98  
% 3.81/0.98  fof(f55,plain,(
% 3.81/0.98    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_tdlat_3(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))))),
% 3.81/0.98    introduced(choice_axiom,[])).
% 3.81/0.98  
% 3.81/0.98  fof(f56,plain,(
% 3.81/0.98    ! [X0] : (! [X1] : ((u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_tdlat_3(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.81/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f44,f55])).
% 3.81/0.98  
% 3.81/0.98  fof(f83,plain,(
% 3.81/0.98    ( ! [X0,X1] : (m1_pre_topc(sK2(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f56])).
% 3.81/0.98  
% 3.81/0.98  fof(f87,plain,(
% 3.81/0.98    v2_pre_topc(sK3)),
% 3.81/0.98    inference(cnf_transformation,[],[f61])).
% 3.81/0.98  
% 3.81/0.98  fof(f86,plain,(
% 3.81/0.98    ~v2_struct_0(sK3)),
% 3.81/0.98    inference(cnf_transformation,[],[f61])).
% 3.81/0.98  
% 3.81/0.98  fof(f89,plain,(
% 3.81/0.98    l1_pre_topc(sK3)),
% 3.81/0.98    inference(cnf_transformation,[],[f61])).
% 3.81/0.98  
% 3.81/0.98  fof(f90,plain,(
% 3.81/0.98    ~v1_xboole_0(sK4)),
% 3.81/0.98    inference(cnf_transformation,[],[f61])).
% 3.81/0.98  
% 3.81/0.98  fof(f1,axiom,(
% 3.81/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.81/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f49,plain,(
% 3.81/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.81/0.98    inference(nnf_transformation,[],[f1])).
% 3.81/0.98  
% 3.81/0.98  fof(f50,plain,(
% 3.81/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.81/0.98    inference(rectify,[],[f49])).
% 3.81/0.98  
% 3.81/0.98  fof(f51,plain,(
% 3.81/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.81/0.98    introduced(choice_axiom,[])).
% 3.81/0.98  
% 3.81/0.98  fof(f52,plain,(
% 3.81/0.98    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.81/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f50,f51])).
% 3.81/0.98  
% 3.81/0.98  fof(f63,plain,(
% 3.81/0.98    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f52])).
% 3.81/0.98  
% 3.81/0.98  fof(f5,axiom,(
% 3.81/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.81/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f25,plain,(
% 3.81/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.81/0.98    inference(ennf_transformation,[],[f5])).
% 3.81/0.98  
% 3.81/0.98  fof(f67,plain,(
% 3.81/0.98    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f25])).
% 3.81/0.98  
% 3.81/0.98  fof(f10,axiom,(
% 3.81/0.98    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 3.81/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f31,plain,(
% 3.81/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.81/0.98    inference(ennf_transformation,[],[f10])).
% 3.81/0.98  
% 3.81/0.98  fof(f32,plain,(
% 3.81/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.81/0.98    inference(flattening,[],[f31])).
% 3.81/0.98  
% 3.81/0.98  fof(f72,plain,(
% 3.81/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f32])).
% 3.81/0.98  
% 3.81/0.98  fof(f11,axiom,(
% 3.81/0.98    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 3.81/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f33,plain,(
% 3.81/0.98    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.81/0.98    inference(ennf_transformation,[],[f11])).
% 3.81/0.98  
% 3.81/0.98  fof(f34,plain,(
% 3.81/0.98    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.81/0.98    inference(flattening,[],[f33])).
% 3.81/0.98  
% 3.81/0.98  fof(f73,plain,(
% 3.81/0.98    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f34])).
% 3.81/0.98  
% 3.81/0.98  fof(f93,plain,(
% 3.81/0.98    ~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3)),
% 3.81/0.98    inference(cnf_transformation,[],[f61])).
% 3.81/0.98  
% 3.81/0.98  fof(f13,axiom,(
% 3.81/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((~v7_struct_0(X1) & ~v2_struct_0(X1)) => (~v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 3.81/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f37,plain,(
% 3.81/0.98    ! [X0] : (! [X1] : (((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (v7_struct_0(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.81/0.98    inference(ennf_transformation,[],[f13])).
% 3.81/0.98  
% 3.81/0.98  fof(f38,plain,(
% 3.81/0.98    ! [X0] : (! [X1] : ((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.81/0.98    inference(flattening,[],[f37])).
% 3.81/0.98  
% 3.81/0.98  fof(f76,plain,(
% 3.81/0.98    ( ! [X0,X1] : (~v1_tdlat_3(X1) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f38])).
% 3.81/0.98  
% 3.81/0.98  fof(f7,axiom,(
% 3.81/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.81/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f27,plain,(
% 3.81/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.81/0.98    inference(ennf_transformation,[],[f7])).
% 3.81/0.98  
% 3.81/0.98  fof(f69,plain,(
% 3.81/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f27])).
% 3.81/0.98  
% 3.81/0.98  fof(f9,axiom,(
% 3.81/0.98    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 3.81/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f29,plain,(
% 3.81/0.98    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 3.81/0.98    inference(ennf_transformation,[],[f9])).
% 3.81/0.98  
% 3.81/0.98  fof(f30,plain,(
% 3.81/0.98    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 3.81/0.98    inference(flattening,[],[f29])).
% 3.81/0.98  
% 3.81/0.98  fof(f71,plain,(
% 3.81/0.98    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f30])).
% 3.81/0.98  
% 3.81/0.98  fof(f8,axiom,(
% 3.81/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.81/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f28,plain,(
% 3.81/0.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.81/0.98    inference(ennf_transformation,[],[f8])).
% 3.81/0.98  
% 3.81/0.98  fof(f70,plain,(
% 3.81/0.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f28])).
% 3.81/0.98  
% 3.81/0.98  fof(f12,axiom,(
% 3.81/0.98    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 3.81/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f35,plain,(
% 3.81/0.98    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 3.81/0.98    inference(ennf_transformation,[],[f12])).
% 3.81/0.98  
% 3.81/0.98  fof(f36,plain,(
% 3.81/0.98    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 3.81/0.98    inference(flattening,[],[f35])).
% 3.81/0.98  
% 3.81/0.98  fof(f74,plain,(
% 3.81/0.98    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f36])).
% 3.81/0.98  
% 3.81/0.98  fof(f88,plain,(
% 3.81/0.98    v2_tdlat_3(sK3)),
% 3.81/0.98    inference(cnf_transformation,[],[f61])).
% 3.81/0.98  
% 3.81/0.98  fof(f82,plain,(
% 3.81/0.98    ( ! [X0,X1] : (v1_tdlat_3(sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f56])).
% 3.81/0.98  
% 3.81/0.98  fof(f81,plain,(
% 3.81/0.98    ( ! [X0,X1] : (~v2_struct_0(sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f56])).
% 3.81/0.98  
% 3.81/0.98  fof(f84,plain,(
% 3.81/0.98    ( ! [X0,X1] : (u1_struct_0(sK2(X0,X1)) = X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f56])).
% 3.81/0.98  
% 3.81/0.98  fof(f14,axiom,(
% 3.81/0.98    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 3.81/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f21,plain,(
% 3.81/0.98    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2))))),
% 3.81/0.98    inference(pure_predicate_removal,[],[f14])).
% 3.81/0.98  
% 3.81/0.98  fof(f39,plain,(
% 3.81/0.98    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.81/0.98    inference(ennf_transformation,[],[f21])).
% 3.81/0.98  
% 3.81/0.98  fof(f40,plain,(
% 3.81/0.98    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.81/0.98    inference(flattening,[],[f39])).
% 3.81/0.98  
% 3.81/0.98  fof(f53,plain,(
% 3.81/0.98    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(sK1(X0,X1)) = X1 & m1_pre_topc(sK1(X0,X1),X0) & ~v2_struct_0(sK1(X0,X1))))),
% 3.81/0.98    introduced(choice_axiom,[])).
% 3.81/0.98  
% 3.81/0.98  fof(f54,plain,(
% 3.81/0.98    ! [X0] : (! [X1] : ((u1_struct_0(sK1(X0,X1)) = X1 & m1_pre_topc(sK1(X0,X1),X0) & ~v2_struct_0(sK1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.81/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f40,f53])).
% 3.81/0.98  
% 3.81/0.98  fof(f78,plain,(
% 3.81/0.98    ( ! [X0,X1] : (m1_pre_topc(sK1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f54])).
% 3.81/0.98  
% 3.81/0.98  fof(f79,plain,(
% 3.81/0.98    ( ! [X0,X1] : (u1_struct_0(sK1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f54])).
% 3.81/0.98  
% 3.81/0.98  fof(f77,plain,(
% 3.81/0.98    ( ! [X0,X1] : (~v2_struct_0(sK1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f54])).
% 3.81/0.98  
% 3.81/0.98  fof(f4,axiom,(
% 3.81/0.98    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.81/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f24,plain,(
% 3.81/0.98    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.81/0.98    inference(ennf_transformation,[],[f4])).
% 3.81/0.98  
% 3.81/0.98  fof(f66,plain,(
% 3.81/0.98    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f24])).
% 3.81/0.98  
% 3.81/0.98  fof(f17,axiom,(
% 3.81/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 3.81/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f45,plain,(
% 3.81/0.98    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.81/0.98    inference(ennf_transformation,[],[f17])).
% 3.81/0.98  
% 3.81/0.98  fof(f46,plain,(
% 3.81/0.98    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.81/0.98    inference(flattening,[],[f45])).
% 3.81/0.98  
% 3.81/0.98  fof(f85,plain,(
% 3.81/0.98    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f46])).
% 3.81/0.98  
% 3.81/0.98  fof(f2,axiom,(
% 3.81/0.98    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 3.81/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f64,plain,(
% 3.81/0.98    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 3.81/0.98    inference(cnf_transformation,[],[f2])).
% 3.81/0.98  
% 3.81/0.98  fof(f6,axiom,(
% 3.81/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.81/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f20,plain,(
% 3.81/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 3.81/0.98    inference(unused_predicate_definition_removal,[],[f6])).
% 3.81/0.98  
% 3.81/0.98  fof(f26,plain,(
% 3.81/0.98    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 3.81/0.98    inference(ennf_transformation,[],[f20])).
% 3.81/0.98  
% 3.81/0.98  fof(f68,plain,(
% 3.81/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.81/0.98    inference(cnf_transformation,[],[f26])).
% 3.81/0.98  
% 3.81/0.98  fof(f15,axiom,(
% 3.81/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 3.81/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f41,plain,(
% 3.81/0.98    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 3.81/0.98    inference(ennf_transformation,[],[f15])).
% 3.81/0.98  
% 3.81/0.98  fof(f42,plain,(
% 3.81/0.98    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.81/0.98    inference(flattening,[],[f41])).
% 3.81/0.98  
% 3.81/0.98  fof(f80,plain,(
% 3.81/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f42])).
% 3.81/0.98  
% 3.81/0.98  fof(f3,axiom,(
% 3.81/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 3.81/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.98  
% 3.81/0.98  fof(f23,plain,(
% 3.81/0.98    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 3.81/0.98    inference(ennf_transformation,[],[f3])).
% 3.81/0.98  
% 3.81/0.98  fof(f65,plain,(
% 3.81/0.98    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 3.81/0.98    inference(cnf_transformation,[],[f23])).
% 3.81/0.98  
% 3.81/0.98  fof(f92,plain,(
% 3.81/0.98    v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3)),
% 3.81/0.98    inference(cnf_transformation,[],[f61])).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1771,plain,
% 3.81/0.98      ( ~ v2_tex_2(X0,X1) | v2_tex_2(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.81/0.98      theory(equality) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_11549,plain,
% 3.81/0.98      ( v2_tex_2(X0,X1)
% 3.81/0.98      | ~ v2_tex_2(k1_tarski(sK0(sK4)),X2)
% 3.81/0.98      | X1 != X2
% 3.81/0.98      | X0 != k1_tarski(sK0(sK4)) ),
% 3.81/0.98      inference(instantiation,[status(thm)],[c_1771]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_15262,plain,
% 3.81/0.98      ( ~ v2_tex_2(k1_tarski(sK0(sK4)),X0)
% 3.81/0.98      | v2_tex_2(sK4,X1)
% 3.81/0.98      | X1 != X0
% 3.81/0.98      | sK4 != k1_tarski(sK0(sK4)) ),
% 3.81/0.98      inference(instantiation,[status(thm)],[c_11549]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_15264,plain,
% 3.81/0.98      ( ~ v2_tex_2(k1_tarski(sK0(sK4)),sK3)
% 3.81/0.98      | v2_tex_2(sK4,sK3)
% 3.81/0.98      | sK3 != sK3
% 3.81/0.98      | sK4 != k1_tarski(sK0(sK4)) ),
% 3.81/0.98      inference(instantiation,[status(thm)],[c_15262]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_26,negated_conjecture,
% 3.81/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.81/0.98      inference(cnf_transformation,[],[f91]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_2341,plain,
% 3.81/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_20,plain,
% 3.81/0.98      ( ~ v2_tex_2(X0,X1)
% 3.81/0.98      | m1_pre_topc(sK2(X1,X0),X1)
% 3.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.81/0.98      | ~ v2_pre_topc(X1)
% 3.81/0.98      | v2_struct_0(X1)
% 3.81/0.98      | ~ l1_pre_topc(X1)
% 3.81/0.98      | v1_xboole_0(X0) ),
% 3.81/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_30,negated_conjecture,
% 3.81/0.98      ( v2_pre_topc(sK3) ),
% 3.81/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_746,plain,
% 3.81/0.98      ( ~ v2_tex_2(X0,X1)
% 3.81/0.98      | m1_pre_topc(sK2(X1,X0),X1)
% 3.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.81/0.98      | v2_struct_0(X1)
% 3.81/0.98      | ~ l1_pre_topc(X1)
% 3.81/0.98      | v1_xboole_0(X0)
% 3.81/0.98      | sK3 != X1 ),
% 3.81/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_30]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_747,plain,
% 3.81/0.98      ( ~ v2_tex_2(X0,sK3)
% 3.81/0.98      | m1_pre_topc(sK2(sK3,X0),sK3)
% 3.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.81/0.98      | v2_struct_0(sK3)
% 3.81/0.98      | ~ l1_pre_topc(sK3)
% 3.81/0.98      | v1_xboole_0(X0) ),
% 3.81/0.98      inference(unflattening,[status(thm)],[c_746]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_31,negated_conjecture,
% 3.81/0.98      ( ~ v2_struct_0(sK3) ),
% 3.81/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_28,negated_conjecture,
% 3.81/0.98      ( l1_pre_topc(sK3) ),
% 3.81/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_751,plain,
% 3.81/0.98      ( ~ v2_tex_2(X0,sK3)
% 3.81/0.98      | m1_pre_topc(sK2(sK3,X0),sK3)
% 3.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.81/0.98      | v1_xboole_0(X0) ),
% 3.81/0.98      inference(global_propositional_subsumption,
% 3.81/0.98                [status(thm)],
% 3.81/0.98                [c_747,c_31,c_28]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_2332,plain,
% 3.81/0.98      ( v2_tex_2(X0,sK3) != iProver_top
% 3.81/0.98      | m1_pre_topc(sK2(sK3,X0),sK3) = iProver_top
% 3.81/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.81/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_751]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_3128,plain,
% 3.81/0.98      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.81/0.98      | m1_pre_topc(sK2(sK3,sK4),sK3) = iProver_top
% 3.81/0.98      | v1_xboole_0(sK4) = iProver_top ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_2341,c_2332]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_27,negated_conjecture,
% 3.81/0.98      ( ~ v1_xboole_0(sK4) ),
% 3.81/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_36,plain,
% 3.81/0.98      ( v1_xboole_0(sK4) != iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_3240,plain,
% 3.81/0.98      ( m1_pre_topc(sK2(sK3,sK4),sK3) = iProver_top
% 3.81/0.98      | v2_tex_2(sK4,sK3) != iProver_top ),
% 3.81/0.98      inference(global_propositional_subsumption,
% 3.81/0.98                [status(thm)],
% 3.81/0.98                [c_3128,c_36]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_3241,plain,
% 3.81/0.98      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.81/0.98      | m1_pre_topc(sK2(sK3,sK4),sK3) = iProver_top ),
% 3.81/0.98      inference(renaming,[status(thm)],[c_3240]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_0,plain,
% 3.81/0.98      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.81/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_5,plain,
% 3.81/0.98      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.81/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_452,plain,
% 3.81/0.98      ( m1_subset_1(X0,X1) | v1_xboole_0(X2) | X1 != X2 | sK0(X2) != X0 ),
% 3.81/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_5]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_453,plain,
% 3.81/0.98      ( m1_subset_1(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.81/0.98      inference(unflattening,[status(thm)],[c_452]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_2336,plain,
% 3.81/0.98      ( m1_subset_1(sK0(X0),X0) = iProver_top
% 3.81/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_453]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_10,plain,
% 3.81/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.81/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.81/0.98      | m1_subset_1(X2,u1_struct_0(X1))
% 3.81/0.98      | v2_struct_0(X1)
% 3.81/0.98      | v2_struct_0(X0)
% 3.81/0.98      | ~ l1_pre_topc(X1) ),
% 3.81/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_2348,plain,
% 3.81/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 3.81/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.81/0.98      | m1_subset_1(X2,u1_struct_0(X1)) = iProver_top
% 3.81/0.98      | v2_struct_0(X0) = iProver_top
% 3.81/0.98      | v2_struct_0(X1) = iProver_top
% 3.81/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_4285,plain,
% 3.81/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 3.81/0.98      | m1_subset_1(sK0(u1_struct_0(X0)),u1_struct_0(X1)) = iProver_top
% 3.81/0.98      | v2_struct_0(X0) = iProver_top
% 3.81/0.98      | v2_struct_0(X1) = iProver_top
% 3.81/0.98      | l1_pre_topc(X1) != iProver_top
% 3.81/0.98      | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_2336,c_2348]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_11,plain,
% 3.81/0.98      ( ~ m1_subset_1(X0,X1)
% 3.81/0.98      | v1_xboole_0(X1)
% 3.81/0.98      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 3.81/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_2347,plain,
% 3.81/0.98      ( k6_domain_1(X0,X1) = k1_tarski(X1)
% 3.81/0.98      | m1_subset_1(X1,X0) != iProver_top
% 3.81/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_6091,plain,
% 3.81/0.98      ( k6_domain_1(u1_struct_0(X0),sK0(u1_struct_0(X1))) = k1_tarski(sK0(u1_struct_0(X1)))
% 3.81/0.98      | m1_pre_topc(X1,X0) != iProver_top
% 3.81/0.98      | v2_struct_0(X1) = iProver_top
% 3.81/0.98      | v2_struct_0(X0) = iProver_top
% 3.81/0.98      | l1_pre_topc(X0) != iProver_top
% 3.81/0.98      | v1_xboole_0(u1_struct_0(X1)) = iProver_top
% 3.81/0.98      | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_4285,c_2347]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_8219,plain,
% 3.81/0.98      ( k6_domain_1(u1_struct_0(sK3),sK0(u1_struct_0(sK2(sK3,sK4)))) = k1_tarski(sK0(u1_struct_0(sK2(sK3,sK4))))
% 3.81/0.98      | v2_tex_2(sK4,sK3) != iProver_top
% 3.81/0.98      | v2_struct_0(sK2(sK3,sK4)) = iProver_top
% 3.81/0.98      | v2_struct_0(sK3) = iProver_top
% 3.81/0.98      | l1_pre_topc(sK3) != iProver_top
% 3.81/0.98      | v1_xboole_0(u1_struct_0(sK2(sK3,sK4))) = iProver_top
% 3.81/0.98      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_3241,c_6091]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_24,negated_conjecture,
% 3.81/0.98      ( ~ v2_tex_2(sK4,sK3) | ~ v1_zfmisc_1(sK4) ),
% 3.81/0.98      inference(cnf_transformation,[],[f93]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_39,plain,
% 3.81/0.98      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.81/0.98      | v1_zfmisc_1(sK4) != iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_13,plain,
% 3.81/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.81/0.98      | ~ v1_tdlat_3(X0)
% 3.81/0.98      | ~ v2_tdlat_3(X1)
% 3.81/0.98      | ~ v2_pre_topc(X1)
% 3.81/0.98      | v2_struct_0(X1)
% 3.81/0.98      | v2_struct_0(X0)
% 3.81/0.98      | v7_struct_0(X0)
% 3.81/0.98      | ~ l1_pre_topc(X1) ),
% 3.81/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_7,plain,
% 3.81/0.98      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.81/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_9,plain,
% 3.81/0.98      ( ~ v7_struct_0(X0)
% 3.81/0.98      | v1_zfmisc_1(u1_struct_0(X0))
% 3.81/0.98      | ~ l1_struct_0(X0) ),
% 3.81/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_408,plain,
% 3.81/0.98      ( ~ v7_struct_0(X0)
% 3.81/0.98      | v1_zfmisc_1(u1_struct_0(X0))
% 3.81/0.98      | ~ l1_pre_topc(X0) ),
% 3.81/0.98      inference(resolution,[status(thm)],[c_7,c_9]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_484,plain,
% 3.81/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.81/0.98      | ~ v1_tdlat_3(X0)
% 3.81/0.98      | ~ v2_tdlat_3(X1)
% 3.81/0.98      | ~ v2_pre_topc(X1)
% 3.81/0.98      | v2_struct_0(X0)
% 3.81/0.98      | v2_struct_0(X1)
% 3.81/0.98      | v1_zfmisc_1(u1_struct_0(X0))
% 3.81/0.98      | ~ l1_pre_topc(X0)
% 3.81/0.98      | ~ l1_pre_topc(X1) ),
% 3.81/0.98      inference(resolution,[status(thm)],[c_13,c_408]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_8,plain,
% 3.81/0.98      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.81/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_488,plain,
% 3.81/0.98      ( v1_zfmisc_1(u1_struct_0(X0))
% 3.81/0.98      | v2_struct_0(X1)
% 3.81/0.98      | v2_struct_0(X0)
% 3.81/0.98      | ~ v2_pre_topc(X1)
% 3.81/0.98      | ~ v2_tdlat_3(X1)
% 3.81/0.98      | ~ v1_tdlat_3(X0)
% 3.81/0.98      | ~ m1_pre_topc(X0,X1)
% 3.81/0.98      | ~ l1_pre_topc(X1) ),
% 3.81/0.98      inference(global_propositional_subsumption,
% 3.81/0.98                [status(thm)],
% 3.81/0.98                [c_484,c_8]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_489,plain,
% 3.81/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.81/0.98      | ~ v1_tdlat_3(X0)
% 3.81/0.98      | ~ v2_tdlat_3(X1)
% 3.81/0.98      | ~ v2_pre_topc(X1)
% 3.81/0.98      | v2_struct_0(X0)
% 3.81/0.98      | v2_struct_0(X1)
% 3.81/0.98      | v1_zfmisc_1(u1_struct_0(X0))
% 3.81/0.98      | ~ l1_pre_topc(X1) ),
% 3.81/0.98      inference(renaming,[status(thm)],[c_488]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_12,plain,
% 3.81/0.98      ( ~ v2_tdlat_3(X0) | v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 3.81/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_508,plain,
% 3.81/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.81/0.98      | ~ v1_tdlat_3(X0)
% 3.81/0.98      | ~ v2_tdlat_3(X1)
% 3.81/0.98      | v2_struct_0(X0)
% 3.81/0.98      | v2_struct_0(X1)
% 3.81/0.98      | v1_zfmisc_1(u1_struct_0(X0))
% 3.81/0.98      | ~ l1_pre_topc(X1) ),
% 3.81/0.98      inference(forward_subsumption_resolution,
% 3.81/0.98                [status(thm)],
% 3.81/0.98                [c_489,c_12]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_29,negated_conjecture,
% 3.81/0.98      ( v2_tdlat_3(sK3) ),
% 3.81/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_529,plain,
% 3.81/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.81/0.98      | ~ v1_tdlat_3(X0)
% 3.81/0.98      | v2_struct_0(X0)
% 3.81/0.98      | v2_struct_0(X1)
% 3.81/0.98      | v1_zfmisc_1(u1_struct_0(X0))
% 3.81/0.98      | ~ l1_pre_topc(X1)
% 3.81/0.98      | sK3 != X1 ),
% 3.81/0.98      inference(resolution_lifted,[status(thm)],[c_508,c_29]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_530,plain,
% 3.81/0.98      ( ~ m1_pre_topc(X0,sK3)
% 3.81/0.98      | ~ v1_tdlat_3(X0)
% 3.81/0.98      | v2_struct_0(X0)
% 3.81/0.98      | v2_struct_0(sK3)
% 3.81/0.98      | v1_zfmisc_1(u1_struct_0(X0))
% 3.81/0.98      | ~ l1_pre_topc(sK3) ),
% 3.81/0.98      inference(unflattening,[status(thm)],[c_529]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_534,plain,
% 3.81/0.98      ( v1_zfmisc_1(u1_struct_0(X0))
% 3.81/0.98      | ~ m1_pre_topc(X0,sK3)
% 3.81/0.98      | ~ v1_tdlat_3(X0)
% 3.81/0.98      | v2_struct_0(X0) ),
% 3.81/0.98      inference(global_propositional_subsumption,
% 3.81/0.98                [status(thm)],
% 3.81/0.98                [c_530,c_31,c_28]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_535,plain,
% 3.81/0.98      ( ~ m1_pre_topc(X0,sK3)
% 3.81/0.98      | ~ v1_tdlat_3(X0)
% 3.81/0.98      | v2_struct_0(X0)
% 3.81/0.98      | v1_zfmisc_1(u1_struct_0(X0)) ),
% 3.81/0.98      inference(renaming,[status(thm)],[c_534]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_21,plain,
% 3.81/0.98      ( ~ v2_tex_2(X0,X1)
% 3.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.81/0.98      | v1_tdlat_3(sK2(X1,X0))
% 3.81/0.98      | ~ v2_pre_topc(X1)
% 3.81/0.98      | v2_struct_0(X1)
% 3.81/0.98      | ~ l1_pre_topc(X1)
% 3.81/0.98      | v1_xboole_0(X0) ),
% 3.81/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_722,plain,
% 3.81/0.98      ( ~ v2_tex_2(X0,X1)
% 3.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.81/0.98      | v1_tdlat_3(sK2(X1,X0))
% 3.81/0.98      | v2_struct_0(X1)
% 3.81/0.98      | ~ l1_pre_topc(X1)
% 3.81/0.98      | v1_xboole_0(X0)
% 3.81/0.98      | sK3 != X1 ),
% 3.81/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_30]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_723,plain,
% 3.81/0.98      ( ~ v2_tex_2(X0,sK3)
% 3.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.81/0.98      | v1_tdlat_3(sK2(sK3,X0))
% 3.81/0.98      | v2_struct_0(sK3)
% 3.81/0.98      | ~ l1_pre_topc(sK3)
% 3.81/0.98      | v1_xboole_0(X0) ),
% 3.81/0.98      inference(unflattening,[status(thm)],[c_722]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_727,plain,
% 3.81/0.98      ( ~ v2_tex_2(X0,sK3)
% 3.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.81/0.98      | v1_tdlat_3(sK2(sK3,X0))
% 3.81/0.98      | v1_xboole_0(X0) ),
% 3.81/0.98      inference(global_propositional_subsumption,
% 3.81/0.98                [status(thm)],
% 3.81/0.98                [c_723,c_31,c_28]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_817,plain,
% 3.81/0.98      ( ~ v2_tex_2(X0,sK3)
% 3.81/0.98      | ~ m1_pre_topc(X1,sK3)
% 3.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.81/0.98      | v2_struct_0(X1)
% 3.81/0.98      | v1_zfmisc_1(u1_struct_0(X1))
% 3.81/0.98      | v1_xboole_0(X0)
% 3.81/0.98      | sK2(sK3,X0) != X1 ),
% 3.81/0.98      inference(resolution_lifted,[status(thm)],[c_535,c_727]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_818,plain,
% 3.81/0.98      ( ~ v2_tex_2(X0,sK3)
% 3.81/0.98      | ~ m1_pre_topc(sK2(sK3,X0),sK3)
% 3.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.81/0.98      | v2_struct_0(sK2(sK3,X0))
% 3.81/0.98      | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
% 3.81/0.98      | v1_xboole_0(X0) ),
% 3.81/0.98      inference(unflattening,[status(thm)],[c_817]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_22,plain,
% 3.81/0.98      ( ~ v2_tex_2(X0,X1)
% 3.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.81/0.98      | ~ v2_pre_topc(X1)
% 3.81/0.98      | v2_struct_0(X1)
% 3.81/0.98      | ~ v2_struct_0(sK2(X1,X0))
% 3.81/0.98      | ~ l1_pre_topc(X1)
% 3.81/0.98      | v1_xboole_0(X0) ),
% 3.81/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_698,plain,
% 3.81/0.98      ( ~ v2_tex_2(X0,X1)
% 3.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.81/0.98      | v2_struct_0(X1)
% 3.81/0.98      | ~ v2_struct_0(sK2(X1,X0))
% 3.81/0.98      | ~ l1_pre_topc(X1)
% 3.81/0.98      | v1_xboole_0(X0)
% 3.81/0.98      | sK3 != X1 ),
% 3.81/0.98      inference(resolution_lifted,[status(thm)],[c_22,c_30]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_699,plain,
% 3.81/0.98      ( ~ v2_tex_2(X0,sK3)
% 3.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.81/0.98      | ~ v2_struct_0(sK2(sK3,X0))
% 3.81/0.98      | v2_struct_0(sK3)
% 3.81/0.98      | ~ l1_pre_topc(sK3)
% 3.81/0.98      | v1_xboole_0(X0) ),
% 3.81/0.98      inference(unflattening,[status(thm)],[c_698]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_703,plain,
% 3.81/0.98      ( ~ v2_tex_2(X0,sK3)
% 3.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.81/0.98      | ~ v2_struct_0(sK2(sK3,X0))
% 3.81/0.98      | v1_xboole_0(X0) ),
% 3.81/0.98      inference(global_propositional_subsumption,
% 3.81/0.98                [status(thm)],
% 3.81/0.98                [c_699,c_31,c_28]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_822,plain,
% 3.81/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.81/0.98      | ~ v2_tex_2(X0,sK3)
% 3.81/0.98      | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
% 3.81/0.98      | v1_xboole_0(X0) ),
% 3.81/0.98      inference(global_propositional_subsumption,
% 3.81/0.98                [status(thm)],
% 3.81/0.98                [c_818,c_703,c_751]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_823,plain,
% 3.81/0.98      ( ~ v2_tex_2(X0,sK3)
% 3.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.81/0.98      | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
% 3.81/0.98      | v1_xboole_0(X0) ),
% 3.81/0.98      inference(renaming,[status(thm)],[c_822]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_2330,plain,
% 3.81/0.98      ( v2_tex_2(X0,sK3) != iProver_top
% 3.81/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.81/0.98      | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0))) = iProver_top
% 3.81/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_823]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_2685,plain,
% 3.81/0.98      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.81/0.98      | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) = iProver_top
% 3.81/0.98      | v1_xboole_0(sK4) = iProver_top ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_2341,c_2330]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1758,plain,( X0 = X0 ),theory(equality) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_2724,plain,
% 3.81/0.98      ( sK4 = sK4 ),
% 3.81/0.98      inference(instantiation,[status(thm)],[c_1758]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_19,plain,
% 3.81/0.98      ( ~ v2_tex_2(X0,X1)
% 3.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.81/0.98      | ~ v2_pre_topc(X1)
% 3.81/0.98      | v2_struct_0(X1)
% 3.81/0.98      | ~ l1_pre_topc(X1)
% 3.81/0.98      | v1_xboole_0(X0)
% 3.81/0.98      | u1_struct_0(sK2(X1,X0)) = X0 ),
% 3.81/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_770,plain,
% 3.81/0.98      ( ~ v2_tex_2(X0,X1)
% 3.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.81/0.98      | v2_struct_0(X1)
% 3.81/0.98      | ~ l1_pre_topc(X1)
% 3.81/0.98      | v1_xboole_0(X0)
% 3.81/0.98      | u1_struct_0(sK2(X1,X0)) = X0
% 3.81/0.98      | sK3 != X1 ),
% 3.81/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_771,plain,
% 3.81/0.98      ( ~ v2_tex_2(X0,sK3)
% 3.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.81/0.98      | v2_struct_0(sK3)
% 3.81/0.98      | ~ l1_pre_topc(sK3)
% 3.81/0.98      | v1_xboole_0(X0)
% 3.81/0.98      | u1_struct_0(sK2(sK3,X0)) = X0 ),
% 3.81/0.98      inference(unflattening,[status(thm)],[c_770]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_775,plain,
% 3.81/0.98      ( ~ v2_tex_2(X0,sK3)
% 3.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.81/0.98      | v1_xboole_0(X0)
% 3.81/0.98      | u1_struct_0(sK2(sK3,X0)) = X0 ),
% 3.81/0.98      inference(global_propositional_subsumption,
% 3.81/0.98                [status(thm)],
% 3.81/0.98                [c_771,c_31,c_28]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_2331,plain,
% 3.81/0.98      ( u1_struct_0(sK2(sK3,X0)) = X0
% 3.81/0.98      | v2_tex_2(X0,sK3) != iProver_top
% 3.81/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.81/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.81/0.98      inference(predicate_to_equality,[status(thm)],[c_775]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_3035,plain,
% 3.81/0.98      ( u1_struct_0(sK2(sK3,sK4)) = sK4
% 3.81/0.98      | v2_tex_2(sK4,sK3) != iProver_top
% 3.81/0.98      | v1_xboole_0(sK4) = iProver_top ),
% 3.81/0.98      inference(superposition,[status(thm)],[c_2341,c_2331]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1759,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_2700,plain,
% 3.81/0.98      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 3.81/0.98      inference(instantiation,[status(thm)],[c_1759]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_2917,plain,
% 3.81/0.98      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 3.81/0.98      inference(instantiation,[status(thm)],[c_2700]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_3075,plain,
% 3.81/0.98      ( u1_struct_0(sK2(sK3,sK4)) != sK4
% 3.81/0.98      | sK4 = u1_struct_0(sK2(sK3,sK4))
% 3.81/0.98      | sK4 != sK4 ),
% 3.81/0.98      inference(instantiation,[status(thm)],[c_2917]) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_1767,plain,
% 3.81/0.98      ( ~ v1_zfmisc_1(X0) | v1_zfmisc_1(X1) | X1 != X0 ),
% 3.81/0.98      theory(equality) ).
% 3.81/0.98  
% 3.81/0.98  cnf(c_2851,plain,
% 3.81/0.98      ( v1_zfmisc_1(X0)
% 3.81/0.98      | ~ v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
% 3.81/0.99      | X0 != u1_struct_0(sK2(sK3,sK4)) ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_1767]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_4078,plain,
% 3.81/0.99      ( ~ v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
% 3.81/0.99      | v1_zfmisc_1(sK4)
% 3.81/0.99      | sK4 != u1_struct_0(sK2(sK3,sK4)) ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_2851]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_4079,plain,
% 3.81/0.99      ( sK4 != u1_struct_0(sK2(sK3,sK4))
% 3.81/0.99      | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) != iProver_top
% 3.81/0.99      | v1_zfmisc_1(sK4) = iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_4078]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_8542,plain,
% 3.81/0.99      ( v2_tex_2(sK4,sK3) != iProver_top ),
% 3.81/0.99      inference(global_propositional_subsumption,
% 3.81/0.99                [status(thm)],
% 3.81/0.99                [c_8219,c_36,c_39,c_2685,c_2724,c_3035,c_3075,c_4079]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_8544,plain,
% 3.81/0.99      ( ~ v2_tex_2(sK4,sK3) ),
% 3.81/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_8542]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_16,plain,
% 3.81/0.99      ( m1_pre_topc(sK1(X0,X1),X0)
% 3.81/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.81/0.99      | v2_struct_0(X0)
% 3.81/0.99      | ~ l1_pre_topc(X0)
% 3.81/0.99      | v1_xboole_0(X1) ),
% 3.81/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2345,plain,
% 3.81/0.99      ( m1_pre_topc(sK1(X0,X1),X0) = iProver_top
% 3.81/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.81/0.99      | v2_struct_0(X0) = iProver_top
% 3.81/0.99      | l1_pre_topc(X0) != iProver_top
% 3.81/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_3210,plain,
% 3.81/0.99      ( m1_pre_topc(sK1(sK3,sK4),sK3) = iProver_top
% 3.81/0.99      | v2_struct_0(sK3) = iProver_top
% 3.81/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.81/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.81/0.99      inference(superposition,[status(thm)],[c_2341,c_2345]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_32,plain,
% 3.81/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_35,plain,
% 3.81/0.99      ( l1_pre_topc(sK3) = iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_37,plain,
% 3.81/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2659,plain,
% 3.81/0.99      ( m1_pre_topc(sK1(X0,sK4),X0)
% 3.81/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
% 3.81/0.99      | v2_struct_0(X0)
% 3.81/0.99      | ~ l1_pre_topc(X0)
% 3.81/0.99      | v1_xboole_0(sK4) ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2660,plain,
% 3.81/0.99      ( m1_pre_topc(sK1(X0,sK4),X0) = iProver_top
% 3.81/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.81/0.99      | v2_struct_0(X0) = iProver_top
% 3.81/0.99      | l1_pre_topc(X0) != iProver_top
% 3.81/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_2659]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2662,plain,
% 3.81/0.99      ( m1_pre_topc(sK1(sK3,sK4),sK3) = iProver_top
% 3.81/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.81/0.99      | v2_struct_0(sK3) = iProver_top
% 3.81/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.81/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_2660]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_3425,plain,
% 3.81/0.99      ( m1_pre_topc(sK1(sK3,sK4),sK3) = iProver_top ),
% 3.81/0.99      inference(global_propositional_subsumption,
% 3.81/0.99                [status(thm)],
% 3.81/0.99                [c_3210,c_32,c_35,c_36,c_37,c_2662]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_15,plain,
% 3.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.81/0.99      | v2_struct_0(X1)
% 3.81/0.99      | ~ l1_pre_topc(X1)
% 3.81/0.99      | v1_xboole_0(X0)
% 3.81/0.99      | u1_struct_0(sK1(X1,X0)) = X0 ),
% 3.81/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2346,plain,
% 3.81/0.99      ( u1_struct_0(sK1(X0,X1)) = X1
% 3.81/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.81/0.99      | v2_struct_0(X0) = iProver_top
% 3.81/0.99      | l1_pre_topc(X0) != iProver_top
% 3.81/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_3136,plain,
% 3.81/0.99      ( u1_struct_0(sK1(sK3,sK4)) = sK4
% 3.81/0.99      | v2_struct_0(sK3) = iProver_top
% 3.81/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.81/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.81/0.99      inference(superposition,[status(thm)],[c_2341,c_2346]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2649,plain,
% 3.81/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
% 3.81/0.99      | v2_struct_0(X0)
% 3.81/0.99      | ~ l1_pre_topc(X0)
% 3.81/0.99      | v1_xboole_0(sK4)
% 3.81/0.99      | u1_struct_0(sK1(X0,sK4)) = sK4 ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2651,plain,
% 3.81/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.81/0.99      | v2_struct_0(sK3)
% 3.81/0.99      | ~ l1_pre_topc(sK3)
% 3.81/0.99      | v1_xboole_0(sK4)
% 3.81/0.99      | u1_struct_0(sK1(sK3,sK4)) = sK4 ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_2649]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_3284,plain,
% 3.81/0.99      ( u1_struct_0(sK1(sK3,sK4)) = sK4 ),
% 3.81/0.99      inference(global_propositional_subsumption,
% 3.81/0.99                [status(thm)],
% 3.81/0.99                [c_3136,c_31,c_28,c_27,c_26,c_2651]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_3287,plain,
% 3.81/0.99      ( m1_pre_topc(sK1(sK3,sK4),X0) != iProver_top
% 3.81/0.99      | m1_subset_1(X1,u1_struct_0(X0)) = iProver_top
% 3.81/0.99      | m1_subset_1(X1,sK4) != iProver_top
% 3.81/0.99      | v2_struct_0(X0) = iProver_top
% 3.81/0.99      | v2_struct_0(sK1(sK3,sK4)) = iProver_top
% 3.81/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.81/0.99      inference(superposition,[status(thm)],[c_3284,c_2348]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_17,plain,
% 3.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.81/0.99      | v2_struct_0(X1)
% 3.81/0.99      | ~ v2_struct_0(sK1(X1,X0))
% 3.81/0.99      | ~ l1_pre_topc(X1)
% 3.81/0.99      | v1_xboole_0(X0) ),
% 3.81/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2639,plain,
% 3.81/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
% 3.81/0.99      | v2_struct_0(X0)
% 3.81/0.99      | ~ v2_struct_0(sK1(X0,sK4))
% 3.81/0.99      | ~ l1_pre_topc(X0)
% 3.81/0.99      | v1_xboole_0(sK4) ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2640,plain,
% 3.81/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.81/0.99      | v2_struct_0(X0) = iProver_top
% 3.81/0.99      | v2_struct_0(sK1(X0,sK4)) != iProver_top
% 3.81/0.99      | l1_pre_topc(X0) != iProver_top
% 3.81/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_2639]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2642,plain,
% 3.81/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.81/0.99      | v2_struct_0(sK1(sK3,sK4)) != iProver_top
% 3.81/0.99      | v2_struct_0(sK3) = iProver_top
% 3.81/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.81/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_2640]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_4245,plain,
% 3.81/0.99      ( v2_struct_0(X0) = iProver_top
% 3.81/0.99      | m1_subset_1(X1,sK4) != iProver_top
% 3.81/0.99      | m1_subset_1(X1,u1_struct_0(X0)) = iProver_top
% 3.81/0.99      | m1_pre_topc(sK1(sK3,sK4),X0) != iProver_top
% 3.81/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.81/0.99      inference(global_propositional_subsumption,
% 3.81/0.99                [status(thm)],
% 3.81/0.99                [c_3287,c_32,c_35,c_36,c_37,c_2642]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_4246,plain,
% 3.81/0.99      ( m1_pre_topc(sK1(sK3,sK4),X0) != iProver_top
% 3.81/0.99      | m1_subset_1(X1,u1_struct_0(X0)) = iProver_top
% 3.81/0.99      | m1_subset_1(X1,sK4) != iProver_top
% 3.81/0.99      | v2_struct_0(X0) = iProver_top
% 3.81/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.81/0.99      inference(renaming,[status(thm)],[c_4245]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_4256,plain,
% 3.81/0.99      ( m1_subset_1(X0,u1_struct_0(sK3)) = iProver_top
% 3.81/0.99      | m1_subset_1(X0,sK4) != iProver_top
% 3.81/0.99      | v2_struct_0(sK3) = iProver_top
% 3.81/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.81/0.99      inference(superposition,[status(thm)],[c_3425,c_4246]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_4514,plain,
% 3.81/0.99      ( m1_subset_1(X0,u1_struct_0(sK3)) = iProver_top
% 3.81/0.99      | m1_subset_1(X0,sK4) != iProver_top ),
% 3.81/0.99      inference(global_propositional_subsumption,
% 3.81/0.99                [status(thm)],
% 3.81/0.99                [c_4256,c_32,c_35]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_4523,plain,
% 3.81/0.99      ( k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0)
% 3.81/0.99      | m1_subset_1(X0,sK4) != iProver_top
% 3.81/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.81/0.99      inference(superposition,[status(thm)],[c_4514,c_2347]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_4,plain,
% 3.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.81/0.99      | ~ v1_xboole_0(X1)
% 3.81/0.99      | v1_xboole_0(X0) ),
% 3.81/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2590,plain,
% 3.81/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
% 3.81/0.99      | ~ v1_xboole_0(X0)
% 3.81/0.99      | v1_xboole_0(sK4) ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2697,plain,
% 3.81/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.81/0.99      | ~ v1_xboole_0(u1_struct_0(sK3))
% 3.81/0.99      | v1_xboole_0(sK4) ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_2590]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2698,plain,
% 3.81/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.81/0.99      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top
% 3.81/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_2697]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_4996,plain,
% 3.81/0.99      ( m1_subset_1(X0,sK4) != iProver_top
% 3.81/0.99      | k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0) ),
% 3.81/0.99      inference(global_propositional_subsumption,
% 3.81/0.99                [status(thm)],
% 3.81/0.99                [c_4523,c_36,c_37,c_2698]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_4997,plain,
% 3.81/0.99      ( k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0)
% 3.81/0.99      | m1_subset_1(X0,sK4) != iProver_top ),
% 3.81/0.99      inference(renaming,[status(thm)],[c_4996]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_5004,plain,
% 3.81/0.99      ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k1_tarski(sK0(sK4))
% 3.81/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.81/0.99      inference(superposition,[status(thm)],[c_2336,c_4997]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2574,plain,
% 3.81/0.99      ( m1_subset_1(sK0(sK4),sK4) | v1_xboole_0(sK4) ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_453]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2641,plain,
% 3.81/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.81/0.99      | ~ v2_struct_0(sK1(sK3,sK4))
% 3.81/0.99      | v2_struct_0(sK3)
% 3.81/0.99      | ~ l1_pre_topc(sK3)
% 3.81/0.99      | v1_xboole_0(sK4) ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_2639]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2661,plain,
% 3.81/0.99      ( m1_pre_topc(sK1(sK3,sK4),sK3)
% 3.81/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.81/0.99      | v2_struct_0(sK3)
% 3.81/0.99      | ~ l1_pre_topc(sK3)
% 3.81/0.99      | v1_xboole_0(sK4) ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_2659]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_3068,plain,
% 3.81/0.99      ( sK0(sK4) = sK0(sK4) ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_1758]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_1763,plain,
% 3.81/0.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.81/0.99      theory(equality) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2687,plain,
% 3.81/0.99      ( m1_subset_1(X0,X1)
% 3.81/0.99      | ~ m1_subset_1(sK0(sK4),sK4)
% 3.81/0.99      | X0 != sK0(sK4)
% 3.81/0.99      | X1 != sK4 ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_1763]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2876,plain,
% 3.81/0.99      ( m1_subset_1(X0,u1_struct_0(sK1(X1,sK4)))
% 3.81/0.99      | ~ m1_subset_1(sK0(sK4),sK4)
% 3.81/0.99      | X0 != sK0(sK4)
% 3.81/0.99      | u1_struct_0(sK1(X1,sK4)) != sK4 ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_2687]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_3249,plain,
% 3.81/0.99      ( m1_subset_1(sK0(sK4),u1_struct_0(sK1(X0,sK4)))
% 3.81/0.99      | ~ m1_subset_1(sK0(sK4),sK4)
% 3.81/0.99      | u1_struct_0(sK1(X0,sK4)) != sK4
% 3.81/0.99      | sK0(sK4) != sK0(sK4) ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_2876]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_3253,plain,
% 3.81/0.99      ( m1_subset_1(sK0(sK4),u1_struct_0(sK1(sK3,sK4)))
% 3.81/0.99      | ~ m1_subset_1(sK0(sK4),sK4)
% 3.81/0.99      | u1_struct_0(sK1(sK3,sK4)) != sK4
% 3.81/0.99      | sK0(sK4) != sK0(sK4) ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_3249]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2803,plain,
% 3.81/0.99      ( ~ m1_pre_topc(sK1(X0,sK4),X0)
% 3.81/0.99      | m1_subset_1(X1,u1_struct_0(X0))
% 3.81/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1(X0,sK4)))
% 3.81/0.99      | v2_struct_0(X0)
% 3.81/0.99      | v2_struct_0(sK1(X0,sK4))
% 3.81/0.99      | ~ l1_pre_topc(X0) ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_3811,plain,
% 3.81/0.99      ( ~ m1_pre_topc(sK1(X0,sK4),X0)
% 3.81/0.99      | m1_subset_1(sK0(sK4),u1_struct_0(X0))
% 3.81/0.99      | ~ m1_subset_1(sK0(sK4),u1_struct_0(sK1(X0,sK4)))
% 3.81/0.99      | v2_struct_0(X0)
% 3.81/0.99      | v2_struct_0(sK1(X0,sK4))
% 3.81/0.99      | ~ l1_pre_topc(X0) ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_2803]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_3813,plain,
% 3.81/0.99      ( ~ m1_pre_topc(sK1(sK3,sK4),sK3)
% 3.81/0.99      | ~ m1_subset_1(sK0(sK4),u1_struct_0(sK1(sK3,sK4)))
% 3.81/0.99      | m1_subset_1(sK0(sK4),u1_struct_0(sK3))
% 3.81/0.99      | v2_struct_0(sK1(sK3,sK4))
% 3.81/0.99      | v2_struct_0(sK3)
% 3.81/0.99      | ~ l1_pre_topc(sK3) ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_3811]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2781,plain,
% 3.81/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.81/0.99      | v1_xboole_0(u1_struct_0(sK3))
% 3.81/0.99      | k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0) ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_4441,plain,
% 3.81/0.99      ( ~ m1_subset_1(sK0(sK4),u1_struct_0(sK3))
% 3.81/0.99      | v1_xboole_0(u1_struct_0(sK3))
% 3.81/0.99      | k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k1_tarski(sK0(sK4)) ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_2781]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_5712,plain,
% 3.81/0.99      ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k1_tarski(sK0(sK4)) ),
% 3.81/0.99      inference(global_propositional_subsumption,
% 3.81/0.99                [status(thm)],
% 3.81/0.99                [c_5004,c_31,c_28,c_27,c_26,c_2574,c_2641,c_2651,c_2661,
% 3.81/0.99                 c_2697,c_3068,c_3253,c_3813,c_4441]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_23,plain,
% 3.81/0.99      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 3.81/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.81/0.99      | ~ v2_pre_topc(X0)
% 3.81/0.99      | v2_struct_0(X0)
% 3.81/0.99      | ~ l1_pre_topc(X0) ),
% 3.81/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_680,plain,
% 3.81/0.99      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 3.81/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.81/0.99      | v2_struct_0(X0)
% 3.81/0.99      | ~ l1_pre_topc(X0)
% 3.81/0.99      | sK3 != X0 ),
% 3.81/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_30]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_681,plain,
% 3.81/0.99      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
% 3.81/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.81/0.99      | v2_struct_0(sK3)
% 3.81/0.99      | ~ l1_pre_topc(sK3) ),
% 3.81/0.99      inference(unflattening,[status(thm)],[c_680]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_685,plain,
% 3.81/0.99      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
% 3.81/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 3.81/0.99      inference(global_propositional_subsumption,
% 3.81/0.99                [status(thm)],
% 3.81/0.99                [c_681,c_31,c_28]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2334,plain,
% 3.81/0.99      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) = iProver_top
% 3.81/0.99      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_685]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_5715,plain,
% 3.81/0.99      ( v2_tex_2(k1_tarski(sK0(sK4)),sK3) = iProver_top
% 3.81/0.99      | m1_subset_1(sK0(sK4),u1_struct_0(sK3)) != iProver_top ),
% 3.81/0.99      inference(superposition,[status(thm)],[c_5712,c_2334]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_5716,plain,
% 3.81/0.99      ( v2_tex_2(k1_tarski(sK0(sK4)),sK3)
% 3.81/0.99      | ~ m1_subset_1(sK0(sK4),u1_struct_0(sK3)) ),
% 3.81/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_5715]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2,plain,
% 3.81/0.99      ( ~ v1_xboole_0(k1_tarski(X0)) ),
% 3.81/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_4221,plain,
% 3.81/0.99      ( ~ v1_xboole_0(k1_tarski(sK0(sK4))) ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_4222,plain,
% 3.81/0.99      ( v1_xboole_0(k1_tarski(sK0(sK4))) != iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_4221]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_6,plain,
% 3.81/0.99      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.81/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_18,plain,
% 3.81/0.99      ( ~ r1_tarski(X0,X1)
% 3.81/0.99      | ~ v1_zfmisc_1(X1)
% 3.81/0.99      | v1_xboole_0(X0)
% 3.81/0.99      | v1_xboole_0(X1)
% 3.81/0.99      | X1 = X0 ),
% 3.81/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_426,plain,
% 3.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.81/0.99      | ~ v1_zfmisc_1(X1)
% 3.81/0.99      | v1_xboole_0(X0)
% 3.81/0.99      | v1_xboole_0(X1)
% 3.81/0.99      | X1 = X0 ),
% 3.81/0.99      inference(resolution,[status(thm)],[c_6,c_18]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_430,plain,
% 3.81/0.99      ( v1_xboole_0(X0)
% 3.81/0.99      | ~ v1_zfmisc_1(X1)
% 3.81/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.81/0.99      | X1 = X0 ),
% 3.81/0.99      inference(global_propositional_subsumption,
% 3.81/0.99                [status(thm)],
% 3.81/0.99                [c_426,c_4]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_431,plain,
% 3.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.81/0.99      | ~ v1_zfmisc_1(X1)
% 3.81/0.99      | v1_xboole_0(X0)
% 3.81/0.99      | X1 = X0 ),
% 3.81/0.99      inference(renaming,[status(thm)],[c_430]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2624,plain,
% 3.81/0.99      ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
% 3.81/0.99      | ~ v1_zfmisc_1(X1)
% 3.81/0.99      | v1_xboole_0(k1_tarski(X0))
% 3.81/0.99      | X1 = k1_tarski(X0) ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_431]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_3166,plain,
% 3.81/0.99      ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK4))
% 3.81/0.99      | ~ v1_zfmisc_1(sK4)
% 3.81/0.99      | v1_xboole_0(k1_tarski(X0))
% 3.81/0.99      | sK4 = k1_tarski(X0) ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_2624]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_3738,plain,
% 3.81/0.99      ( ~ m1_subset_1(k1_tarski(sK0(sK4)),k1_zfmisc_1(sK4))
% 3.81/0.99      | ~ v1_zfmisc_1(sK4)
% 3.81/0.99      | v1_xboole_0(k1_tarski(sK0(sK4)))
% 3.81/0.99      | sK4 = k1_tarski(sK0(sK4)) ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_3166]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_3741,plain,
% 3.81/0.99      ( sK4 = k1_tarski(sK0(sK4))
% 3.81/0.99      | m1_subset_1(k1_tarski(sK0(sK4)),k1_zfmisc_1(sK4)) != iProver_top
% 3.81/0.99      | v1_zfmisc_1(sK4) != iProver_top
% 3.81/0.99      | v1_xboole_0(k1_tarski(sK0(sK4))) = iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_3738]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_3,plain,
% 3.81/0.99      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~ r2_hidden(X0,X1) ),
% 3.81/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_464,plain,
% 3.81/0.99      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
% 3.81/0.99      | v1_xboole_0(X2)
% 3.81/0.99      | X1 != X2
% 3.81/0.99      | sK0(X2) != X0 ),
% 3.81/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_3]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_465,plain,
% 3.81/0.99      ( m1_subset_1(k1_tarski(sK0(X0)),k1_zfmisc_1(X0))
% 3.81/0.99      | v1_xboole_0(X0) ),
% 3.81/0.99      inference(unflattening,[status(thm)],[c_464]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2582,plain,
% 3.81/0.99      ( m1_subset_1(k1_tarski(sK0(sK4)),k1_zfmisc_1(sK4))
% 3.81/0.99      | v1_xboole_0(sK4) ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_465]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2583,plain,
% 3.81/0.99      ( m1_subset_1(k1_tarski(sK0(sK4)),k1_zfmisc_1(sK4)) = iProver_top
% 3.81/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_2582]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_1785,plain,
% 3.81/0.99      ( sK3 = sK3 ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_1758]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_25,negated_conjecture,
% 3.81/0.99      ( v2_tex_2(sK4,sK3) | v1_zfmisc_1(sK4) ),
% 3.81/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_38,plain,
% 3.81/0.99      ( v2_tex_2(sK4,sK3) = iProver_top
% 3.81/0.99      | v1_zfmisc_1(sK4) = iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(contradiction,plain,
% 3.81/0.99      ( $false ),
% 3.81/0.99      inference(minisat,
% 3.81/0.99                [status(thm)],
% 3.81/0.99                [c_15264,c_8544,c_8542,c_5716,c_4222,c_3813,c_3741,
% 3.81/0.99                 c_3253,c_3068,c_2661,c_2651,c_2641,c_2583,c_2574,c_1785,
% 3.81/0.99                 c_38,c_26,c_36,c_27,c_28,c_31]) ).
% 3.81/0.99  
% 3.81/0.99  
% 3.81/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.81/0.99  
% 3.81/0.99  ------                               Statistics
% 3.81/0.99  
% 3.81/0.99  ------ General
% 3.81/0.99  
% 3.81/0.99  abstr_ref_over_cycles:                  0
% 3.81/0.99  abstr_ref_under_cycles:                 0
% 3.81/0.99  gc_basic_clause_elim:                   0
% 3.81/0.99  forced_gc_time:                         0
% 3.81/0.99  parsing_time:                           0.011
% 3.81/0.99  unif_index_cands_time:                  0.
% 3.81/0.99  unif_index_add_time:                    0.
% 3.81/0.99  orderings_time:                         0.
% 3.81/0.99  out_proof_time:                         0.014
% 3.81/0.99  total_time:                             0.439
% 3.81/0.99  num_of_symbols:                         54
% 3.81/0.99  num_of_terms:                           9073
% 3.81/0.99  
% 3.81/0.99  ------ Preprocessing
% 3.81/0.99  
% 3.81/0.99  num_of_splits:                          0
% 3.81/0.99  num_of_split_atoms:                     0
% 3.81/0.99  num_of_reused_defs:                     0
% 3.81/0.99  num_eq_ax_congr_red:                    23
% 3.81/0.99  num_of_sem_filtered_clauses:            1
% 3.81/0.99  num_of_subtypes:                        0
% 3.81/0.99  monotx_restored_types:                  0
% 3.81/0.99  sat_num_of_epr_types:                   0
% 3.81/0.99  sat_num_of_non_cyclic_types:            0
% 3.81/0.99  sat_guarded_non_collapsed_types:        0
% 3.81/0.99  num_pure_diseq_elim:                    0
% 3.81/0.99  simp_replaced_by:                       0
% 3.81/0.99  res_preprocessed:                       126
% 3.81/0.99  prep_upred:                             0
% 3.81/0.99  prep_unflattend:                        53
% 3.81/0.99  smt_new_axioms:                         0
% 3.81/0.99  pred_elim_cands:                        7
% 3.81/0.99  pred_elim:                              7
% 3.81/0.99  pred_elim_cl:                           9
% 3.81/0.99  pred_elim_cycles:                       15
% 3.81/0.99  merged_defs:                            8
% 3.81/0.99  merged_defs_ncl:                        0
% 3.81/0.99  bin_hyper_res:                          8
% 3.81/0.99  prep_cycles:                            4
% 3.81/0.99  pred_elim_time:                         0.023
% 3.81/0.99  splitting_time:                         0.
% 3.81/0.99  sem_filter_time:                        0.
% 3.81/0.99  monotx_time:                            0.001
% 3.81/0.99  subtype_inf_time:                       0.
% 3.81/0.99  
% 3.81/0.99  ------ Problem properties
% 3.81/0.99  
% 3.81/0.99  clauses:                                22
% 3.81/0.99  conjectures:                            6
% 3.81/0.99  epr:                                    6
% 3.81/0.99  horn:                                   10
% 3.81/0.99  ground:                                 6
% 3.81/0.99  unary:                                  5
% 3.81/0.99  binary:                                 5
% 3.81/0.99  lits:                                   65
% 3.81/0.99  lits_eq:                                4
% 3.81/0.99  fd_pure:                                0
% 3.81/0.99  fd_pseudo:                              0
% 3.81/0.99  fd_cond:                                0
% 3.81/0.99  fd_pseudo_cond:                         1
% 3.81/0.99  ac_symbols:                             0
% 3.81/0.99  
% 3.81/0.99  ------ Propositional Solver
% 3.81/0.99  
% 3.81/0.99  prop_solver_calls:                      32
% 3.81/0.99  prop_fast_solver_calls:                 2257
% 3.81/0.99  smt_solver_calls:                       0
% 3.81/0.99  smt_fast_solver_calls:                  0
% 3.81/0.99  prop_num_of_clauses:                    4926
% 3.81/0.99  prop_preprocess_simplified:             10573
% 3.81/0.99  prop_fo_subsumed:                       270
% 3.81/0.99  prop_solver_time:                       0.
% 3.81/0.99  smt_solver_time:                        0.
% 3.81/0.99  smt_fast_solver_time:                   0.
% 3.81/0.99  prop_fast_solver_time:                  0.
% 3.81/0.99  prop_unsat_core_time:                   0.
% 3.81/0.99  
% 3.81/0.99  ------ QBF
% 3.81/0.99  
% 3.81/0.99  qbf_q_res:                              0
% 3.81/0.99  qbf_num_tautologies:                    0
% 3.81/0.99  qbf_prep_cycles:                        0
% 3.81/0.99  
% 3.81/0.99  ------ BMC1
% 3.81/0.99  
% 3.81/0.99  bmc1_current_bound:                     -1
% 3.81/0.99  bmc1_last_solved_bound:                 -1
% 3.81/0.99  bmc1_unsat_core_size:                   -1
% 3.81/0.99  bmc1_unsat_core_parents_size:           -1
% 3.81/0.99  bmc1_merge_next_fun:                    0
% 3.81/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.81/0.99  
% 3.81/0.99  ------ Instantiation
% 3.81/0.99  
% 3.81/0.99  inst_num_of_clauses:                    1483
% 3.81/0.99  inst_num_in_passive:                    473
% 3.81/0.99  inst_num_in_active:                     780
% 3.81/0.99  inst_num_in_unprocessed:                229
% 3.81/0.99  inst_num_of_loops:                      835
% 3.81/0.99  inst_num_of_learning_restarts:          0
% 3.81/0.99  inst_num_moves_active_passive:          49
% 3.81/0.99  inst_lit_activity:                      0
% 3.81/0.99  inst_lit_activity_moves:                0
% 3.81/0.99  inst_num_tautologies:                   0
% 3.81/0.99  inst_num_prop_implied:                  0
% 3.81/0.99  inst_num_existing_simplified:           0
% 3.81/0.99  inst_num_eq_res_simplified:             0
% 3.81/0.99  inst_num_child_elim:                    0
% 3.81/0.99  inst_num_of_dismatching_blockings:      548
% 3.81/0.99  inst_num_of_non_proper_insts:           1809
% 3.81/0.99  inst_num_of_duplicates:                 0
% 3.81/0.99  inst_inst_num_from_inst_to_res:         0
% 3.81/0.99  inst_dismatching_checking_time:         0.
% 3.81/0.99  
% 3.81/0.99  ------ Resolution
% 3.81/0.99  
% 3.81/0.99  res_num_of_clauses:                     0
% 3.81/0.99  res_num_in_passive:                     0
% 3.81/0.99  res_num_in_active:                      0
% 3.81/0.99  res_num_of_loops:                       130
% 3.81/0.99  res_forward_subset_subsumed:            211
% 3.81/0.99  res_backward_subset_subsumed:           2
% 3.81/0.99  res_forward_subsumed:                   0
% 3.81/0.99  res_backward_subsumed:                  0
% 3.81/0.99  res_forward_subsumption_resolution:     2
% 3.81/0.99  res_backward_subsumption_resolution:    0
% 3.81/0.99  res_clause_to_clause_subsumption:       1113
% 3.81/0.99  res_orphan_elimination:                 0
% 3.81/0.99  res_tautology_del:                      271
% 3.81/0.99  res_num_eq_res_simplified:              0
% 3.81/0.99  res_num_sel_changes:                    0
% 3.81/0.99  res_moves_from_active_to_pass:          0
% 3.81/0.99  
% 3.81/0.99  ------ Superposition
% 3.81/0.99  
% 3.81/0.99  sup_time_total:                         0.
% 3.81/0.99  sup_time_generating:                    0.
% 3.81/0.99  sup_time_sim_full:                      0.
% 3.81/0.99  sup_time_sim_immed:                     0.
% 3.81/0.99  
% 3.81/0.99  sup_num_of_clauses:                     279
% 3.81/0.99  sup_num_in_active:                      159
% 3.81/0.99  sup_num_in_passive:                     120
% 3.81/0.99  sup_num_of_loops:                       166
% 3.81/0.99  sup_fw_superposition:                   165
% 3.81/0.99  sup_bw_superposition:                   158
% 3.81/0.99  sup_immediate_simplified:               130
% 3.81/0.99  sup_given_eliminated:                   0
% 3.81/0.99  comparisons_done:                       0
% 3.81/0.99  comparisons_avoided:                    0
% 3.81/0.99  
% 3.81/0.99  ------ Simplifications
% 3.81/0.99  
% 3.81/0.99  
% 3.81/0.99  sim_fw_subset_subsumed:                 17
% 3.81/0.99  sim_bw_subset_subsumed:                 13
% 3.81/0.99  sim_fw_subsumed:                        16
% 3.81/0.99  sim_bw_subsumed:                        1
% 3.81/0.99  sim_fw_subsumption_res:                 6
% 3.81/0.99  sim_bw_subsumption_res:                 0
% 3.81/0.99  sim_tautology_del:                      6
% 3.81/0.99  sim_eq_tautology_del:                   4
% 3.81/0.99  sim_eq_res_simp:                        0
% 3.81/0.99  sim_fw_demodulated:                     0
% 3.81/0.99  sim_bw_demodulated:                     0
% 3.81/0.99  sim_light_normalised:                   106
% 3.81/0.99  sim_joinable_taut:                      0
% 3.81/0.99  sim_joinable_simp:                      0
% 3.81/0.99  sim_ac_normalised:                      0
% 3.81/0.99  sim_smt_subsumption:                    0
% 3.81/0.99  
%------------------------------------------------------------------------------
