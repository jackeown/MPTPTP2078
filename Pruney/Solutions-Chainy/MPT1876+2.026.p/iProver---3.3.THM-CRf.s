%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:52 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :  237 (1340 expanded)
%              Number of clauses        :  150 ( 327 expanded)
%              Number of leaves         :   26 ( 312 expanded)
%              Depth                    :   27
%              Number of atoms          :  974 (9847 expanded)
%              Number of equality atoms :  238 ( 443 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f2,f48])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f49])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f46,plain,(
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
    inference(flattening,[],[f46])).

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
    inference(nnf_transformation,[],[f47])).

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

fof(f86,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(pure_predicate_removal,[],[f13])).

fof(f38,plain,(
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
    inference(flattening,[],[f38])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f50])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f84,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f85,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f58])).

fof(f74,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f72,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f75,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f87,plain,
    ( v1_zfmisc_1(sK4)
    | v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f58])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
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
    inference(flattening,[],[f36])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_tdlat_3(X1)
      | v7_struct_0(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f63,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f65,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f64,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f69,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f83,plain,(
    v2_tdlat_3(sK3) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f20])).

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
    inference(flattening,[],[f42])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f52])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f82,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK2(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f79,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK2(X0,X1)) = X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f1,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f88,plain,
    ( ~ v1_zfmisc_1(sK4)
    | ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2278,plain,
    ( m1_subset_1(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2267,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_14,plain,
    ( m1_pre_topc(sK1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2271,plain,
    ( m1_pre_topc(sK1(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3848,plain,
    ( m1_pre_topc(sK1(sK3,sK4),sK3) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2267,c_2271])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_30,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_33,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_34,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_35,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2511,plain,
    ( m1_pre_topc(sK1(sK3,sK4),sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2512,plain,
    ( m1_pre_topc(sK1(sK3,sK4),sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2511])).

cnf(c_4221,plain,
    ( m1_pre_topc(sK1(sK3,sK4),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3848,c_30,c_33,c_34,c_35,c_2512])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2272,plain,
    ( u1_struct_0(sK1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3307,plain,
    ( u1_struct_0(sK1(sK3,sK4)) = sK4
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2267,c_2272])).

cnf(c_2506,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(sK4)
    | u1_struct_0(sK1(sK3,sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_3610,plain,
    ( u1_struct_0(sK1(sK3,sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3307,c_29,c_26,c_25,c_24,c_2506])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2275,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3988,plain,
    ( m1_pre_topc(sK1(sK3,sK4),X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) = iProver_top
    | m1_subset_1(X1,sK4) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1(sK3,sK4)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3610,c_2275])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK1(X1,X0))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_3011,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_struct_0(sK1(sK3,sK4))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_3012,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK1(sK3,sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3011])).

cnf(c_4626,plain,
    ( v2_struct_0(X0) = iProver_top
    | m1_subset_1(X1,sK4) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) = iProver_top
    | m1_pre_topc(sK1(sK3,sK4),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3988,c_30,c_33,c_34,c_35,c_3012])).

cnf(c_4627,plain,
    ( m1_pre_topc(sK1(sK3,sK4),X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) = iProver_top
    | m1_subset_1(X1,sK4) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4626])).

cnf(c_4637,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(X0,sK4) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4221,c_4627])).

cnf(c_4642,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4637,c_30,c_33])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2273,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4651,plain,
    ( k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0)
    | m1_subset_1(X0,sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4642,c_2273])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2631,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2686,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2631])).

cnf(c_2687,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2686])).

cnf(c_5058,plain,
    ( m1_subset_1(X0,sK4) != iProver_top
    | k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4651,c_34,c_35,c_2687])).

cnf(c_5059,plain,
    ( k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0)
    | m1_subset_1(X0,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_5058])).

cnf(c_5066,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k1_tarski(sK0(sK4)) ),
    inference(superposition,[status(thm)],[c_2278,c_5059])).

cnf(c_2731,plain,
    ( k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0))
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2278,c_2273])).

cnf(c_2266,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4061,plain,
    ( k6_domain_1(sK4,sK0(sK4)) = k1_tarski(sK0(sK4)) ),
    inference(superposition,[status(thm)],[c_2731,c_2266])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2274,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4071,plain,
    ( m1_subset_1(sK0(sK4),sK4) != iProver_top
    | m1_subset_1(k1_tarski(sK0(sK4)),k1_zfmisc_1(sK4)) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4061,c_2274])).

cnf(c_2676,plain,
    ( m1_subset_1(sK0(sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2677,plain,
    ( m1_subset_1(sK0(sK4),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2676])).

cnf(c_4333,plain,
    ( m1_subset_1(k1_tarski(sK0(sK4)),k1_zfmisc_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4071,c_34,c_2677])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_397,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_3,c_16])).

cnf(c_401,plain,
    ( v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_397,c_2])).

cnf(c_402,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | X1 = X0 ),
    inference(renaming,[status(thm)],[c_401])).

cnf(c_2263,plain,
    ( X0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_402])).

cnf(c_4338,plain,
    ( k1_tarski(sK0(sK4)) = sK4
    | v1_zfmisc_1(sK4) != iProver_top
    | v1_xboole_0(k1_tarski(sK0(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4333,c_2263])).

cnf(c_23,negated_conjecture,
    ( v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(sK4) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_218,plain,
    ( v1_zfmisc_1(sK4)
    | v2_tex_2(sK4,sK3) ),
    inference(prop_impl,[status(thm)],[c_23])).

cnf(c_219,plain,
    ( v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(sK4) ),
    inference(renaming,[status(thm)],[c_218])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_4,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_6,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_379,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_4,c_6])).

cnf(c_423,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_11,c_379])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_427,plain,
    ( v1_zfmisc_1(u1_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v1_tdlat_3(X0)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_423,c_5])).

cnf(c_428,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_427])).

cnf(c_10,plain,
    ( ~ v2_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_447,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_428,c_10])).

cnf(c_27,negated_conjecture,
    ( v2_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_468,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_447,c_27])).

cnf(c_469,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_468])).

cnf(c_473,plain,
    ( v1_zfmisc_1(u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK3)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_469,c_29,c_26])).

cnf(c_474,plain,
    ( ~ m1_pre_topc(X0,sK3)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0)) ),
    inference(renaming,[status(thm)],[c_473])).

cnf(c_19,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tdlat_3(sK2(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_661,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tdlat_3(sK2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_662,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_tdlat_3(sK2(sK3,X0))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_661])).

cnf(c_666,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_tdlat_3(sK2(sK3,X0))
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_662,c_29,c_26])).

cnf(c_756,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_pre_topc(X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(X1)
    | v1_zfmisc_1(u1_struct_0(X1))
    | v1_xboole_0(X0)
    | sK2(sK3,X0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_474,c_666])).

cnf(c_757,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_pre_topc(sK2(sK3,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK2(sK3,X0))
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_756])).

cnf(c_20,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK2(X1,X0))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_637,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK2(X1,X0))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_28])).

cnf(c_638,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_struct_0(sK2(sK3,X0))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_637])).

cnf(c_642,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_struct_0(sK2(sK3,X0))
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_638,c_29,c_26])).

cnf(c_18,plain,
    ( ~ v2_tex_2(X0,X1)
    | m1_pre_topc(sK2(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_685,plain,
    ( ~ v2_tex_2(X0,X1)
    | m1_pre_topc(sK2(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_28])).

cnf(c_686,plain,
    ( ~ v2_tex_2(X0,sK3)
    | m1_pre_topc(sK2(sK3,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_685])).

cnf(c_690,plain,
    ( ~ v2_tex_2(X0,sK3)
    | m1_pre_topc(sK2(sK3,X0),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_686,c_29,c_26])).

cnf(c_761,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_tex_2(X0,sK3)
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_757,c_642,c_690])).

cnf(c_762,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_761])).

cnf(c_998,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
    | v1_zfmisc_1(sK4)
    | v1_xboole_0(X0)
    | sK3 != sK3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_219,c_762])).

cnf(c_999,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
    | v1_zfmisc_1(sK4)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_998])).

cnf(c_1001,plain,
    ( v1_zfmisc_1(sK4)
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_999,c_25,c_24])).

cnf(c_1002,plain,
    ( v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
    | v1_zfmisc_1(sK4) ),
    inference(renaming,[status(thm)],[c_1001])).

cnf(c_1003,plain,
    ( v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) = iProver_top
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1002])).

cnf(c_17,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK2(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_709,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK2(X1,X0)) = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_28])).

cnf(c_710,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(X0)
    | u1_struct_0(sK2(sK3,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_709])).

cnf(c_714,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(X0)
    | u1_struct_0(sK2(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_710,c_29,c_26])).

cnf(c_1012,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_zfmisc_1(sK4)
    | v1_xboole_0(X0)
    | u1_struct_0(sK2(sK3,X0)) = X0
    | sK3 != sK3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_219,c_714])).

cnf(c_1013,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_zfmisc_1(sK4)
    | v1_xboole_0(sK4)
    | u1_struct_0(sK2(sK3,sK4)) = sK4 ),
    inference(unflattening,[status(thm)],[c_1012])).

cnf(c_1015,plain,
    ( v1_zfmisc_1(sK4)
    | u1_struct_0(sK2(sK3,sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1013,c_25,c_24])).

cnf(c_1017,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1015])).

cnf(c_1694,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2577,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1694])).

cnf(c_1695,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2695,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_1695])).

cnf(c_3004,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2695])).

cnf(c_3488,plain,
    ( u1_struct_0(sK2(sK3,sK4)) != sK4
    | sK4 = u1_struct_0(sK2(sK3,sK4))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3004])).

cnf(c_1702,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_zfmisc_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2892,plain,
    ( v1_zfmisc_1(X0)
    | ~ v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
    | X0 != u1_struct_0(sK2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1702])).

cnf(c_3919,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
    | v1_zfmisc_1(sK4)
    | sK4 != u1_struct_0(sK2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2892])).

cnf(c_3920,plain,
    ( sK4 != u1_struct_0(sK2(sK3,sK4))
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) != iProver_top
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3919])).

cnf(c_4952,plain,
    ( k1_tarski(sK0(sK4)) = sK4
    | v1_xboole_0(k1_tarski(sK0(sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4338,c_1003,c_1017,c_2577,c_3488,c_3920])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2279,plain,
    ( v1_xboole_0(k1_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4958,plain,
    ( k1_tarski(sK0(sK4)) = sK4 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4952,c_2279])).

cnf(c_5067,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_5066,c_4958])).

cnf(c_21,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_619,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_28])).

cnf(c_620,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_619])).

cnf(c_624,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_620,c_29,c_26])).

cnf(c_2262,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_624])).

cnf(c_12752,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top
    | m1_subset_1(sK0(sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5067,c_2262])).

cnf(c_2260,plain,
    ( v2_tex_2(X0,sK3) != iProver_top
    | m1_pre_topc(sK2(sK3,X0),sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_690])).

cnf(c_3054,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | m1_pre_topc(sK2(sK3,sK4),sK3) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2267,c_2260])).

cnf(c_3573,plain,
    ( m1_pre_topc(sK2(sK3,sK4),sK3) = iProver_top
    | v2_tex_2(sK4,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3054,c_34])).

cnf(c_3574,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | m1_pre_topc(sK2(sK3,sK4),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_3573])).

cnf(c_3987,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(X0)),u1_struct_0(X1)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2278,c_2275])).

cnf(c_7322,plain,
    ( k6_domain_1(u1_struct_0(X0),sK0(u1_struct_0(X1))) = k1_tarski(sK0(u1_struct_0(X1)))
    | m1_pre_topc(X1,X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3987,c_2273])).

cnf(c_8281,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(u1_struct_0(sK2(sK3,sK4)))) = k1_tarski(sK0(u1_struct_0(sK2(sK3,sK4))))
    | v2_tex_2(sK4,sK3) != iProver_top
    | v2_struct_0(sK2(sK3,sK4)) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3574,c_7322])).

cnf(c_22,negated_conjecture,
    ( ~ v2_tex_2(sK4,sK3)
    | ~ v1_zfmisc_1(sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_37,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v1_zfmisc_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_8513,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8281,c_37,c_1003,c_1017,c_2577,c_3488,c_3920])).

cnf(c_3080,plain,
    ( ~ m1_pre_topc(sK1(sK3,sK4),X0)
    | m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK1(sK3,sK4)))
    | v2_struct_0(X0)
    | v2_struct_0(sK1(sK3,sK4))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_7199,plain,
    ( ~ m1_pre_topc(sK1(sK3,sK4),X0)
    | m1_subset_1(sK0(sK4),u1_struct_0(X0))
    | ~ m1_subset_1(sK0(sK4),u1_struct_0(sK1(sK3,sK4)))
    | v2_struct_0(X0)
    | v2_struct_0(sK1(sK3,sK4))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_3080])).

cnf(c_7200,plain,
    ( m1_pre_topc(sK1(sK3,sK4),X0) != iProver_top
    | m1_subset_1(sK0(sK4),u1_struct_0(X0)) = iProver_top
    | m1_subset_1(sK0(sK4),u1_struct_0(sK1(sK3,sK4))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1(sK3,sK4)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7199])).

cnf(c_7202,plain,
    ( m1_pre_topc(sK1(sK3,sK4),sK3) != iProver_top
    | m1_subset_1(sK0(sK4),u1_struct_0(sK1(sK3,sK4))) != iProver_top
    | m1_subset_1(sK0(sK4),u1_struct_0(sK3)) = iProver_top
    | v2_struct_0(sK1(sK3,sK4)) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7200])).

cnf(c_2863,plain,
    ( sK0(X0) = sK0(X0) ),
    inference(instantiation,[status(thm)],[c_1694])).

cnf(c_5760,plain,
    ( sK0(sK4) = sK0(sK4) ),
    inference(instantiation,[status(thm)],[c_2863])).

cnf(c_1697,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2514,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK0(X2),X2)
    | X1 != X2
    | X0 != sK0(X2) ),
    inference(instantiation,[status(thm)],[c_1697])).

cnf(c_2862,plain,
    ( ~ m1_subset_1(sK0(X0),X0)
    | m1_subset_1(sK0(X0),X1)
    | X1 != X0
    | sK0(X0) != sK0(X0) ),
    inference(instantiation,[status(thm)],[c_2514])).

cnf(c_3521,plain,
    ( ~ m1_subset_1(sK0(X0),X0)
    | m1_subset_1(sK0(X0),u1_struct_0(sK1(sK3,sK4)))
    | u1_struct_0(sK1(sK3,sK4)) != X0
    | sK0(X0) != sK0(X0) ),
    inference(instantiation,[status(thm)],[c_2862])).

cnf(c_4896,plain,
    ( m1_subset_1(sK0(sK4),u1_struct_0(sK1(sK3,sK4)))
    | ~ m1_subset_1(sK0(sK4),sK4)
    | u1_struct_0(sK1(sK3,sK4)) != sK4
    | sK0(sK4) != sK0(sK4) ),
    inference(instantiation,[status(thm)],[c_3521])).

cnf(c_4897,plain,
    ( u1_struct_0(sK1(sK3,sK4)) != sK4
    | sK0(sK4) != sK0(sK4)
    | m1_subset_1(sK0(sK4),u1_struct_0(sK1(sK3,sK4))) = iProver_top
    | m1_subset_1(sK0(sK4),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4896])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12752,c_8513,c_7202,c_5760,c_4897,c_3012,c_2677,c_2512,c_2506,c_35,c_24,c_34,c_25,c_33,c_26,c_30,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:48:01 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.65/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/0.97  
% 3.65/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.65/0.97  
% 3.65/0.97  ------  iProver source info
% 3.65/0.97  
% 3.65/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.65/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.65/0.97  git: non_committed_changes: false
% 3.65/0.97  git: last_make_outside_of_git: false
% 3.65/0.97  
% 3.65/0.97  ------ 
% 3.65/0.97  
% 3.65/0.97  ------ Input Options
% 3.65/0.97  
% 3.65/0.97  --out_options                           all
% 3.65/0.97  --tptp_safe_out                         true
% 3.65/0.97  --problem_path                          ""
% 3.65/0.97  --include_path                          ""
% 3.65/0.97  --clausifier                            res/vclausify_rel
% 3.65/0.97  --clausifier_options                    --mode clausify
% 3.65/0.97  --stdin                                 false
% 3.65/0.97  --stats_out                             all
% 3.65/0.97  
% 3.65/0.97  ------ General Options
% 3.65/0.97  
% 3.65/0.97  --fof                                   false
% 3.65/0.97  --time_out_real                         305.
% 3.65/0.97  --time_out_virtual                      -1.
% 3.65/0.97  --symbol_type_check                     false
% 3.65/0.97  --clausify_out                          false
% 3.65/0.97  --sig_cnt_out                           false
% 3.65/0.97  --trig_cnt_out                          false
% 3.65/0.97  --trig_cnt_out_tolerance                1.
% 3.65/0.97  --trig_cnt_out_sk_spl                   false
% 3.65/0.97  --abstr_cl_out                          false
% 3.65/0.97  
% 3.65/0.97  ------ Global Options
% 3.65/0.97  
% 3.65/0.97  --schedule                              default
% 3.65/0.97  --add_important_lit                     false
% 3.65/0.97  --prop_solver_per_cl                    1000
% 3.65/0.97  --min_unsat_core                        false
% 3.65/0.97  --soft_assumptions                      false
% 3.65/0.97  --soft_lemma_size                       3
% 3.65/0.97  --prop_impl_unit_size                   0
% 3.65/0.97  --prop_impl_unit                        []
% 3.65/0.97  --share_sel_clauses                     true
% 3.65/0.97  --reset_solvers                         false
% 3.65/0.97  --bc_imp_inh                            [conj_cone]
% 3.65/0.97  --conj_cone_tolerance                   3.
% 3.65/0.97  --extra_neg_conj                        none
% 3.65/0.97  --large_theory_mode                     true
% 3.65/0.97  --prolific_symb_bound                   200
% 3.65/0.97  --lt_threshold                          2000
% 3.65/0.97  --clause_weak_htbl                      true
% 3.65/0.97  --gc_record_bc_elim                     false
% 3.65/0.97  
% 3.65/0.97  ------ Preprocessing Options
% 3.65/0.97  
% 3.65/0.97  --preprocessing_flag                    true
% 3.65/0.97  --time_out_prep_mult                    0.1
% 3.65/0.97  --splitting_mode                        input
% 3.65/0.97  --splitting_grd                         true
% 3.65/0.97  --splitting_cvd                         false
% 3.65/0.97  --splitting_cvd_svl                     false
% 3.65/0.97  --splitting_nvd                         32
% 3.65/0.97  --sub_typing                            true
% 3.65/0.97  --prep_gs_sim                           true
% 3.65/0.97  --prep_unflatten                        true
% 3.65/0.97  --prep_res_sim                          true
% 3.65/0.97  --prep_upred                            true
% 3.65/0.97  --prep_sem_filter                       exhaustive
% 3.65/0.97  --prep_sem_filter_out                   false
% 3.65/0.97  --pred_elim                             true
% 3.65/0.97  --res_sim_input                         true
% 3.65/0.97  --eq_ax_congr_red                       true
% 3.65/0.97  --pure_diseq_elim                       true
% 3.65/0.97  --brand_transform                       false
% 3.65/0.97  --non_eq_to_eq                          false
% 3.65/0.97  --prep_def_merge                        true
% 3.65/0.97  --prep_def_merge_prop_impl              false
% 3.65/0.97  --prep_def_merge_mbd                    true
% 3.65/0.97  --prep_def_merge_tr_red                 false
% 3.65/0.97  --prep_def_merge_tr_cl                  false
% 3.65/0.97  --smt_preprocessing                     true
% 3.65/0.97  --smt_ac_axioms                         fast
% 3.65/0.97  --preprocessed_out                      false
% 3.65/0.97  --preprocessed_stats                    false
% 3.65/0.97  
% 3.65/0.97  ------ Abstraction refinement Options
% 3.65/0.97  
% 3.65/0.97  --abstr_ref                             []
% 3.65/0.97  --abstr_ref_prep                        false
% 3.65/0.97  --abstr_ref_until_sat                   false
% 3.65/0.97  --abstr_ref_sig_restrict                funpre
% 3.65/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.65/0.97  --abstr_ref_under                       []
% 3.65/0.97  
% 3.65/0.97  ------ SAT Options
% 3.65/0.97  
% 3.65/0.97  --sat_mode                              false
% 3.65/0.97  --sat_fm_restart_options                ""
% 3.65/0.97  --sat_gr_def                            false
% 3.65/0.97  --sat_epr_types                         true
% 3.65/0.97  --sat_non_cyclic_types                  false
% 3.65/0.97  --sat_finite_models                     false
% 3.65/0.97  --sat_fm_lemmas                         false
% 3.65/0.97  --sat_fm_prep                           false
% 3.65/0.97  --sat_fm_uc_incr                        true
% 3.65/0.97  --sat_out_model                         small
% 3.65/0.97  --sat_out_clauses                       false
% 3.65/0.97  
% 3.65/0.97  ------ QBF Options
% 3.65/0.97  
% 3.65/0.97  --qbf_mode                              false
% 3.65/0.97  --qbf_elim_univ                         false
% 3.65/0.97  --qbf_dom_inst                          none
% 3.65/0.97  --qbf_dom_pre_inst                      false
% 3.65/0.97  --qbf_sk_in                             false
% 3.65/0.97  --qbf_pred_elim                         true
% 3.65/0.97  --qbf_split                             512
% 3.65/0.97  
% 3.65/0.97  ------ BMC1 Options
% 3.65/0.97  
% 3.65/0.97  --bmc1_incremental                      false
% 3.65/0.97  --bmc1_axioms                           reachable_all
% 3.65/0.97  --bmc1_min_bound                        0
% 3.65/0.97  --bmc1_max_bound                        -1
% 3.65/0.97  --bmc1_max_bound_default                -1
% 3.65/0.97  --bmc1_symbol_reachability              true
% 3.65/0.97  --bmc1_property_lemmas                  false
% 3.65/0.97  --bmc1_k_induction                      false
% 3.65/0.97  --bmc1_non_equiv_states                 false
% 3.65/0.97  --bmc1_deadlock                         false
% 3.65/0.97  --bmc1_ucm                              false
% 3.65/0.97  --bmc1_add_unsat_core                   none
% 3.65/0.97  --bmc1_unsat_core_children              false
% 3.65/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.65/0.97  --bmc1_out_stat                         full
% 3.65/0.97  --bmc1_ground_init                      false
% 3.65/0.97  --bmc1_pre_inst_next_state              false
% 3.65/0.97  --bmc1_pre_inst_state                   false
% 3.65/0.97  --bmc1_pre_inst_reach_state             false
% 3.65/0.97  --bmc1_out_unsat_core                   false
% 3.65/0.97  --bmc1_aig_witness_out                  false
% 3.65/0.97  --bmc1_verbose                          false
% 3.65/0.97  --bmc1_dump_clauses_tptp                false
% 3.65/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.65/0.97  --bmc1_dump_file                        -
% 3.65/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.65/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.65/0.97  --bmc1_ucm_extend_mode                  1
% 3.65/0.97  --bmc1_ucm_init_mode                    2
% 3.65/0.97  --bmc1_ucm_cone_mode                    none
% 3.65/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.65/0.97  --bmc1_ucm_relax_model                  4
% 3.65/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.65/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.65/0.97  --bmc1_ucm_layered_model                none
% 3.65/0.97  --bmc1_ucm_max_lemma_size               10
% 3.65/0.97  
% 3.65/0.97  ------ AIG Options
% 3.65/0.97  
% 3.65/0.97  --aig_mode                              false
% 3.65/0.97  
% 3.65/0.97  ------ Instantiation Options
% 3.65/0.97  
% 3.65/0.97  --instantiation_flag                    true
% 3.65/0.97  --inst_sos_flag                         false
% 3.65/0.97  --inst_sos_phase                        true
% 3.65/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.65/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.65/0.97  --inst_lit_sel_side                     num_symb
% 3.65/0.97  --inst_solver_per_active                1400
% 3.65/0.97  --inst_solver_calls_frac                1.
% 3.65/0.97  --inst_passive_queue_type               priority_queues
% 3.65/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.65/0.97  --inst_passive_queues_freq              [25;2]
% 3.65/0.97  --inst_dismatching                      true
% 3.65/0.97  --inst_eager_unprocessed_to_passive     true
% 3.65/0.97  --inst_prop_sim_given                   true
% 3.65/0.97  --inst_prop_sim_new                     false
% 3.65/0.97  --inst_subs_new                         false
% 3.65/0.97  --inst_eq_res_simp                      false
% 3.65/0.97  --inst_subs_given                       false
% 3.65/0.97  --inst_orphan_elimination               true
% 3.65/0.97  --inst_learning_loop_flag               true
% 3.65/0.97  --inst_learning_start                   3000
% 3.65/0.97  --inst_learning_factor                  2
% 3.65/0.97  --inst_start_prop_sim_after_learn       3
% 3.65/0.97  --inst_sel_renew                        solver
% 3.65/0.97  --inst_lit_activity_flag                true
% 3.65/0.97  --inst_restr_to_given                   false
% 3.65/0.97  --inst_activity_threshold               500
% 3.65/0.97  --inst_out_proof                        true
% 3.65/0.97  
% 3.65/0.97  ------ Resolution Options
% 3.65/0.97  
% 3.65/0.97  --resolution_flag                       true
% 3.65/0.97  --res_lit_sel                           adaptive
% 3.65/0.97  --res_lit_sel_side                      none
% 3.65/0.97  --res_ordering                          kbo
% 3.65/0.97  --res_to_prop_solver                    active
% 3.65/0.97  --res_prop_simpl_new                    false
% 3.65/0.97  --res_prop_simpl_given                  true
% 3.65/0.97  --res_passive_queue_type                priority_queues
% 3.65/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.65/0.98  --res_passive_queues_freq               [15;5]
% 3.65/0.98  --res_forward_subs                      full
% 3.65/0.98  --res_backward_subs                     full
% 3.65/0.98  --res_forward_subs_resolution           true
% 3.65/0.98  --res_backward_subs_resolution          true
% 3.65/0.98  --res_orphan_elimination                true
% 3.65/0.98  --res_time_limit                        2.
% 3.65/0.98  --res_out_proof                         true
% 3.65/0.98  
% 3.65/0.98  ------ Superposition Options
% 3.65/0.98  
% 3.65/0.98  --superposition_flag                    true
% 3.65/0.98  --sup_passive_queue_type                priority_queues
% 3.65/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.65/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.65/0.98  --demod_completeness_check              fast
% 3.65/0.98  --demod_use_ground                      true
% 3.65/0.98  --sup_to_prop_solver                    passive
% 3.65/0.98  --sup_prop_simpl_new                    true
% 3.65/0.98  --sup_prop_simpl_given                  true
% 3.65/0.98  --sup_fun_splitting                     false
% 3.65/0.98  --sup_smt_interval                      50000
% 3.65/0.98  
% 3.65/0.98  ------ Superposition Simplification Setup
% 3.65/0.98  
% 3.65/0.98  --sup_indices_passive                   []
% 3.65/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.65/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/0.98  --sup_full_bw                           [BwDemod]
% 3.65/0.98  --sup_immed_triv                        [TrivRules]
% 3.65/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/0.98  --sup_immed_bw_main                     []
% 3.65/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.65/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.65/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.65/0.98  
% 3.65/0.98  ------ Combination Options
% 3.65/0.98  
% 3.65/0.98  --comb_res_mult                         3
% 3.65/0.98  --comb_sup_mult                         2
% 3.65/0.98  --comb_inst_mult                        10
% 3.65/0.98  
% 3.65/0.98  ------ Debug Options
% 3.65/0.98  
% 3.65/0.98  --dbg_backtrace                         false
% 3.65/0.98  --dbg_dump_prop_clauses                 false
% 3.65/0.98  --dbg_dump_prop_clauses_file            -
% 3.65/0.98  --dbg_out_stat                          false
% 3.65/0.98  ------ Parsing...
% 3.65/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.65/0.98  
% 3.65/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.65/0.98  
% 3.65/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.65/0.98  
% 3.65/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/0.98  ------ Proving...
% 3.65/0.98  ------ Problem Properties 
% 3.65/0.98  
% 3.65/0.98  
% 3.65/0.98  clauses                                 22
% 3.65/0.98  conjectures                             6
% 3.65/0.98  EPR                                     6
% 3.65/0.98  Horn                                    11
% 3.65/0.98  unary                                   6
% 3.65/0.98  binary                                  3
% 3.65/0.98  lits                                    65
% 3.65/0.98  lits eq                                 4
% 3.65/0.98  fd_pure                                 0
% 3.65/0.98  fd_pseudo                               0
% 3.65/0.98  fd_cond                                 0
% 3.65/0.98  fd_pseudo_cond                          1
% 3.65/0.98  AC symbols                              0
% 3.65/0.98  
% 3.65/0.98  ------ Schedule dynamic 5 is on 
% 3.65/0.98  
% 3.65/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.65/0.98  
% 3.65/0.98  
% 3.65/0.98  ------ 
% 3.65/0.98  Current options:
% 3.65/0.98  ------ 
% 3.65/0.98  
% 3.65/0.98  ------ Input Options
% 3.65/0.98  
% 3.65/0.98  --out_options                           all
% 3.65/0.98  --tptp_safe_out                         true
% 3.65/0.98  --problem_path                          ""
% 3.65/0.98  --include_path                          ""
% 3.65/0.98  --clausifier                            res/vclausify_rel
% 3.65/0.98  --clausifier_options                    --mode clausify
% 3.65/0.98  --stdin                                 false
% 3.65/0.98  --stats_out                             all
% 3.65/0.98  
% 3.65/0.98  ------ General Options
% 3.65/0.98  
% 3.65/0.98  --fof                                   false
% 3.65/0.98  --time_out_real                         305.
% 3.65/0.98  --time_out_virtual                      -1.
% 3.65/0.98  --symbol_type_check                     false
% 3.65/0.98  --clausify_out                          false
% 3.65/0.98  --sig_cnt_out                           false
% 3.65/0.98  --trig_cnt_out                          false
% 3.65/0.98  --trig_cnt_out_tolerance                1.
% 3.65/0.98  --trig_cnt_out_sk_spl                   false
% 3.65/0.98  --abstr_cl_out                          false
% 3.65/0.98  
% 3.65/0.98  ------ Global Options
% 3.65/0.98  
% 3.65/0.98  --schedule                              default
% 3.65/0.98  --add_important_lit                     false
% 3.65/0.98  --prop_solver_per_cl                    1000
% 3.65/0.98  --min_unsat_core                        false
% 3.65/0.98  --soft_assumptions                      false
% 3.65/0.98  --soft_lemma_size                       3
% 3.65/0.98  --prop_impl_unit_size                   0
% 3.65/0.98  --prop_impl_unit                        []
% 3.65/0.98  --share_sel_clauses                     true
% 3.65/0.98  --reset_solvers                         false
% 3.65/0.98  --bc_imp_inh                            [conj_cone]
% 3.65/0.98  --conj_cone_tolerance                   3.
% 3.65/0.98  --extra_neg_conj                        none
% 3.65/0.98  --large_theory_mode                     true
% 3.65/0.98  --prolific_symb_bound                   200
% 3.65/0.98  --lt_threshold                          2000
% 3.65/0.98  --clause_weak_htbl                      true
% 3.65/0.98  --gc_record_bc_elim                     false
% 3.65/0.98  
% 3.65/0.98  ------ Preprocessing Options
% 3.65/0.98  
% 3.65/0.98  --preprocessing_flag                    true
% 3.65/0.98  --time_out_prep_mult                    0.1
% 3.65/0.98  --splitting_mode                        input
% 3.65/0.98  --splitting_grd                         true
% 3.65/0.98  --splitting_cvd                         false
% 3.65/0.98  --splitting_cvd_svl                     false
% 3.65/0.98  --splitting_nvd                         32
% 3.65/0.98  --sub_typing                            true
% 3.65/0.98  --prep_gs_sim                           true
% 3.65/0.98  --prep_unflatten                        true
% 3.65/0.98  --prep_res_sim                          true
% 3.65/0.98  --prep_upred                            true
% 3.65/0.98  --prep_sem_filter                       exhaustive
% 3.65/0.98  --prep_sem_filter_out                   false
% 3.65/0.98  --pred_elim                             true
% 3.65/0.98  --res_sim_input                         true
% 3.65/0.98  --eq_ax_congr_red                       true
% 3.65/0.98  --pure_diseq_elim                       true
% 3.65/0.98  --brand_transform                       false
% 3.65/0.98  --non_eq_to_eq                          false
% 3.65/0.98  --prep_def_merge                        true
% 3.65/0.98  --prep_def_merge_prop_impl              false
% 3.65/0.98  --prep_def_merge_mbd                    true
% 3.65/0.98  --prep_def_merge_tr_red                 false
% 3.65/0.98  --prep_def_merge_tr_cl                  false
% 3.65/0.98  --smt_preprocessing                     true
% 3.65/0.98  --smt_ac_axioms                         fast
% 3.65/0.98  --preprocessed_out                      false
% 3.65/0.98  --preprocessed_stats                    false
% 3.65/0.98  
% 3.65/0.98  ------ Abstraction refinement Options
% 3.65/0.98  
% 3.65/0.98  --abstr_ref                             []
% 3.65/0.98  --abstr_ref_prep                        false
% 3.65/0.98  --abstr_ref_until_sat                   false
% 3.65/0.98  --abstr_ref_sig_restrict                funpre
% 3.65/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.65/0.98  --abstr_ref_under                       []
% 3.65/0.98  
% 3.65/0.98  ------ SAT Options
% 3.65/0.98  
% 3.65/0.98  --sat_mode                              false
% 3.65/0.98  --sat_fm_restart_options                ""
% 3.65/0.98  --sat_gr_def                            false
% 3.65/0.98  --sat_epr_types                         true
% 3.65/0.98  --sat_non_cyclic_types                  false
% 3.65/0.98  --sat_finite_models                     false
% 3.65/0.98  --sat_fm_lemmas                         false
% 3.65/0.98  --sat_fm_prep                           false
% 3.65/0.98  --sat_fm_uc_incr                        true
% 3.65/0.98  --sat_out_model                         small
% 3.65/0.98  --sat_out_clauses                       false
% 3.65/0.98  
% 3.65/0.98  ------ QBF Options
% 3.65/0.98  
% 3.65/0.98  --qbf_mode                              false
% 3.65/0.98  --qbf_elim_univ                         false
% 3.65/0.98  --qbf_dom_inst                          none
% 3.65/0.98  --qbf_dom_pre_inst                      false
% 3.65/0.98  --qbf_sk_in                             false
% 3.65/0.98  --qbf_pred_elim                         true
% 3.65/0.98  --qbf_split                             512
% 3.65/0.98  
% 3.65/0.98  ------ BMC1 Options
% 3.65/0.98  
% 3.65/0.98  --bmc1_incremental                      false
% 3.65/0.98  --bmc1_axioms                           reachable_all
% 3.65/0.98  --bmc1_min_bound                        0
% 3.65/0.98  --bmc1_max_bound                        -1
% 3.65/0.98  --bmc1_max_bound_default                -1
% 3.65/0.98  --bmc1_symbol_reachability              true
% 3.65/0.98  --bmc1_property_lemmas                  false
% 3.65/0.98  --bmc1_k_induction                      false
% 3.65/0.98  --bmc1_non_equiv_states                 false
% 3.65/0.98  --bmc1_deadlock                         false
% 3.65/0.98  --bmc1_ucm                              false
% 3.65/0.98  --bmc1_add_unsat_core                   none
% 3.65/0.98  --bmc1_unsat_core_children              false
% 3.65/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.65/0.98  --bmc1_out_stat                         full
% 3.65/0.98  --bmc1_ground_init                      false
% 3.65/0.98  --bmc1_pre_inst_next_state              false
% 3.65/0.98  --bmc1_pre_inst_state                   false
% 3.65/0.98  --bmc1_pre_inst_reach_state             false
% 3.65/0.98  --bmc1_out_unsat_core                   false
% 3.65/0.98  --bmc1_aig_witness_out                  false
% 3.65/0.98  --bmc1_verbose                          false
% 3.65/0.98  --bmc1_dump_clauses_tptp                false
% 3.65/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.65/0.98  --bmc1_dump_file                        -
% 3.65/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.65/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.65/0.98  --bmc1_ucm_extend_mode                  1
% 3.65/0.98  --bmc1_ucm_init_mode                    2
% 3.65/0.98  --bmc1_ucm_cone_mode                    none
% 3.65/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.65/0.98  --bmc1_ucm_relax_model                  4
% 3.65/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.65/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.65/0.98  --bmc1_ucm_layered_model                none
% 3.65/0.98  --bmc1_ucm_max_lemma_size               10
% 3.65/0.98  
% 3.65/0.98  ------ AIG Options
% 3.65/0.98  
% 3.65/0.98  --aig_mode                              false
% 3.65/0.98  
% 3.65/0.98  ------ Instantiation Options
% 3.65/0.98  
% 3.65/0.98  --instantiation_flag                    true
% 3.65/0.98  --inst_sos_flag                         false
% 3.65/0.98  --inst_sos_phase                        true
% 3.65/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.65/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.65/0.98  --inst_lit_sel_side                     none
% 3.65/0.98  --inst_solver_per_active                1400
% 3.65/0.98  --inst_solver_calls_frac                1.
% 3.65/0.98  --inst_passive_queue_type               priority_queues
% 3.65/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.65/0.98  --inst_passive_queues_freq              [25;2]
% 3.65/0.98  --inst_dismatching                      true
% 3.65/0.98  --inst_eager_unprocessed_to_passive     true
% 3.65/0.98  --inst_prop_sim_given                   true
% 3.65/0.98  --inst_prop_sim_new                     false
% 3.65/0.98  --inst_subs_new                         false
% 3.65/0.98  --inst_eq_res_simp                      false
% 3.65/0.98  --inst_subs_given                       false
% 3.65/0.98  --inst_orphan_elimination               true
% 3.65/0.98  --inst_learning_loop_flag               true
% 3.65/0.98  --inst_learning_start                   3000
% 3.65/0.98  --inst_learning_factor                  2
% 3.65/0.98  --inst_start_prop_sim_after_learn       3
% 3.65/0.98  --inst_sel_renew                        solver
% 3.65/0.98  --inst_lit_activity_flag                true
% 3.65/0.98  --inst_restr_to_given                   false
% 3.65/0.98  --inst_activity_threshold               500
% 3.65/0.98  --inst_out_proof                        true
% 3.65/0.98  
% 3.65/0.98  ------ Resolution Options
% 3.65/0.98  
% 3.65/0.98  --resolution_flag                       false
% 3.65/0.98  --res_lit_sel                           adaptive
% 3.65/0.98  --res_lit_sel_side                      none
% 3.65/0.98  --res_ordering                          kbo
% 3.65/0.98  --res_to_prop_solver                    active
% 3.65/0.98  --res_prop_simpl_new                    false
% 3.65/0.98  --res_prop_simpl_given                  true
% 3.65/0.98  --res_passive_queue_type                priority_queues
% 3.65/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.65/0.98  --res_passive_queues_freq               [15;5]
% 3.65/0.98  --res_forward_subs                      full
% 3.65/0.98  --res_backward_subs                     full
% 3.65/0.98  --res_forward_subs_resolution           true
% 3.65/0.98  --res_backward_subs_resolution          true
% 3.65/0.98  --res_orphan_elimination                true
% 3.65/0.98  --res_time_limit                        2.
% 3.65/0.98  --res_out_proof                         true
% 3.65/0.98  
% 3.65/0.98  ------ Superposition Options
% 3.65/0.98  
% 3.65/0.98  --superposition_flag                    true
% 3.65/0.98  --sup_passive_queue_type                priority_queues
% 3.65/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.65/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.65/0.98  --demod_completeness_check              fast
% 3.65/0.98  --demod_use_ground                      true
% 3.65/0.98  --sup_to_prop_solver                    passive
% 3.65/0.98  --sup_prop_simpl_new                    true
% 3.65/0.98  --sup_prop_simpl_given                  true
% 3.65/0.98  --sup_fun_splitting                     false
% 3.65/0.98  --sup_smt_interval                      50000
% 3.65/0.98  
% 3.65/0.98  ------ Superposition Simplification Setup
% 3.65/0.98  
% 3.65/0.98  --sup_indices_passive                   []
% 3.65/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.65/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/0.98  --sup_full_bw                           [BwDemod]
% 3.65/0.98  --sup_immed_triv                        [TrivRules]
% 3.65/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/0.98  --sup_immed_bw_main                     []
% 3.65/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.65/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.65/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.65/0.98  
% 3.65/0.98  ------ Combination Options
% 3.65/0.98  
% 3.65/0.98  --comb_res_mult                         3
% 3.65/0.98  --comb_sup_mult                         2
% 3.65/0.98  --comb_inst_mult                        10
% 3.65/0.98  
% 3.65/0.98  ------ Debug Options
% 3.65/0.98  
% 3.65/0.98  --dbg_backtrace                         false
% 3.65/0.98  --dbg_dump_prop_clauses                 false
% 3.65/0.98  --dbg_dump_prop_clauses_file            -
% 3.65/0.98  --dbg_out_stat                          false
% 3.65/0.98  
% 3.65/0.98  
% 3.65/0.98  
% 3.65/0.98  
% 3.65/0.98  ------ Proving...
% 3.65/0.98  
% 3.65/0.98  
% 3.65/0.98  % SZS status Theorem for theBenchmark.p
% 3.65/0.98  
% 3.65/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.65/0.98  
% 3.65/0.98  fof(f2,axiom,(
% 3.65/0.98    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f48,plain,(
% 3.65/0.98    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK0(X0),X0))),
% 3.65/0.98    introduced(choice_axiom,[])).
% 3.65/0.98  
% 3.65/0.98  fof(f49,plain,(
% 3.65/0.98    ! [X0] : m1_subset_1(sK0(X0),X0)),
% 3.65/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f2,f48])).
% 3.65/0.98  
% 3.65/0.98  fof(f60,plain,(
% 3.65/0.98    ( ! [X0] : (m1_subset_1(sK0(X0),X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f49])).
% 3.65/0.98  
% 3.65/0.98  fof(f17,conjecture,(
% 3.65/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f18,negated_conjecture,(
% 3.65/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 3.65/0.98    inference(negated_conjecture,[],[f17])).
% 3.65/0.98  
% 3.65/0.98  fof(f46,plain,(
% 3.65/0.98    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.65/0.98    inference(ennf_transformation,[],[f18])).
% 3.65/0.98  
% 3.65/0.98  fof(f47,plain,(
% 3.65/0.98    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.65/0.98    inference(flattening,[],[f46])).
% 3.65/0.98  
% 3.65/0.98  fof(f54,plain,(
% 3.65/0.98    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.65/0.98    inference(nnf_transformation,[],[f47])).
% 3.65/0.98  
% 3.65/0.98  fof(f55,plain,(
% 3.65/0.98    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.65/0.98    inference(flattening,[],[f54])).
% 3.65/0.98  
% 3.65/0.98  fof(f57,plain,(
% 3.65/0.98    ( ! [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,X0)) & (v1_zfmisc_1(sK4) | v2_tex_2(sK4,X0)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK4))) )),
% 3.65/0.98    introduced(choice_axiom,[])).
% 3.65/0.98  
% 3.65/0.98  fof(f56,plain,(
% 3.65/0.98    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK3)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 3.65/0.98    introduced(choice_axiom,[])).
% 3.65/0.98  
% 3.65/0.98  fof(f58,plain,(
% 3.65/0.98    ((~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3)) & (v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 3.65/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f55,f57,f56])).
% 3.65/0.98  
% 3.65/0.98  fof(f86,plain,(
% 3.65/0.98    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 3.65/0.98    inference(cnf_transformation,[],[f58])).
% 3.65/0.98  
% 3.65/0.98  fof(f13,axiom,(
% 3.65/0.98    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f21,plain,(
% 3.65/0.98    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2))))),
% 3.65/0.98    inference(pure_predicate_removal,[],[f13])).
% 3.65/0.98  
% 3.65/0.98  fof(f38,plain,(
% 3.65/0.98    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.65/0.98    inference(ennf_transformation,[],[f21])).
% 3.65/0.98  
% 3.65/0.98  fof(f39,plain,(
% 3.65/0.98    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.65/0.98    inference(flattening,[],[f38])).
% 3.65/0.98  
% 3.65/0.98  fof(f50,plain,(
% 3.65/0.98    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(sK1(X0,X1)) = X1 & m1_pre_topc(sK1(X0,X1),X0) & ~v2_struct_0(sK1(X0,X1))))),
% 3.65/0.98    introduced(choice_axiom,[])).
% 3.65/0.98  
% 3.65/0.98  fof(f51,plain,(
% 3.65/0.98    ! [X0] : (! [X1] : ((u1_struct_0(sK1(X0,X1)) = X1 & m1_pre_topc(sK1(X0,X1),X0) & ~v2_struct_0(sK1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.65/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f50])).
% 3.65/0.98  
% 3.65/0.98  fof(f73,plain,(
% 3.65/0.98    ( ! [X0,X1] : (m1_pre_topc(sK1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f51])).
% 3.65/0.98  
% 3.65/0.98  fof(f81,plain,(
% 3.65/0.98    ~v2_struct_0(sK3)),
% 3.65/0.98    inference(cnf_transformation,[],[f58])).
% 3.65/0.98  
% 3.65/0.98  fof(f84,plain,(
% 3.65/0.98    l1_pre_topc(sK3)),
% 3.65/0.98    inference(cnf_transformation,[],[f58])).
% 3.65/0.98  
% 3.65/0.98  fof(f85,plain,(
% 3.65/0.98    ~v1_xboole_0(sK4)),
% 3.65/0.98    inference(cnf_transformation,[],[f58])).
% 3.65/0.98  
% 3.65/0.98  fof(f74,plain,(
% 3.65/0.98    ( ! [X0,X1] : (u1_struct_0(sK1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f51])).
% 3.65/0.98  
% 3.65/0.98  fof(f8,axiom,(
% 3.65/0.98    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f28,plain,(
% 3.65/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.65/0.98    inference(ennf_transformation,[],[f8])).
% 3.65/0.98  
% 3.65/0.98  fof(f29,plain,(
% 3.65/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.65/0.98    inference(flattening,[],[f28])).
% 3.65/0.98  
% 3.65/0.98  fof(f66,plain,(
% 3.65/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f29])).
% 3.65/0.98  
% 3.65/0.98  fof(f72,plain,(
% 3.65/0.98    ( ! [X0,X1] : (~v2_struct_0(sK1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f51])).
% 3.65/0.98  
% 3.65/0.98  fof(f10,axiom,(
% 3.65/0.98    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f32,plain,(
% 3.65/0.98    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.65/0.98    inference(ennf_transformation,[],[f10])).
% 3.65/0.98  
% 3.65/0.98  fof(f33,plain,(
% 3.65/0.98    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.65/0.98    inference(flattening,[],[f32])).
% 3.65/0.98  
% 3.65/0.98  fof(f68,plain,(
% 3.65/0.98    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f33])).
% 3.65/0.98  
% 3.65/0.98  fof(f3,axiom,(
% 3.65/0.98    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f22,plain,(
% 3.65/0.98    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.65/0.98    inference(ennf_transformation,[],[f3])).
% 3.65/0.98  
% 3.65/0.98  fof(f61,plain,(
% 3.65/0.98    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f22])).
% 3.65/0.98  
% 3.65/0.98  fof(f9,axiom,(
% 3.65/0.98    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f30,plain,(
% 3.65/0.98    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.65/0.98    inference(ennf_transformation,[],[f9])).
% 3.65/0.98  
% 3.65/0.98  fof(f31,plain,(
% 3.65/0.98    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.65/0.98    inference(flattening,[],[f30])).
% 3.65/0.98  
% 3.65/0.98  fof(f67,plain,(
% 3.65/0.98    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f31])).
% 3.65/0.98  
% 3.65/0.98  fof(f4,axiom,(
% 3.65/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f19,plain,(
% 3.65/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 3.65/0.98    inference(unused_predicate_definition_removal,[],[f4])).
% 3.65/0.98  
% 3.65/0.98  fof(f23,plain,(
% 3.65/0.98    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 3.65/0.98    inference(ennf_transformation,[],[f19])).
% 3.65/0.98  
% 3.65/0.98  fof(f62,plain,(
% 3.65/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.65/0.98    inference(cnf_transformation,[],[f23])).
% 3.65/0.98  
% 3.65/0.98  fof(f14,axiom,(
% 3.65/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f40,plain,(
% 3.65/0.98    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 3.65/0.98    inference(ennf_transformation,[],[f14])).
% 3.65/0.98  
% 3.65/0.98  fof(f41,plain,(
% 3.65/0.98    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.65/0.98    inference(flattening,[],[f40])).
% 3.65/0.98  
% 3.65/0.98  fof(f75,plain,(
% 3.65/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f41])).
% 3.65/0.98  
% 3.65/0.98  fof(f87,plain,(
% 3.65/0.98    v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3)),
% 3.65/0.98    inference(cnf_transformation,[],[f58])).
% 3.65/0.98  
% 3.65/0.98  fof(f12,axiom,(
% 3.65/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((~v7_struct_0(X1) & ~v2_struct_0(X1)) => (~v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f36,plain,(
% 3.65/0.98    ! [X0] : (! [X1] : (((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (v7_struct_0(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.65/0.98    inference(ennf_transformation,[],[f12])).
% 3.65/0.98  
% 3.65/0.98  fof(f37,plain,(
% 3.65/0.98    ! [X0] : (! [X1] : ((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.65/0.98    inference(flattening,[],[f36])).
% 3.65/0.98  
% 3.65/0.98  fof(f71,plain,(
% 3.65/0.98    ( ! [X0,X1] : (~v1_tdlat_3(X1) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f37])).
% 3.65/0.98  
% 3.65/0.98  fof(f5,axiom,(
% 3.65/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f24,plain,(
% 3.65/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.65/0.98    inference(ennf_transformation,[],[f5])).
% 3.65/0.98  
% 3.65/0.98  fof(f63,plain,(
% 3.65/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f24])).
% 3.65/0.98  
% 3.65/0.98  fof(f7,axiom,(
% 3.65/0.98    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f26,plain,(
% 3.65/0.98    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 3.65/0.98    inference(ennf_transformation,[],[f7])).
% 3.65/0.98  
% 3.65/0.98  fof(f27,plain,(
% 3.65/0.98    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 3.65/0.98    inference(flattening,[],[f26])).
% 3.65/0.98  
% 3.65/0.98  fof(f65,plain,(
% 3.65/0.98    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f27])).
% 3.65/0.98  
% 3.65/0.98  fof(f6,axiom,(
% 3.65/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f25,plain,(
% 3.65/0.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.65/0.98    inference(ennf_transformation,[],[f6])).
% 3.65/0.98  
% 3.65/0.98  fof(f64,plain,(
% 3.65/0.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f25])).
% 3.65/0.98  
% 3.65/0.98  fof(f11,axiom,(
% 3.65/0.98    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f34,plain,(
% 3.65/0.98    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 3.65/0.98    inference(ennf_transformation,[],[f11])).
% 3.65/0.98  
% 3.65/0.98  fof(f35,plain,(
% 3.65/0.98    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 3.65/0.98    inference(flattening,[],[f34])).
% 3.65/0.98  
% 3.65/0.98  fof(f69,plain,(
% 3.65/0.98    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f35])).
% 3.65/0.98  
% 3.65/0.98  fof(f83,plain,(
% 3.65/0.98    v2_tdlat_3(sK3)),
% 3.65/0.98    inference(cnf_transformation,[],[f58])).
% 3.65/0.98  
% 3.65/0.98  fof(f15,axiom,(
% 3.65/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f20,plain,(
% 3.65/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 3.65/0.98    inference(pure_predicate_removal,[],[f15])).
% 3.65/0.98  
% 3.65/0.98  fof(f42,plain,(
% 3.65/0.98    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.65/0.98    inference(ennf_transformation,[],[f20])).
% 3.65/0.98  
% 3.65/0.98  fof(f43,plain,(
% 3.65/0.98    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.65/0.98    inference(flattening,[],[f42])).
% 3.65/0.98  
% 3.65/0.98  fof(f52,plain,(
% 3.65/0.98    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_tdlat_3(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))))),
% 3.65/0.98    introduced(choice_axiom,[])).
% 3.65/0.98  
% 3.65/0.98  fof(f53,plain,(
% 3.65/0.98    ! [X0] : (! [X1] : ((u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_tdlat_3(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.65/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f52])).
% 3.65/0.98  
% 3.65/0.98  fof(f77,plain,(
% 3.65/0.98    ( ! [X0,X1] : (v1_tdlat_3(sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f53])).
% 3.65/0.98  
% 3.65/0.98  fof(f82,plain,(
% 3.65/0.98    v2_pre_topc(sK3)),
% 3.65/0.98    inference(cnf_transformation,[],[f58])).
% 3.65/0.98  
% 3.65/0.98  fof(f76,plain,(
% 3.65/0.98    ( ! [X0,X1] : (~v2_struct_0(sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f53])).
% 3.65/0.98  
% 3.65/0.98  fof(f78,plain,(
% 3.65/0.98    ( ! [X0,X1] : (m1_pre_topc(sK2(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f53])).
% 3.65/0.98  
% 3.65/0.98  fof(f79,plain,(
% 3.65/0.98    ( ! [X0,X1] : (u1_struct_0(sK2(X0,X1)) = X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f53])).
% 3.65/0.98  
% 3.65/0.98  fof(f1,axiom,(
% 3.65/0.98    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f59,plain,(
% 3.65/0.98    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 3.65/0.98    inference(cnf_transformation,[],[f1])).
% 3.65/0.98  
% 3.65/0.98  fof(f16,axiom,(
% 3.65/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f44,plain,(
% 3.65/0.98    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.65/0.98    inference(ennf_transformation,[],[f16])).
% 3.65/0.98  
% 3.65/0.98  fof(f45,plain,(
% 3.65/0.98    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.65/0.98    inference(flattening,[],[f44])).
% 3.65/0.98  
% 3.65/0.98  fof(f80,plain,(
% 3.65/0.98    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f45])).
% 3.65/0.98  
% 3.65/0.98  fof(f88,plain,(
% 3.65/0.98    ~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3)),
% 3.65/0.98    inference(cnf_transformation,[],[f58])).
% 3.65/0.98  
% 3.65/0.98  cnf(c_1,plain,
% 3.65/0.98      ( m1_subset_1(sK0(X0),X0) ),
% 3.65/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2278,plain,
% 3.65/0.98      ( m1_subset_1(sK0(X0),X0) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_24,negated_conjecture,
% 3.65/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.65/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2267,plain,
% 3.65/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_14,plain,
% 3.65/0.98      ( m1_pre_topc(sK1(X0,X1),X0)
% 3.65/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.65/0.98      | v2_struct_0(X0)
% 3.65/0.98      | ~ l1_pre_topc(X0)
% 3.65/0.98      | v1_xboole_0(X1) ),
% 3.65/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2271,plain,
% 3.65/0.98      ( m1_pre_topc(sK1(X0,X1),X0) = iProver_top
% 3.65/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.65/0.98      | v2_struct_0(X0) = iProver_top
% 3.65/0.98      | l1_pre_topc(X0) != iProver_top
% 3.65/0.98      | v1_xboole_0(X1) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3848,plain,
% 3.65/0.98      ( m1_pre_topc(sK1(sK3,sK4),sK3) = iProver_top
% 3.65/0.98      | v2_struct_0(sK3) = iProver_top
% 3.65/0.98      | l1_pre_topc(sK3) != iProver_top
% 3.65/0.98      | v1_xboole_0(sK4) = iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_2267,c_2271]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_29,negated_conjecture,
% 3.65/0.98      ( ~ v2_struct_0(sK3) ),
% 3.65/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_30,plain,
% 3.65/0.98      ( v2_struct_0(sK3) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_26,negated_conjecture,
% 3.65/0.98      ( l1_pre_topc(sK3) ),
% 3.65/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_33,plain,
% 3.65/0.98      ( l1_pre_topc(sK3) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_25,negated_conjecture,
% 3.65/0.98      ( ~ v1_xboole_0(sK4) ),
% 3.65/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_34,plain,
% 3.65/0.98      ( v1_xboole_0(sK4) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_35,plain,
% 3.65/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2511,plain,
% 3.65/0.98      ( m1_pre_topc(sK1(sK3,sK4),sK3)
% 3.65/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.65/0.98      | v2_struct_0(sK3)
% 3.65/0.98      | ~ l1_pre_topc(sK3)
% 3.65/0.98      | v1_xboole_0(sK4) ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_14]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2512,plain,
% 3.65/0.98      ( m1_pre_topc(sK1(sK3,sK4),sK3) = iProver_top
% 3.65/0.98      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.65/0.98      | v2_struct_0(sK3) = iProver_top
% 3.65/0.98      | l1_pre_topc(sK3) != iProver_top
% 3.65/0.98      | v1_xboole_0(sK4) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_2511]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_4221,plain,
% 3.65/0.98      ( m1_pre_topc(sK1(sK3,sK4),sK3) = iProver_top ),
% 3.65/0.98      inference(global_propositional_subsumption,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_3848,c_30,c_33,c_34,c_35,c_2512]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_13,plain,
% 3.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.98      | v2_struct_0(X1)
% 3.65/0.98      | ~ l1_pre_topc(X1)
% 3.65/0.98      | v1_xboole_0(X0)
% 3.65/0.98      | u1_struct_0(sK1(X1,X0)) = X0 ),
% 3.65/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2272,plain,
% 3.65/0.98      ( u1_struct_0(sK1(X0,X1)) = X1
% 3.65/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.65/0.98      | v2_struct_0(X0) = iProver_top
% 3.65/0.98      | l1_pre_topc(X0) != iProver_top
% 3.65/0.98      | v1_xboole_0(X1) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3307,plain,
% 3.65/0.98      ( u1_struct_0(sK1(sK3,sK4)) = sK4
% 3.65/0.98      | v2_struct_0(sK3) = iProver_top
% 3.65/0.98      | l1_pre_topc(sK3) != iProver_top
% 3.65/0.98      | v1_xboole_0(sK4) = iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_2267,c_2272]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2506,plain,
% 3.65/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.65/0.98      | v2_struct_0(sK3)
% 3.65/0.98      | ~ l1_pre_topc(sK3)
% 3.65/0.98      | v1_xboole_0(sK4)
% 3.65/0.98      | u1_struct_0(sK1(sK3,sK4)) = sK4 ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3610,plain,
% 3.65/0.98      ( u1_struct_0(sK1(sK3,sK4)) = sK4 ),
% 3.65/0.98      inference(global_propositional_subsumption,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_3307,c_29,c_26,c_25,c_24,c_2506]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_7,plain,
% 3.65/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.65/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.65/0.98      | m1_subset_1(X2,u1_struct_0(X1))
% 3.65/0.98      | v2_struct_0(X1)
% 3.65/0.98      | v2_struct_0(X0)
% 3.65/0.98      | ~ l1_pre_topc(X1) ),
% 3.65/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2275,plain,
% 3.65/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 3.65/0.98      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.65/0.98      | m1_subset_1(X2,u1_struct_0(X1)) = iProver_top
% 3.65/0.98      | v2_struct_0(X0) = iProver_top
% 3.65/0.98      | v2_struct_0(X1) = iProver_top
% 3.65/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3988,plain,
% 3.65/0.98      ( m1_pre_topc(sK1(sK3,sK4),X0) != iProver_top
% 3.65/0.98      | m1_subset_1(X1,u1_struct_0(X0)) = iProver_top
% 3.65/0.98      | m1_subset_1(X1,sK4) != iProver_top
% 3.65/0.98      | v2_struct_0(X0) = iProver_top
% 3.65/0.98      | v2_struct_0(sK1(sK3,sK4)) = iProver_top
% 3.65/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_3610,c_2275]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_15,plain,
% 3.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.98      | v2_struct_0(X1)
% 3.65/0.98      | ~ v2_struct_0(sK1(X1,X0))
% 3.65/0.98      | ~ l1_pre_topc(X1)
% 3.65/0.98      | v1_xboole_0(X0) ),
% 3.65/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3011,plain,
% 3.65/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.65/0.98      | ~ v2_struct_0(sK1(sK3,sK4))
% 3.65/0.98      | v2_struct_0(sK3)
% 3.65/0.98      | ~ l1_pre_topc(sK3)
% 3.65/0.98      | v1_xboole_0(sK4) ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_15]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3012,plain,
% 3.65/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.65/0.98      | v2_struct_0(sK1(sK3,sK4)) != iProver_top
% 3.65/0.98      | v2_struct_0(sK3) = iProver_top
% 3.65/0.98      | l1_pre_topc(sK3) != iProver_top
% 3.65/0.98      | v1_xboole_0(sK4) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_3011]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_4626,plain,
% 3.65/0.98      ( v2_struct_0(X0) = iProver_top
% 3.65/0.98      | m1_subset_1(X1,sK4) != iProver_top
% 3.65/0.98      | m1_subset_1(X1,u1_struct_0(X0)) = iProver_top
% 3.65/0.98      | m1_pre_topc(sK1(sK3,sK4),X0) != iProver_top
% 3.65/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.65/0.98      inference(global_propositional_subsumption,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_3988,c_30,c_33,c_34,c_35,c_3012]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_4627,plain,
% 3.65/0.98      ( m1_pre_topc(sK1(sK3,sK4),X0) != iProver_top
% 3.65/0.98      | m1_subset_1(X1,u1_struct_0(X0)) = iProver_top
% 3.65/0.98      | m1_subset_1(X1,sK4) != iProver_top
% 3.65/0.98      | v2_struct_0(X0) = iProver_top
% 3.65/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.65/0.98      inference(renaming,[status(thm)],[c_4626]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_4637,plain,
% 3.65/0.98      ( m1_subset_1(X0,u1_struct_0(sK3)) = iProver_top
% 3.65/0.98      | m1_subset_1(X0,sK4) != iProver_top
% 3.65/0.98      | v2_struct_0(sK3) = iProver_top
% 3.65/0.98      | l1_pre_topc(sK3) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_4221,c_4627]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_4642,plain,
% 3.65/0.98      ( m1_subset_1(X0,u1_struct_0(sK3)) = iProver_top
% 3.65/0.98      | m1_subset_1(X0,sK4) != iProver_top ),
% 3.65/0.98      inference(global_propositional_subsumption,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_4637,c_30,c_33]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_9,plain,
% 3.65/0.98      ( ~ m1_subset_1(X0,X1)
% 3.65/0.98      | v1_xboole_0(X1)
% 3.65/0.98      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 3.65/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2273,plain,
% 3.65/0.98      ( k6_domain_1(X0,X1) = k1_tarski(X1)
% 3.65/0.98      | m1_subset_1(X1,X0) != iProver_top
% 3.65/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_4651,plain,
% 3.65/0.98      ( k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0)
% 3.65/0.98      | m1_subset_1(X0,sK4) != iProver_top
% 3.65/0.98      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_4642,c_2273]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2,plain,
% 3.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.65/0.98      | ~ v1_xboole_0(X1)
% 3.65/0.98      | v1_xboole_0(X0) ),
% 3.65/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2631,plain,
% 3.65/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
% 3.65/0.98      | ~ v1_xboole_0(X0)
% 3.65/0.98      | v1_xboole_0(sK4) ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2686,plain,
% 3.65/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.65/0.98      | ~ v1_xboole_0(u1_struct_0(sK3))
% 3.65/0.98      | v1_xboole_0(sK4) ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_2631]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2687,plain,
% 3.65/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.65/0.98      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top
% 3.65/0.98      | v1_xboole_0(sK4) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_2686]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_5058,plain,
% 3.65/0.98      ( m1_subset_1(X0,sK4) != iProver_top
% 3.65/0.98      | k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0) ),
% 3.65/0.98      inference(global_propositional_subsumption,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_4651,c_34,c_35,c_2687]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_5059,plain,
% 3.65/0.98      ( k6_domain_1(u1_struct_0(sK3),X0) = k1_tarski(X0)
% 3.65/0.98      | m1_subset_1(X0,sK4) != iProver_top ),
% 3.65/0.98      inference(renaming,[status(thm)],[c_5058]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_5066,plain,
% 3.65/0.98      ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k1_tarski(sK0(sK4)) ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_2278,c_5059]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2731,plain,
% 3.65/0.98      ( k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0))
% 3.65/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_2278,c_2273]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2266,plain,
% 3.65/0.98      ( v1_xboole_0(sK4) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_4061,plain,
% 3.65/0.98      ( k6_domain_1(sK4,sK0(sK4)) = k1_tarski(sK0(sK4)) ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_2731,c_2266]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_8,plain,
% 3.65/0.98      ( ~ m1_subset_1(X0,X1)
% 3.65/0.98      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 3.65/0.98      | v1_xboole_0(X1) ),
% 3.65/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2274,plain,
% 3.65/0.98      ( m1_subset_1(X0,X1) != iProver_top
% 3.65/0.98      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
% 3.65/0.98      | v1_xboole_0(X1) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_4071,plain,
% 3.65/0.98      ( m1_subset_1(sK0(sK4),sK4) != iProver_top
% 3.65/0.98      | m1_subset_1(k1_tarski(sK0(sK4)),k1_zfmisc_1(sK4)) = iProver_top
% 3.65/0.98      | v1_xboole_0(sK4) = iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_4061,c_2274]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2676,plain,
% 3.65/0.98      ( m1_subset_1(sK0(sK4),sK4) ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2677,plain,
% 3.65/0.98      ( m1_subset_1(sK0(sK4),sK4) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_2676]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_4333,plain,
% 3.65/0.98      ( m1_subset_1(k1_tarski(sK0(sK4)),k1_zfmisc_1(sK4)) = iProver_top ),
% 3.65/0.98      inference(global_propositional_subsumption,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_4071,c_34,c_2677]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3,plain,
% 3.65/0.98      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.65/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_16,plain,
% 3.65/0.98      ( ~ r1_tarski(X0,X1)
% 3.65/0.98      | ~ v1_zfmisc_1(X1)
% 3.65/0.98      | v1_xboole_0(X0)
% 3.65/0.98      | v1_xboole_0(X1)
% 3.65/0.98      | X1 = X0 ),
% 3.65/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_397,plain,
% 3.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.65/0.98      | ~ v1_zfmisc_1(X1)
% 3.65/0.98      | v1_xboole_0(X0)
% 3.65/0.98      | v1_xboole_0(X1)
% 3.65/0.98      | X1 = X0 ),
% 3.65/0.98      inference(resolution,[status(thm)],[c_3,c_16]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_401,plain,
% 3.65/0.98      ( v1_xboole_0(X0)
% 3.65/0.98      | ~ v1_zfmisc_1(X1)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.65/0.98      | X1 = X0 ),
% 3.65/0.98      inference(global_propositional_subsumption,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_397,c_2]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_402,plain,
% 3.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.65/0.98      | ~ v1_zfmisc_1(X1)
% 3.65/0.98      | v1_xboole_0(X0)
% 3.65/0.98      | X1 = X0 ),
% 3.65/0.98      inference(renaming,[status(thm)],[c_401]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2263,plain,
% 3.65/0.98      ( X0 = X1
% 3.65/0.98      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 3.65/0.98      | v1_zfmisc_1(X0) != iProver_top
% 3.65/0.98      | v1_xboole_0(X1) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_402]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_4338,plain,
% 3.65/0.98      ( k1_tarski(sK0(sK4)) = sK4
% 3.65/0.98      | v1_zfmisc_1(sK4) != iProver_top
% 3.65/0.98      | v1_xboole_0(k1_tarski(sK0(sK4))) = iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_4333,c_2263]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_23,negated_conjecture,
% 3.65/0.98      ( v2_tex_2(sK4,sK3) | v1_zfmisc_1(sK4) ),
% 3.65/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_218,plain,
% 3.65/0.98      ( v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3) ),
% 3.65/0.98      inference(prop_impl,[status(thm)],[c_23]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_219,plain,
% 3.65/0.98      ( v2_tex_2(sK4,sK3) | v1_zfmisc_1(sK4) ),
% 3.65/0.98      inference(renaming,[status(thm)],[c_218]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_11,plain,
% 3.65/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.65/0.98      | ~ v1_tdlat_3(X0)
% 3.65/0.98      | ~ v2_tdlat_3(X1)
% 3.65/0.98      | ~ v2_pre_topc(X1)
% 3.65/0.98      | v2_struct_0(X1)
% 3.65/0.98      | v2_struct_0(X0)
% 3.65/0.98      | v7_struct_0(X0)
% 3.65/0.98      | ~ l1_pre_topc(X1) ),
% 3.65/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_4,plain,
% 3.65/0.98      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.65/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_6,plain,
% 3.65/0.98      ( ~ v7_struct_0(X0)
% 3.65/0.98      | v1_zfmisc_1(u1_struct_0(X0))
% 3.65/0.98      | ~ l1_struct_0(X0) ),
% 3.65/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_379,plain,
% 3.65/0.98      ( ~ v7_struct_0(X0)
% 3.65/0.98      | v1_zfmisc_1(u1_struct_0(X0))
% 3.65/0.98      | ~ l1_pre_topc(X0) ),
% 3.65/0.98      inference(resolution,[status(thm)],[c_4,c_6]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_423,plain,
% 3.65/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.65/0.98      | ~ v1_tdlat_3(X0)
% 3.65/0.98      | ~ v2_tdlat_3(X1)
% 3.65/0.98      | ~ v2_pre_topc(X1)
% 3.65/0.98      | v2_struct_0(X0)
% 3.65/0.98      | v2_struct_0(X1)
% 3.65/0.98      | v1_zfmisc_1(u1_struct_0(X0))
% 3.65/0.98      | ~ l1_pre_topc(X0)
% 3.65/0.98      | ~ l1_pre_topc(X1) ),
% 3.65/0.98      inference(resolution,[status(thm)],[c_11,c_379]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_5,plain,
% 3.65/0.98      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.65/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_427,plain,
% 3.65/0.98      ( v1_zfmisc_1(u1_struct_0(X0))
% 3.65/0.98      | v2_struct_0(X1)
% 3.65/0.98      | v2_struct_0(X0)
% 3.65/0.98      | ~ v2_pre_topc(X1)
% 3.65/0.98      | ~ v2_tdlat_3(X1)
% 3.65/0.98      | ~ v1_tdlat_3(X0)
% 3.65/0.98      | ~ m1_pre_topc(X0,X1)
% 3.65/0.98      | ~ l1_pre_topc(X1) ),
% 3.65/0.98      inference(global_propositional_subsumption,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_423,c_5]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_428,plain,
% 3.65/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.65/0.98      | ~ v1_tdlat_3(X0)
% 3.65/0.98      | ~ v2_tdlat_3(X1)
% 3.65/0.98      | ~ v2_pre_topc(X1)
% 3.65/0.98      | v2_struct_0(X0)
% 3.65/0.98      | v2_struct_0(X1)
% 3.65/0.98      | v1_zfmisc_1(u1_struct_0(X0))
% 3.65/0.98      | ~ l1_pre_topc(X1) ),
% 3.65/0.98      inference(renaming,[status(thm)],[c_427]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_10,plain,
% 3.65/0.98      ( ~ v2_tdlat_3(X0) | v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 3.65/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_447,plain,
% 3.65/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.65/0.98      | ~ v1_tdlat_3(X0)
% 3.65/0.98      | ~ v2_tdlat_3(X1)
% 3.65/0.98      | v2_struct_0(X0)
% 3.65/0.98      | v2_struct_0(X1)
% 3.65/0.98      | v1_zfmisc_1(u1_struct_0(X0))
% 3.65/0.98      | ~ l1_pre_topc(X1) ),
% 3.65/0.98      inference(forward_subsumption_resolution,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_428,c_10]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_27,negated_conjecture,
% 3.65/0.98      ( v2_tdlat_3(sK3) ),
% 3.65/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_468,plain,
% 3.65/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.65/0.98      | ~ v1_tdlat_3(X0)
% 3.65/0.98      | v2_struct_0(X0)
% 3.65/0.98      | v2_struct_0(X1)
% 3.65/0.98      | v1_zfmisc_1(u1_struct_0(X0))
% 3.65/0.98      | ~ l1_pre_topc(X1)
% 3.65/0.98      | sK3 != X1 ),
% 3.65/0.98      inference(resolution_lifted,[status(thm)],[c_447,c_27]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_469,plain,
% 3.65/0.98      ( ~ m1_pre_topc(X0,sK3)
% 3.65/0.98      | ~ v1_tdlat_3(X0)
% 3.65/0.98      | v2_struct_0(X0)
% 3.65/0.98      | v2_struct_0(sK3)
% 3.65/0.98      | v1_zfmisc_1(u1_struct_0(X0))
% 3.65/0.98      | ~ l1_pre_topc(sK3) ),
% 3.65/0.98      inference(unflattening,[status(thm)],[c_468]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_473,plain,
% 3.65/0.98      ( v1_zfmisc_1(u1_struct_0(X0))
% 3.65/0.98      | ~ m1_pre_topc(X0,sK3)
% 3.65/0.98      | ~ v1_tdlat_3(X0)
% 3.65/0.98      | v2_struct_0(X0) ),
% 3.65/0.98      inference(global_propositional_subsumption,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_469,c_29,c_26]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_474,plain,
% 3.65/0.98      ( ~ m1_pre_topc(X0,sK3)
% 3.65/0.98      | ~ v1_tdlat_3(X0)
% 3.65/0.98      | v2_struct_0(X0)
% 3.65/0.98      | v1_zfmisc_1(u1_struct_0(X0)) ),
% 3.65/0.98      inference(renaming,[status(thm)],[c_473]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_19,plain,
% 3.65/0.98      ( ~ v2_tex_2(X0,X1)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.98      | v1_tdlat_3(sK2(X1,X0))
% 3.65/0.98      | ~ v2_pre_topc(X1)
% 3.65/0.98      | v2_struct_0(X1)
% 3.65/0.98      | ~ l1_pre_topc(X1)
% 3.65/0.98      | v1_xboole_0(X0) ),
% 3.65/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_28,negated_conjecture,
% 3.65/0.98      ( v2_pre_topc(sK3) ),
% 3.65/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_661,plain,
% 3.65/0.98      ( ~ v2_tex_2(X0,X1)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.98      | v1_tdlat_3(sK2(X1,X0))
% 3.65/0.98      | v2_struct_0(X1)
% 3.65/0.98      | ~ l1_pre_topc(X1)
% 3.65/0.98      | v1_xboole_0(X0)
% 3.65/0.98      | sK3 != X1 ),
% 3.65/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_662,plain,
% 3.65/0.98      ( ~ v2_tex_2(X0,sK3)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.65/0.98      | v1_tdlat_3(sK2(sK3,X0))
% 3.65/0.98      | v2_struct_0(sK3)
% 3.65/0.98      | ~ l1_pre_topc(sK3)
% 3.65/0.98      | v1_xboole_0(X0) ),
% 3.65/0.98      inference(unflattening,[status(thm)],[c_661]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_666,plain,
% 3.65/0.98      ( ~ v2_tex_2(X0,sK3)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.65/0.98      | v1_tdlat_3(sK2(sK3,X0))
% 3.65/0.98      | v1_xboole_0(X0) ),
% 3.65/0.98      inference(global_propositional_subsumption,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_662,c_29,c_26]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_756,plain,
% 3.65/0.98      ( ~ v2_tex_2(X0,sK3)
% 3.65/0.98      | ~ m1_pre_topc(X1,sK3)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.65/0.98      | v2_struct_0(X1)
% 3.65/0.98      | v1_zfmisc_1(u1_struct_0(X1))
% 3.65/0.98      | v1_xboole_0(X0)
% 3.65/0.98      | sK2(sK3,X0) != X1 ),
% 3.65/0.98      inference(resolution_lifted,[status(thm)],[c_474,c_666]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_757,plain,
% 3.65/0.98      ( ~ v2_tex_2(X0,sK3)
% 3.65/0.98      | ~ m1_pre_topc(sK2(sK3,X0),sK3)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.65/0.98      | v2_struct_0(sK2(sK3,X0))
% 3.65/0.98      | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
% 3.65/0.98      | v1_xboole_0(X0) ),
% 3.65/0.98      inference(unflattening,[status(thm)],[c_756]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_20,plain,
% 3.65/0.98      ( ~ v2_tex_2(X0,X1)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.98      | ~ v2_pre_topc(X1)
% 3.65/0.98      | v2_struct_0(X1)
% 3.65/0.98      | ~ v2_struct_0(sK2(X1,X0))
% 3.65/0.98      | ~ l1_pre_topc(X1)
% 3.65/0.98      | v1_xboole_0(X0) ),
% 3.65/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_637,plain,
% 3.65/0.98      ( ~ v2_tex_2(X0,X1)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.98      | v2_struct_0(X1)
% 3.65/0.98      | ~ v2_struct_0(sK2(X1,X0))
% 3.65/0.98      | ~ l1_pre_topc(X1)
% 3.65/0.98      | v1_xboole_0(X0)
% 3.65/0.98      | sK3 != X1 ),
% 3.65/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_28]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_638,plain,
% 3.65/0.98      ( ~ v2_tex_2(X0,sK3)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.65/0.98      | ~ v2_struct_0(sK2(sK3,X0))
% 3.65/0.98      | v2_struct_0(sK3)
% 3.65/0.98      | ~ l1_pre_topc(sK3)
% 3.65/0.98      | v1_xboole_0(X0) ),
% 3.65/0.98      inference(unflattening,[status(thm)],[c_637]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_642,plain,
% 3.65/0.98      ( ~ v2_tex_2(X0,sK3)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.65/0.98      | ~ v2_struct_0(sK2(sK3,X0))
% 3.65/0.98      | v1_xboole_0(X0) ),
% 3.65/0.98      inference(global_propositional_subsumption,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_638,c_29,c_26]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_18,plain,
% 3.65/0.98      ( ~ v2_tex_2(X0,X1)
% 3.65/0.98      | m1_pre_topc(sK2(X1,X0),X1)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.98      | ~ v2_pre_topc(X1)
% 3.65/0.98      | v2_struct_0(X1)
% 3.65/0.98      | ~ l1_pre_topc(X1)
% 3.65/0.98      | v1_xboole_0(X0) ),
% 3.65/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_685,plain,
% 3.65/0.98      ( ~ v2_tex_2(X0,X1)
% 3.65/0.98      | m1_pre_topc(sK2(X1,X0),X1)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.98      | v2_struct_0(X1)
% 3.65/0.98      | ~ l1_pre_topc(X1)
% 3.65/0.98      | v1_xboole_0(X0)
% 3.65/0.98      | sK3 != X1 ),
% 3.65/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_28]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_686,plain,
% 3.65/0.98      ( ~ v2_tex_2(X0,sK3)
% 3.65/0.98      | m1_pre_topc(sK2(sK3,X0),sK3)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.65/0.98      | v2_struct_0(sK3)
% 3.65/0.98      | ~ l1_pre_topc(sK3)
% 3.65/0.98      | v1_xboole_0(X0) ),
% 3.65/0.98      inference(unflattening,[status(thm)],[c_685]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_690,plain,
% 3.65/0.98      ( ~ v2_tex_2(X0,sK3)
% 3.65/0.98      | m1_pre_topc(sK2(sK3,X0),sK3)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.65/0.98      | v1_xboole_0(X0) ),
% 3.65/0.98      inference(global_propositional_subsumption,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_686,c_29,c_26]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_761,plain,
% 3.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.65/0.98      | ~ v2_tex_2(X0,sK3)
% 3.65/0.98      | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
% 3.65/0.98      | v1_xboole_0(X0) ),
% 3.65/0.98      inference(global_propositional_subsumption,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_757,c_642,c_690]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_762,plain,
% 3.65/0.98      ( ~ v2_tex_2(X0,sK3)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.65/0.98      | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
% 3.65/0.98      | v1_xboole_0(X0) ),
% 3.65/0.98      inference(renaming,[status(thm)],[c_761]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_998,plain,
% 3.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.65/0.98      | v1_zfmisc_1(u1_struct_0(sK2(sK3,X0)))
% 3.65/0.98      | v1_zfmisc_1(sK4)
% 3.65/0.98      | v1_xboole_0(X0)
% 3.65/0.98      | sK3 != sK3
% 3.65/0.98      | sK4 != X0 ),
% 3.65/0.98      inference(resolution_lifted,[status(thm)],[c_219,c_762]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_999,plain,
% 3.65/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.65/0.98      | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
% 3.65/0.98      | v1_zfmisc_1(sK4)
% 3.65/0.98      | v1_xboole_0(sK4) ),
% 3.65/0.98      inference(unflattening,[status(thm)],[c_998]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_1001,plain,
% 3.65/0.98      ( v1_zfmisc_1(sK4) | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) ),
% 3.65/0.98      inference(global_propositional_subsumption,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_999,c_25,c_24]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_1002,plain,
% 3.65/0.98      ( v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) | v1_zfmisc_1(sK4) ),
% 3.65/0.98      inference(renaming,[status(thm)],[c_1001]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_1003,plain,
% 3.65/0.98      ( v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) = iProver_top
% 3.65/0.98      | v1_zfmisc_1(sK4) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_1002]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_17,plain,
% 3.65/0.98      ( ~ v2_tex_2(X0,X1)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.98      | ~ v2_pre_topc(X1)
% 3.65/0.98      | v2_struct_0(X1)
% 3.65/0.98      | ~ l1_pre_topc(X1)
% 3.65/0.98      | v1_xboole_0(X0)
% 3.65/0.98      | u1_struct_0(sK2(X1,X0)) = X0 ),
% 3.65/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_709,plain,
% 3.65/0.98      ( ~ v2_tex_2(X0,X1)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.98      | v2_struct_0(X1)
% 3.65/0.98      | ~ l1_pre_topc(X1)
% 3.65/0.98      | v1_xboole_0(X0)
% 3.65/0.98      | u1_struct_0(sK2(X1,X0)) = X0
% 3.65/0.98      | sK3 != X1 ),
% 3.65/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_28]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_710,plain,
% 3.65/0.98      ( ~ v2_tex_2(X0,sK3)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.65/0.98      | v2_struct_0(sK3)
% 3.65/0.98      | ~ l1_pre_topc(sK3)
% 3.65/0.98      | v1_xboole_0(X0)
% 3.65/0.98      | u1_struct_0(sK2(sK3,X0)) = X0 ),
% 3.65/0.98      inference(unflattening,[status(thm)],[c_709]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_714,plain,
% 3.65/0.98      ( ~ v2_tex_2(X0,sK3)
% 3.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.65/0.98      | v1_xboole_0(X0)
% 3.65/0.98      | u1_struct_0(sK2(sK3,X0)) = X0 ),
% 3.65/0.98      inference(global_propositional_subsumption,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_710,c_29,c_26]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_1012,plain,
% 3.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.65/0.98      | v1_zfmisc_1(sK4)
% 3.65/0.98      | v1_xboole_0(X0)
% 3.65/0.98      | u1_struct_0(sK2(sK3,X0)) = X0
% 3.65/0.98      | sK3 != sK3
% 3.65/0.98      | sK4 != X0 ),
% 3.65/0.98      inference(resolution_lifted,[status(thm)],[c_219,c_714]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_1013,plain,
% 3.65/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.65/0.98      | v1_zfmisc_1(sK4)
% 3.65/0.98      | v1_xboole_0(sK4)
% 3.65/0.98      | u1_struct_0(sK2(sK3,sK4)) = sK4 ),
% 3.65/0.98      inference(unflattening,[status(thm)],[c_1012]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_1015,plain,
% 3.65/0.98      ( v1_zfmisc_1(sK4) | u1_struct_0(sK2(sK3,sK4)) = sK4 ),
% 3.65/0.98      inference(global_propositional_subsumption,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_1013,c_25,c_24]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_1017,plain,
% 3.65/0.98      ( u1_struct_0(sK2(sK3,sK4)) = sK4
% 3.65/0.98      | v1_zfmisc_1(sK4) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_1015]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_1694,plain,( X0 = X0 ),theory(equality) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2577,plain,
% 3.65/0.98      ( sK4 = sK4 ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_1694]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_1695,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2695,plain,
% 3.65/0.98      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_1695]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3004,plain,
% 3.65/0.98      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_2695]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3488,plain,
% 3.65/0.98      ( u1_struct_0(sK2(sK3,sK4)) != sK4
% 3.65/0.98      | sK4 = u1_struct_0(sK2(sK3,sK4))
% 3.65/0.98      | sK4 != sK4 ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_3004]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_1702,plain,
% 3.65/0.98      ( ~ v1_zfmisc_1(X0) | v1_zfmisc_1(X1) | X1 != X0 ),
% 3.65/0.98      theory(equality) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2892,plain,
% 3.65/0.98      ( v1_zfmisc_1(X0)
% 3.65/0.98      | ~ v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
% 3.65/0.98      | X0 != u1_struct_0(sK2(sK3,sK4)) ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_1702]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3919,plain,
% 3.65/0.98      ( ~ v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
% 3.65/0.98      | v1_zfmisc_1(sK4)
% 3.65/0.98      | sK4 != u1_struct_0(sK2(sK3,sK4)) ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_2892]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3920,plain,
% 3.65/0.98      ( sK4 != u1_struct_0(sK2(sK3,sK4))
% 3.65/0.98      | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) != iProver_top
% 3.65/0.98      | v1_zfmisc_1(sK4) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_3919]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_4952,plain,
% 3.65/0.98      ( k1_tarski(sK0(sK4)) = sK4
% 3.65/0.98      | v1_xboole_0(k1_tarski(sK0(sK4))) = iProver_top ),
% 3.65/0.98      inference(global_propositional_subsumption,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_4338,c_1003,c_1017,c_2577,c_3488,c_3920]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_0,plain,
% 3.65/0.98      ( ~ v1_xboole_0(k1_tarski(X0)) ),
% 3.65/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2279,plain,
% 3.65/0.98      ( v1_xboole_0(k1_tarski(X0)) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_4958,plain,
% 3.65/0.98      ( k1_tarski(sK0(sK4)) = sK4 ),
% 3.65/0.98      inference(forward_subsumption_resolution,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_4952,c_2279]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_5067,plain,
% 3.65/0.98      ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = sK4 ),
% 3.65/0.98      inference(light_normalisation,[status(thm)],[c_5066,c_4958]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_21,plain,
% 3.65/0.98      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 3.65/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.65/0.98      | ~ v2_pre_topc(X0)
% 3.65/0.98      | v2_struct_0(X0)
% 3.65/0.98      | ~ l1_pre_topc(X0) ),
% 3.65/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_619,plain,
% 3.65/0.98      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 3.65/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.65/0.98      | v2_struct_0(X0)
% 3.65/0.98      | ~ l1_pre_topc(X0)
% 3.65/0.98      | sK3 != X0 ),
% 3.65/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_28]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_620,plain,
% 3.65/0.98      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
% 3.65/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.65/0.98      | v2_struct_0(sK3)
% 3.65/0.98      | ~ l1_pre_topc(sK3) ),
% 3.65/0.98      inference(unflattening,[status(thm)],[c_619]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_624,plain,
% 3.65/0.98      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
% 3.65/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 3.65/0.98      inference(global_propositional_subsumption,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_620,c_29,c_26]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2262,plain,
% 3.65/0.98      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) = iProver_top
% 3.65/0.98      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_624]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_12752,plain,
% 3.65/0.98      ( v2_tex_2(sK4,sK3) = iProver_top
% 3.65/0.98      | m1_subset_1(sK0(sK4),u1_struct_0(sK3)) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_5067,c_2262]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2260,plain,
% 3.65/0.98      ( v2_tex_2(X0,sK3) != iProver_top
% 3.65/0.98      | m1_pre_topc(sK2(sK3,X0),sK3) = iProver_top
% 3.65/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.65/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_690]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3054,plain,
% 3.65/0.98      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.65/0.98      | m1_pre_topc(sK2(sK3,sK4),sK3) = iProver_top
% 3.65/0.98      | v1_xboole_0(sK4) = iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_2267,c_2260]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3573,plain,
% 3.65/0.98      ( m1_pre_topc(sK2(sK3,sK4),sK3) = iProver_top
% 3.65/0.98      | v2_tex_2(sK4,sK3) != iProver_top ),
% 3.65/0.98      inference(global_propositional_subsumption,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_3054,c_34]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3574,plain,
% 3.65/0.98      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.65/0.98      | m1_pre_topc(sK2(sK3,sK4),sK3) = iProver_top ),
% 3.65/0.98      inference(renaming,[status(thm)],[c_3573]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3987,plain,
% 3.65/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 3.65/0.98      | m1_subset_1(sK0(u1_struct_0(X0)),u1_struct_0(X1)) = iProver_top
% 3.65/0.98      | v2_struct_0(X0) = iProver_top
% 3.65/0.98      | v2_struct_0(X1) = iProver_top
% 3.65/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_2278,c_2275]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_7322,plain,
% 3.65/0.98      ( k6_domain_1(u1_struct_0(X0),sK0(u1_struct_0(X1))) = k1_tarski(sK0(u1_struct_0(X1)))
% 3.65/0.98      | m1_pre_topc(X1,X0) != iProver_top
% 3.65/0.98      | v2_struct_0(X1) = iProver_top
% 3.65/0.98      | v2_struct_0(X0) = iProver_top
% 3.65/0.98      | l1_pre_topc(X0) != iProver_top
% 3.65/0.98      | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_3987,c_2273]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_8281,plain,
% 3.65/0.98      ( k6_domain_1(u1_struct_0(sK3),sK0(u1_struct_0(sK2(sK3,sK4)))) = k1_tarski(sK0(u1_struct_0(sK2(sK3,sK4))))
% 3.65/0.98      | v2_tex_2(sK4,sK3) != iProver_top
% 3.65/0.98      | v2_struct_0(sK2(sK3,sK4)) = iProver_top
% 3.65/0.98      | v2_struct_0(sK3) = iProver_top
% 3.65/0.98      | l1_pre_topc(sK3) != iProver_top
% 3.65/0.98      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_3574,c_7322]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_22,negated_conjecture,
% 3.65/0.98      ( ~ v2_tex_2(sK4,sK3) | ~ v1_zfmisc_1(sK4) ),
% 3.65/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_37,plain,
% 3.65/0.98      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.65/0.98      | v1_zfmisc_1(sK4) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_8513,plain,
% 3.65/0.98      ( v2_tex_2(sK4,sK3) != iProver_top ),
% 3.65/0.98      inference(global_propositional_subsumption,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_8281,c_37,c_1003,c_1017,c_2577,c_3488,c_3920]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3080,plain,
% 3.65/0.98      ( ~ m1_pre_topc(sK1(sK3,sK4),X0)
% 3.65/0.98      | m1_subset_1(X1,u1_struct_0(X0))
% 3.65/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1(sK3,sK4)))
% 3.65/0.98      | v2_struct_0(X0)
% 3.65/0.98      | v2_struct_0(sK1(sK3,sK4))
% 3.65/0.98      | ~ l1_pre_topc(X0) ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_7199,plain,
% 3.65/0.98      ( ~ m1_pre_topc(sK1(sK3,sK4),X0)
% 3.65/0.98      | m1_subset_1(sK0(sK4),u1_struct_0(X0))
% 3.65/0.98      | ~ m1_subset_1(sK0(sK4),u1_struct_0(sK1(sK3,sK4)))
% 3.65/0.98      | v2_struct_0(X0)
% 3.65/0.98      | v2_struct_0(sK1(sK3,sK4))
% 3.65/0.98      | ~ l1_pre_topc(X0) ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_3080]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_7200,plain,
% 3.65/0.98      ( m1_pre_topc(sK1(sK3,sK4),X0) != iProver_top
% 3.65/0.98      | m1_subset_1(sK0(sK4),u1_struct_0(X0)) = iProver_top
% 3.65/0.98      | m1_subset_1(sK0(sK4),u1_struct_0(sK1(sK3,sK4))) != iProver_top
% 3.65/0.98      | v2_struct_0(X0) = iProver_top
% 3.65/0.98      | v2_struct_0(sK1(sK3,sK4)) = iProver_top
% 3.65/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_7199]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_7202,plain,
% 3.65/0.98      ( m1_pre_topc(sK1(sK3,sK4),sK3) != iProver_top
% 3.65/0.98      | m1_subset_1(sK0(sK4),u1_struct_0(sK1(sK3,sK4))) != iProver_top
% 3.65/0.98      | m1_subset_1(sK0(sK4),u1_struct_0(sK3)) = iProver_top
% 3.65/0.98      | v2_struct_0(sK1(sK3,sK4)) = iProver_top
% 3.65/0.98      | v2_struct_0(sK3) = iProver_top
% 3.65/0.98      | l1_pre_topc(sK3) != iProver_top ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_7200]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2863,plain,
% 3.65/0.98      ( sK0(X0) = sK0(X0) ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_1694]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_5760,plain,
% 3.65/0.98      ( sK0(sK4) = sK0(sK4) ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_2863]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_1697,plain,
% 3.65/0.98      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.65/0.98      theory(equality) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2514,plain,
% 3.65/0.98      ( m1_subset_1(X0,X1)
% 3.65/0.98      | ~ m1_subset_1(sK0(X2),X2)
% 3.65/0.98      | X1 != X2
% 3.65/0.98      | X0 != sK0(X2) ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_1697]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2862,plain,
% 3.65/0.98      ( ~ m1_subset_1(sK0(X0),X0)
% 3.65/0.98      | m1_subset_1(sK0(X0),X1)
% 3.65/0.98      | X1 != X0
% 3.65/0.98      | sK0(X0) != sK0(X0) ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_2514]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3521,plain,
% 3.65/0.98      ( ~ m1_subset_1(sK0(X0),X0)
% 3.65/0.98      | m1_subset_1(sK0(X0),u1_struct_0(sK1(sK3,sK4)))
% 3.65/0.98      | u1_struct_0(sK1(sK3,sK4)) != X0
% 3.65/0.98      | sK0(X0) != sK0(X0) ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_2862]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_4896,plain,
% 3.65/0.98      ( m1_subset_1(sK0(sK4),u1_struct_0(sK1(sK3,sK4)))
% 3.65/0.98      | ~ m1_subset_1(sK0(sK4),sK4)
% 3.65/0.98      | u1_struct_0(sK1(sK3,sK4)) != sK4
% 3.65/0.98      | sK0(sK4) != sK0(sK4) ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_3521]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_4897,plain,
% 3.65/0.98      ( u1_struct_0(sK1(sK3,sK4)) != sK4
% 3.65/0.98      | sK0(sK4) != sK0(sK4)
% 3.65/0.98      | m1_subset_1(sK0(sK4),u1_struct_0(sK1(sK3,sK4))) = iProver_top
% 3.65/0.98      | m1_subset_1(sK0(sK4),sK4) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_4896]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(contradiction,plain,
% 3.65/0.98      ( $false ),
% 3.65/0.98      inference(minisat,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_12752,c_8513,c_7202,c_5760,c_4897,c_3012,c_2677,
% 3.65/0.98                 c_2512,c_2506,c_35,c_24,c_34,c_25,c_33,c_26,c_30,c_29]) ).
% 3.65/0.98  
% 3.65/0.98  
% 3.65/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.65/0.98  
% 3.65/0.98  ------                               Statistics
% 3.65/0.98  
% 3.65/0.98  ------ General
% 3.65/0.98  
% 3.65/0.98  abstr_ref_over_cycles:                  0
% 3.65/0.98  abstr_ref_under_cycles:                 0
% 3.65/0.98  gc_basic_clause_elim:                   0
% 3.65/0.98  forced_gc_time:                         0
% 3.65/0.98  parsing_time:                           0.009
% 3.65/0.98  unif_index_cands_time:                  0.
% 3.65/0.98  unif_index_add_time:                    0.
% 3.65/0.98  orderings_time:                         0.
% 3.65/0.98  out_proof_time:                         0.019
% 3.65/0.98  total_time:                             0.357
% 3.65/0.98  num_of_symbols:                         53
% 3.65/0.98  num_of_terms:                           8620
% 3.65/0.98  
% 3.65/0.98  ------ Preprocessing
% 3.65/0.98  
% 3.65/0.98  num_of_splits:                          0
% 3.65/0.98  num_of_split_atoms:                     0
% 3.65/0.98  num_of_reused_defs:                     0
% 3.65/0.98  num_eq_ax_congr_red:                    24
% 3.65/0.98  num_of_sem_filtered_clauses:            1
% 3.65/0.98  num_of_subtypes:                        0
% 3.65/0.98  monotx_restored_types:                  0
% 3.65/0.98  sat_num_of_epr_types:                   0
% 3.65/0.98  sat_num_of_non_cyclic_types:            0
% 3.65/0.98  sat_guarded_non_collapsed_types:        0
% 3.65/0.98  num_pure_diseq_elim:                    0
% 3.65/0.98  simp_replaced_by:                       0
% 3.65/0.98  res_preprocessed:                       122
% 3.65/0.98  prep_upred:                             0
% 3.65/0.98  prep_unflattend:                        47
% 3.65/0.98  smt_new_axioms:                         0
% 3.65/0.98  pred_elim_cands:                        7
% 3.65/0.98  pred_elim:                              6
% 3.65/0.98  pred_elim_cl:                           7
% 3.65/0.98  pred_elim_cycles:                       14
% 3.65/0.98  merged_defs:                            8
% 3.65/0.98  merged_defs_ncl:                        0
% 3.65/0.98  bin_hyper_res:                          8
% 3.65/0.98  prep_cycles:                            4
% 3.65/0.98  pred_elim_time:                         0.023
% 3.65/0.98  splitting_time:                         0.
% 3.65/0.98  sem_filter_time:                        0.
% 3.65/0.98  monotx_time:                            0.001
% 3.65/0.98  subtype_inf_time:                       0.
% 3.65/0.98  
% 3.65/0.98  ------ Problem properties
% 3.65/0.98  
% 3.65/0.98  clauses:                                22
% 3.65/0.98  conjectures:                            6
% 3.65/0.98  epr:                                    6
% 3.65/0.98  horn:                                   11
% 3.65/0.98  ground:                                 6
% 3.65/0.98  unary:                                  6
% 3.65/0.98  binary:                                 3
% 3.65/0.98  lits:                                   65
% 3.65/0.98  lits_eq:                                4
% 3.65/0.98  fd_pure:                                0
% 3.65/0.98  fd_pseudo:                              0
% 3.65/0.98  fd_cond:                                0
% 3.65/0.98  fd_pseudo_cond:                         1
% 3.65/0.98  ac_symbols:                             0
% 3.65/0.98  
% 3.65/0.98  ------ Propositional Solver
% 3.65/0.98  
% 3.65/0.98  prop_solver_calls:                      31
% 3.65/0.98  prop_fast_solver_calls:                 1857
% 3.65/0.98  smt_solver_calls:                       0
% 3.65/0.98  smt_fast_solver_calls:                  0
% 3.65/0.98  prop_num_of_clauses:                    3966
% 3.65/0.98  prop_preprocess_simplified:             8870
% 3.65/0.98  prop_fo_subsumed:                       192
% 3.65/0.98  prop_solver_time:                       0.
% 3.65/0.98  smt_solver_time:                        0.
% 3.65/0.98  smt_fast_solver_time:                   0.
% 3.65/0.98  prop_fast_solver_time:                  0.
% 3.65/0.98  prop_unsat_core_time:                   0.
% 3.65/0.98  
% 3.65/0.98  ------ QBF
% 3.65/0.98  
% 3.65/0.98  qbf_q_res:                              0
% 3.65/0.98  qbf_num_tautologies:                    0
% 3.65/0.98  qbf_prep_cycles:                        0
% 3.65/0.98  
% 3.65/0.98  ------ BMC1
% 3.65/0.98  
% 3.65/0.98  bmc1_current_bound:                     -1
% 3.65/0.98  bmc1_last_solved_bound:                 -1
% 3.65/0.98  bmc1_unsat_core_size:                   -1
% 3.65/0.98  bmc1_unsat_core_parents_size:           -1
% 3.65/0.98  bmc1_merge_next_fun:                    0
% 3.65/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.65/0.98  
% 3.65/0.98  ------ Instantiation
% 3.65/0.98  
% 3.65/0.98  inst_num_of_clauses:                    1193
% 3.65/0.98  inst_num_in_passive:                    296
% 3.65/0.98  inst_num_in_active:                     708
% 3.65/0.98  inst_num_in_unprocessed:                189
% 3.65/0.98  inst_num_of_loops:                      790
% 3.65/0.98  inst_num_of_learning_restarts:          0
% 3.65/0.98  inst_num_moves_active_passive:          76
% 3.65/0.98  inst_lit_activity:                      0
% 3.65/0.98  inst_lit_activity_moves:                0
% 3.65/0.98  inst_num_tautologies:                   0
% 3.65/0.98  inst_num_prop_implied:                  0
% 3.65/0.98  inst_num_existing_simplified:           0
% 3.65/0.98  inst_num_eq_res_simplified:             0
% 3.65/0.98  inst_num_child_elim:                    0
% 3.65/0.98  inst_num_of_dismatching_blockings:      566
% 3.65/0.98  inst_num_of_non_proper_insts:           1528
% 3.65/0.98  inst_num_of_duplicates:                 0
% 3.65/0.98  inst_inst_num_from_inst_to_res:         0
% 3.65/0.98  inst_dismatching_checking_time:         0.
% 3.65/0.98  
% 3.65/0.98  ------ Resolution
% 3.65/0.98  
% 3.65/0.98  res_num_of_clauses:                     0
% 3.65/0.98  res_num_in_passive:                     0
% 3.65/0.98  res_num_in_active:                      0
% 3.65/0.98  res_num_of_loops:                       126
% 3.65/0.98  res_forward_subset_subsumed:            192
% 3.65/0.98  res_backward_subset_subsumed:           2
% 3.65/0.98  res_forward_subsumed:                   0
% 3.65/0.98  res_backward_subsumed:                  0
% 3.65/0.98  res_forward_subsumption_resolution:     2
% 3.65/0.98  res_backward_subsumption_resolution:    0
% 3.65/0.98  res_clause_to_clause_subsumption:       769
% 3.65/0.98  res_orphan_elimination:                 0
% 3.65/0.98  res_tautology_del:                      227
% 3.65/0.98  res_num_eq_res_simplified:              0
% 3.65/0.98  res_num_sel_changes:                    0
% 3.65/0.98  res_moves_from_active_to_pass:          0
% 3.65/0.98  
% 3.65/0.98  ------ Superposition
% 3.65/0.98  
% 3.65/0.98  sup_time_total:                         0.
% 3.65/0.98  sup_time_generating:                    0.
% 3.65/0.98  sup_time_sim_full:                      0.
% 3.65/0.98  sup_time_sim_immed:                     0.
% 3.65/0.98  
% 3.65/0.98  sup_num_of_clauses:                     266
% 3.65/0.98  sup_num_in_active:                      147
% 3.65/0.98  sup_num_in_passive:                     119
% 3.65/0.98  sup_num_of_loops:                       156
% 3.65/0.98  sup_fw_superposition:                   163
% 3.65/0.98  sup_bw_superposition:                   177
% 3.65/0.98  sup_immediate_simplified:               135
% 3.65/0.98  sup_given_eliminated:                   0
% 3.65/0.98  comparisons_done:                       0
% 3.65/0.98  comparisons_avoided:                    0
% 3.65/0.98  
% 3.65/0.98  ------ Simplifications
% 3.65/0.98  
% 3.65/0.98  
% 3.65/0.98  sim_fw_subset_subsumed:                 28
% 3.65/0.98  sim_bw_subset_subsumed:                 13
% 3.65/0.98  sim_fw_subsumed:                        21
% 3.65/0.98  sim_bw_subsumed:                        0
% 3.65/0.98  sim_fw_subsumption_res:                 12
% 3.65/0.98  sim_bw_subsumption_res:                 0
% 3.65/0.98  sim_tautology_del:                      6
% 3.65/0.98  sim_eq_tautology_del:                   8
% 3.65/0.98  sim_eq_res_simp:                        0
% 3.65/0.98  sim_fw_demodulated:                     3
% 3.65/0.98  sim_bw_demodulated:                     5
% 3.65/0.98  sim_light_normalised:                   103
% 3.65/0.98  sim_joinable_taut:                      0
% 3.65/0.98  sim_joinable_simp:                      0
% 3.65/0.98  sim_ac_normalised:                      0
% 3.65/0.98  sim_smt_subsumption:                    0
% 3.65/0.98  
%------------------------------------------------------------------------------
