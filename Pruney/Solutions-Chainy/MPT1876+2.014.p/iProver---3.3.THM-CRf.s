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
% DateTime   : Thu Dec  3 12:26:49 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :  232 (4564 expanded)
%              Number of clauses        :  151 (1177 expanded)
%              Number of leaves         :   22 (1024 expanded)
%              Depth                    :   26
%              Number of atoms          : 1008 (33672 expanded)
%              Number of equality atoms :  323 (2037 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK0(X0)) = X0
        & m1_subset_1(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK0(X0)) = X0
            & m1_subset_1(sK0(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f46,f47])).

fof(f70,plain,(
    ! [X0] :
      ( m1_subset_1(sK0(X0),X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

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
    inference(ennf_transformation,[],[f16])).

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

fof(f53,plain,(
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
    inference(flattening,[],[f53])).

fof(f56,plain,(
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

fof(f55,plain,
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

fof(f57,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f54,f56,f55])).

fof(f86,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f57])).

fof(f12,axiom,(
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

fof(f17,plain,(
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
    inference(pure_predicate_removal,[],[f12])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f17])).

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
    inference(flattening,[],[f37])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK1(X0,X1)) = X1
        & m1_pre_topc(sK1(X0,X1),X0)
        & ~ v2_struct_0(sK1(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK1(X0,X1)) = X1
            & m1_pre_topc(sK1(X0,X1),X0)
            & ~ v2_struct_0(sK1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f49])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f81,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f84,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f85,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f75,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f5,axiom,(
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

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f83,plain,(
    v2_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f87,plain,
    ( v1_zfmisc_1(sK4)
    | v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f13,axiom,(
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

fof(f18,plain,(
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
    inference(pure_predicate_removal,[],[f13])).

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
    inference(ennf_transformation,[],[f18])).

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

fof(f51,plain,(
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

fof(f52,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f51])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f82,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f9,axiom,(
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

fof(f32,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f67,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f65,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f59,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f61,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f79,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK2(X0,X1)) = X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK2(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f60,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_tdlat_3(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v2_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f88,plain,
    ( ~ v1_zfmisc_1(sK4)
    | ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f71,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK0(X0)) = X0
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_14,plain,
    ( m1_subset_1(sK0(X0),X0)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3577,plain,
    ( m1_subset_1(sK0(X0_50),X0_50)
    | ~ v1_zfmisc_1(X0_50)
    | v1_xboole_0(X0_50) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_4316,plain,
    ( m1_subset_1(sK0(X0_50),X0_50) = iProver_top
    | v1_zfmisc_1(X0_50) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3577])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3566,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_4327,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3566])).

cnf(c_16,plain,
    ( m1_pre_topc(sK1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_3575,plain,
    ( m1_pre_topc(sK1(X0_49,X0_50),X0_49)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49)))
    | v2_struct_0(X0_49)
    | ~ l1_pre_topc(X0_49)
    | v1_xboole_0(X0_50) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_4318,plain,
    ( m1_pre_topc(sK1(X0_49,X0_50),X0_49) = iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49))) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | l1_pre_topc(X0_49) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3575])).

cnf(c_5128,plain,
    ( m1_pre_topc(sK1(sK3,sK4),sK3) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4327,c_4318])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_31,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_34,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_35,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_36,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3639,plain,
    ( m1_pre_topc(sK1(X0_49,X0_50),X0_49) = iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49))) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | l1_pre_topc(X0_49) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3575])).

cnf(c_3641,plain,
    ( m1_pre_topc(sK1(sK3,sK4),sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3639])).

cnf(c_5395,plain,
    ( m1_pre_topc(sK1(sK3,sK4),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5128,c_31,c_34,c_35,c_36,c_3641])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3576,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49)))
    | v2_struct_0(X0_49)
    | ~ l1_pre_topc(X0_49)
    | v1_xboole_0(X0_50)
    | u1_struct_0(sK1(X0_49,X0_50)) = X0_50 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_4317,plain,
    ( u1_struct_0(sK1(X0_49,X0_50)) = X0_50
    | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49))) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | l1_pre_topc(X0_49) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3576])).

cnf(c_5031,plain,
    ( u1_struct_0(sK1(sK3,sK4)) = sK4
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4327,c_4317])).

cnf(c_3637,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(sK4)
    | u1_struct_0(sK1(sK3,sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_3576])).

cnf(c_5242,plain,
    ( u1_struct_0(sK1(sK3,sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5031,c_30,c_27,c_26,c_25,c_3637])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3583,plain,
    ( ~ m1_pre_topc(X0_49,X1_49)
    | ~ m1_subset_1(X0_50,u1_struct_0(X0_49))
    | m1_subset_1(X0_50,u1_struct_0(X1_49))
    | v2_struct_0(X1_49)
    | v2_struct_0(X0_49)
    | ~ l1_pre_topc(X1_49) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_4310,plain,
    ( m1_pre_topc(X0_49,X1_49) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(X0_49)) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(X1_49)) = iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v2_struct_0(X1_49) = iProver_top
    | l1_pre_topc(X1_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3583])).

cnf(c_5249,plain,
    ( m1_pre_topc(sK1(sK3,sK4),X0_49) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(X0_49)) = iProver_top
    | m1_subset_1(X0_50,sK4) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v2_struct_0(sK1(sK3,sK4)) = iProver_top
    | l1_pre_topc(X0_49) != iProver_top ),
    inference(superposition,[status(thm)],[c_5242,c_4310])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK1(X1,X0))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3574,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49)))
    | v2_struct_0(X0_49)
    | ~ v2_struct_0(sK1(X0_49,X0_50))
    | ~ l1_pre_topc(X0_49)
    | v1_xboole_0(X0_50) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_3642,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49))) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v2_struct_0(sK1(X0_49,X0_50)) != iProver_top
    | l1_pre_topc(X0_49) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3574])).

cnf(c_3644,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_struct_0(sK1(sK3,sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3642])).

cnf(c_6715,plain,
    ( v2_struct_0(X0_49) = iProver_top
    | m1_subset_1(X0_50,sK4) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(X0_49)) = iProver_top
    | m1_pre_topc(sK1(sK3,sK4),X0_49) != iProver_top
    | l1_pre_topc(X0_49) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5249,c_31,c_34,c_35,c_36,c_3644])).

cnf(c_6716,plain,
    ( m1_pre_topc(sK1(sK3,sK4),X0_49) != iProver_top
    | m1_subset_1(X0_50,u1_struct_0(X0_49)) = iProver_top
    | m1_subset_1(X0_50,sK4) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | l1_pre_topc(X0_49) != iProver_top ),
    inference(renaming,[status(thm)],[c_6715])).

cnf(c_6726,plain,
    ( m1_subset_1(X0_50,u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(X0_50,sK4) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5395,c_6716])).

cnf(c_6803,plain,
    ( m1_subset_1(X0_50,u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(X0_50,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6726,c_31,c_34])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3582,plain,
    ( ~ m1_subset_1(X0_50,X1_50)
    | v1_xboole_0(X1_50)
    | k6_domain_1(X1_50,X0_50) = k1_tarski(X0_50) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_4311,plain,
    ( k6_domain_1(X0_50,X1_50) = k1_tarski(X1_50)
    | m1_subset_1(X1_50,X0_50) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3582])).

cnf(c_6812,plain,
    ( k6_domain_1(u1_struct_0(sK3),X0_50) = k1_tarski(X0_50)
    | m1_subset_1(X0_50,sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6803,c_4311])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3585,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
    | ~ v1_xboole_0(X1_50)
    | v1_xboole_0(X0_50) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_4308,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(X1_50)) != iProver_top
    | v1_xboole_0(X1_50) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3585])).

cnf(c_4700,plain,
    ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4327,c_4308])).

cnf(c_7190,plain,
    ( m1_subset_1(X0_50,sK4) != iProver_top
    | k6_domain_1(u1_struct_0(sK3),X0_50) = k1_tarski(X0_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6812,c_35,c_4700])).

cnf(c_7191,plain,
    ( k6_domain_1(u1_struct_0(sK3),X0_50) = k1_tarski(X0_50)
    | m1_subset_1(X0_50,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_7190])).

cnf(c_7198,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k1_tarski(sK0(sK4))
    | v1_zfmisc_1(sK4) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4316,c_7191])).

cnf(c_28,negated_conjecture,
    ( v2_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_24,negated_conjecture,
    ( v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(sK4) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_21,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK2(X1,X0))
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_223,plain,
    ( v1_zfmisc_1(sK4)
    | v2_tex_2(sK4,sK3) ),
    inference(prop_impl,[status(thm)],[c_24])).

cnf(c_224,plain,
    ( v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(sK4) ),
    inference(renaming,[status(thm)],[c_223])).

cnf(c_1025,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK2(X1,X0))
    | v1_zfmisc_1(sK4)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK3 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_224])).

cnf(c_1026,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ v2_struct_0(sK2(sK3,sK4))
    | v2_struct_0(sK3)
    | v1_zfmisc_1(sK4)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1025])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1028,plain,
    ( ~ v2_struct_0(sK2(sK3,sK4))
    | v1_zfmisc_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1026,c_30,c_29,c_27,c_26,c_25])).

cnf(c_20,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tdlat_3(sK2(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1039,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tdlat_3(sK2(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v1_zfmisc_1(sK4)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK3 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_224])).

cnf(c_1040,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_tdlat_3(sK2(sK3,sK4))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | v1_zfmisc_1(sK4)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1039])).

cnf(c_1042,plain,
    ( v1_tdlat_3(sK2(sK3,sK4))
    | v1_zfmisc_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1040,c_30,c_29,c_27,c_26,c_25])).

cnf(c_3588,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_3618,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_3588])).

cnf(c_9,plain,
    ( ~ v2_tdlat_3(X0)
    | ~ v1_tdlat_3(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_7,plain,
    ( ~ v2_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_175,plain,
    ( ~ v1_tdlat_3(X0)
    | ~ v2_tdlat_3(X0)
    | v2_struct_0(X0)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_7])).

cnf(c_176,plain,
    ( ~ v2_tdlat_3(X0)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_175])).

cnf(c_1,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_3,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_383,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_1,c_3])).

cnf(c_401,plain,
    ( ~ v2_tdlat_3(X0)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_176,c_383])).

cnf(c_3560,plain,
    ( ~ v2_tdlat_3(X0_49)
    | ~ v1_tdlat_3(X0_49)
    | v2_struct_0(X0_49)
    | v1_zfmisc_1(u1_struct_0(X0_49))
    | ~ l1_pre_topc(X0_49) ),
    inference(subtyping,[status(esa)],[c_401])).

cnf(c_4711,plain,
    ( ~ v2_tdlat_3(sK2(X0_49,X0_50))
    | ~ v1_tdlat_3(sK2(X0_49,X0_50))
    | v2_struct_0(sK2(X0_49,X0_50))
    | v1_zfmisc_1(u1_struct_0(sK2(X0_49,X0_50)))
    | ~ l1_pre_topc(sK2(X0_49,X0_50)) ),
    inference(instantiation,[status(thm)],[c_3560])).

cnf(c_4713,plain,
    ( ~ v2_tdlat_3(sK2(sK3,sK4))
    | ~ v1_tdlat_3(sK2(sK3,sK4))
    | v2_struct_0(sK2(sK3,sK4))
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
    | ~ l1_pre_topc(sK2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_4711])).

cnf(c_3567,negated_conjecture,
    ( v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(sK4) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_4326,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3567])).

cnf(c_18,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK2(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_3573,plain,
    ( ~ v2_tex_2(X0_50,X0_49)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49)))
    | ~ v2_pre_topc(X0_49)
    | v2_struct_0(X0_49)
    | ~ l1_pre_topc(X0_49)
    | v1_xboole_0(X0_50)
    | u1_struct_0(sK2(X0_49,X0_50)) = X0_50 ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_4320,plain,
    ( u1_struct_0(sK2(X0_49,X0_50)) = X0_50
    | v2_tex_2(X0_50,X0_49) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49))) != iProver_top
    | v2_pre_topc(X0_49) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | l1_pre_topc(X0_49) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3573])).

cnf(c_5632,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | v2_tex_2(sK4,sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4327,c_4320])).

cnf(c_32,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6061,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | v2_tex_2(sK4,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5632,c_31,c_32,c_34,c_35])).

cnf(c_6067,plain,
    ( u1_struct_0(sK2(sK3,sK4)) = sK4
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4326,c_6061])).

cnf(c_6068,plain,
    ( v1_zfmisc_1(sK4)
    | u1_struct_0(sK2(sK3,sK4)) = sK4 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6067])).

cnf(c_19,plain,
    ( ~ v2_tex_2(X0,X1)
    | m1_pre_topc(sK2(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_3572,plain,
    ( ~ v2_tex_2(X0_50,X0_49)
    | m1_pre_topc(sK2(X0_49,X0_50),X0_49)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49)))
    | ~ v2_pre_topc(X0_49)
    | v2_struct_0(X0_49)
    | ~ l1_pre_topc(X0_49)
    | v1_xboole_0(X0_50) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_4321,plain,
    ( v2_tex_2(X0_50,X0_49) != iProver_top
    | m1_pre_topc(sK2(X0_49,X0_50),X0_49) = iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49))) != iProver_top
    | v2_pre_topc(X0_49) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | l1_pre_topc(X0_49) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3572])).

cnf(c_5825,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | m1_pre_topc(sK2(sK3,sK4),sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4327,c_4321])).

cnf(c_6203,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | m1_pre_topc(sK2(sK3,sK4),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5825,c_31,c_32,c_34,c_35])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3584,plain,
    ( ~ m1_pre_topc(X0_49,X1_49)
    | ~ l1_pre_topc(X1_49)
    | l1_pre_topc(X0_49) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_4309,plain,
    ( m1_pre_topc(X0_49,X1_49) != iProver_top
    | l1_pre_topc(X1_49) != iProver_top
    | l1_pre_topc(X0_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3584])).

cnf(c_6209,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | l1_pre_topc(sK2(sK3,sK4)) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6203,c_4309])).

cnf(c_6210,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | l1_pre_topc(sK2(sK3,sK4))
    | ~ l1_pre_topc(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6209])).

cnf(c_3589,plain,
    ( X0_50 != X1_50
    | X2_50 != X1_50
    | X2_50 = X0_50 ),
    theory(equality)).

cnf(c_5735,plain,
    ( X0_50 != X1_50
    | X0_50 = u1_struct_0(X0_49)
    | u1_struct_0(X0_49) != X1_50 ),
    inference(instantiation,[status(thm)],[c_3589])).

cnf(c_6514,plain,
    ( X0_50 != X1_50
    | X0_50 = u1_struct_0(sK2(X0_49,X1_50))
    | u1_struct_0(sK2(X0_49,X1_50)) != X1_50 ),
    inference(instantiation,[status(thm)],[c_5735])).

cnf(c_6515,plain,
    ( u1_struct_0(sK2(sK3,sK4)) != sK4
    | sK4 = u1_struct_0(sK2(sK3,sK4))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_6514])).

cnf(c_3596,plain,
    ( ~ v1_zfmisc_1(X0_50)
    | v1_zfmisc_1(X1_50)
    | X1_50 != X0_50 ),
    theory(equality)).

cnf(c_6753,plain,
    ( v1_zfmisc_1(X0_50)
    | ~ v1_zfmisc_1(u1_struct_0(sK2(X0_49,X1_50)))
    | X0_50 != u1_struct_0(sK2(X0_49,X1_50)) ),
    inference(instantiation,[status(thm)],[c_3596])).

cnf(c_6756,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
    | v1_zfmisc_1(sK4)
    | sK4 != u1_struct_0(sK2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_6753])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_tdlat_3(X1)
    | v2_tdlat_3(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1397,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_tdlat_3(X2)
    | v2_tdlat_3(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | X2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_7])).

cnf(c_1398,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_tdlat_3(X1)
    | v2_tdlat_3(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_1397])).

cnf(c_3559,plain,
    ( ~ m1_pre_topc(X0_49,X1_49)
    | ~ v2_tdlat_3(X1_49)
    | v2_tdlat_3(X0_49)
    | v2_struct_0(X1_49)
    | ~ l1_pre_topc(X1_49) ),
    inference(subtyping,[status(esa)],[c_1398])).

cnf(c_4334,plain,
    ( m1_pre_topc(X0_49,X1_49) != iProver_top
    | v2_tdlat_3(X1_49) != iProver_top
    | v2_tdlat_3(X0_49) = iProver_top
    | v2_struct_0(X1_49) = iProver_top
    | l1_pre_topc(X1_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3559])).

cnf(c_7057,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v2_tdlat_3(sK2(sK3,sK4)) = iProver_top
    | v2_tdlat_3(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6203,c_4334])).

cnf(c_7107,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | v2_tdlat_3(sK2(sK3,sK4))
    | ~ v2_tdlat_3(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7057])).

cnf(c_7199,plain,
    ( ~ v1_zfmisc_1(sK4)
    | v1_xboole_0(sK4)
    | k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k1_tarski(sK0(sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7198])).

cnf(c_7201,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k1_tarski(sK0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7198,c_31,c_32,c_33,c_34,c_35,c_37,c_38,c_3618,c_4714,c_5918,c_6061,c_6196,c_6209,c_6515,c_6757,c_7057])).

cnf(c_22,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_3569,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0_49),X0_50),X0_49)
    | ~ m1_subset_1(X0_50,u1_struct_0(X0_49))
    | ~ v2_pre_topc(X0_49)
    | v2_struct_0(X0_49)
    | ~ l1_pre_topc(X0_49) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_4324,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0_49),X0_50),X0_49) = iProver_top
    | m1_subset_1(X0_50,u1_struct_0(X0_49)) != iProver_top
    | v2_pre_topc(X0_49) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | l1_pre_topc(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3569])).

cnf(c_7204,plain,
    ( v2_tex_2(k1_tarski(sK0(sK4)),sK3) = iProver_top
    | m1_subset_1(sK0(sK4),u1_struct_0(sK3)) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7201,c_4324])).

cnf(c_37,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_33,plain,
    ( v2_tdlat_3(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_23,negated_conjecture,
    ( ~ v2_tex_2(sK4,sK3)
    | ~ v1_zfmisc_1(sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_38,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v1_zfmisc_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4712,plain,
    ( v2_tdlat_3(sK2(X0_49,X0_50)) != iProver_top
    | v1_tdlat_3(sK2(X0_49,X0_50)) != iProver_top
    | v2_struct_0(sK2(X0_49,X0_50)) = iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2(X0_49,X0_50))) = iProver_top
    | l1_pre_topc(sK2(X0_49,X0_50)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4711])).

cnf(c_4714,plain,
    ( v2_tdlat_3(sK2(sK3,sK4)) != iProver_top
    | v1_tdlat_3(sK2(sK3,sK4)) != iProver_top
    | v2_struct_0(sK2(sK3,sK4)) = iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) = iProver_top
    | l1_pre_topc(sK2(sK3,sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4712])).

cnf(c_3570,plain,
    ( ~ v2_tex_2(X0_50,X0_49)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49)))
    | ~ v2_pre_topc(X0_49)
    | v2_struct_0(X0_49)
    | ~ v2_struct_0(sK2(X0_49,X0_50))
    | ~ l1_pre_topc(X0_49)
    | v1_xboole_0(X0_50) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_4323,plain,
    ( v2_tex_2(X0_50,X0_49) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49))) != iProver_top
    | v2_pre_topc(X0_49) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v2_struct_0(sK2(X0_49,X0_50)) != iProver_top
    | l1_pre_topc(X0_49) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3570])).

cnf(c_5918,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK2(sK3,sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4327,c_4323])).

cnf(c_3571,plain,
    ( ~ v2_tex_2(X0_50,X0_49)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49)))
    | v1_tdlat_3(sK2(X0_49,X0_50))
    | ~ v2_pre_topc(X0_49)
    | v2_struct_0(X0_49)
    | ~ l1_pre_topc(X0_49)
    | v1_xboole_0(X0_50) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_4322,plain,
    ( v2_tex_2(X0_50,X0_49) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49))) != iProver_top
    | v1_tdlat_3(sK2(X0_49,X0_50)) = iProver_top
    | v2_pre_topc(X0_49) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | l1_pre_topc(X0_49) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3571])).

cnf(c_5765,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v1_tdlat_3(sK2(sK3,sK4)) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4327,c_4322])).

cnf(c_6196,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v1_tdlat_3(sK2(sK3,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5765,c_31,c_32,c_34,c_35])).

cnf(c_6755,plain,
    ( X0_50 != u1_struct_0(sK2(X0_49,X1_50))
    | v1_zfmisc_1(X0_50) = iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2(X0_49,X1_50))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6753])).

cnf(c_6757,plain,
    ( sK4 != u1_struct_0(sK2(sK3,sK4))
    | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) != iProver_top
    | v1_zfmisc_1(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6755])).

cnf(c_7427,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7057,c_31,c_32,c_33,c_34,c_35,c_38,c_3618,c_4714,c_5918,c_6061,c_6196,c_6209,c_6515,c_6757])).

cnf(c_5023,plain,
    ( m1_pre_topc(X0_49,X1_49) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(X0_49)),u1_struct_0(X1_49)) = iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v2_struct_0(X1_49) = iProver_top
    | v1_zfmisc_1(u1_struct_0(X0_49)) != iProver_top
    | l1_pre_topc(X1_49) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_49)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4316,c_4310])).

cnf(c_7757,plain,
    ( m1_pre_topc(sK1(sK3,sK4),X0_49) != iProver_top
    | m1_subset_1(sK0(sK4),u1_struct_0(X0_49)) = iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v2_struct_0(sK1(sK3,sK4)) = iProver_top
    | v1_zfmisc_1(u1_struct_0(sK1(sK3,sK4))) != iProver_top
    | l1_pre_topc(X0_49) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5242,c_5023])).

cnf(c_7818,plain,
    ( m1_pre_topc(sK1(sK3,sK4),X0_49) != iProver_top
    | m1_subset_1(sK0(sK4),u1_struct_0(X0_49)) = iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v2_struct_0(sK1(sK3,sK4)) = iProver_top
    | v1_zfmisc_1(sK4) != iProver_top
    | l1_pre_topc(X0_49) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7757,c_5242])).

cnf(c_7834,plain,
    ( m1_pre_topc(sK1(sK3,sK4),sK3) != iProver_top
    | m1_subset_1(sK0(sK4),u1_struct_0(sK3)) = iProver_top
    | v2_struct_0(sK1(sK3,sK4)) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_zfmisc_1(sK4) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7818])).

cnf(c_7915,plain,
    ( v2_tex_2(k1_tarski(sK0(sK4)),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7204,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_3618,c_3641,c_3644,c_4714,c_5918,c_6061,c_6196,c_6209,c_6515,c_6757,c_7057,c_7834])).

cnf(c_7432,plain,
    ( v1_zfmisc_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4326,c_7427])).

cnf(c_4917,plain,
    ( k6_domain_1(X0_50,sK0(X0_50)) = k1_tarski(sK0(X0_50))
    | v1_zfmisc_1(X0_50) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(superposition,[status(thm)],[c_4316,c_4311])).

cnf(c_7561,plain,
    ( k6_domain_1(sK4,sK0(sK4)) = k1_tarski(sK0(sK4))
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_7432,c_4917])).

cnf(c_4930,plain,
    ( k6_domain_1(sK4,sK0(sK4)) = k1_tarski(sK0(sK4))
    | v1_zfmisc_1(sK4) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4917])).

cnf(c_7654,plain,
    ( k6_domain_1(sK4,sK0(sK4)) = k1_tarski(sK0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7561,c_31,c_32,c_33,c_34,c_35,c_37,c_38,c_3618,c_4714,c_4930,c_5918,c_6061,c_6196,c_6209,c_6515,c_6757,c_7057])).

cnf(c_13,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | k6_domain_1(X0,sK0(X0)) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3578,plain,
    ( ~ v1_zfmisc_1(X0_50)
    | v1_xboole_0(X0_50)
    | k6_domain_1(X0_50,sK0(X0_50)) = X0_50 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_4315,plain,
    ( k6_domain_1(X0_50,sK0(X0_50)) = X0_50
    | v1_zfmisc_1(X0_50) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3578])).

cnf(c_7562,plain,
    ( k6_domain_1(sK4,sK0(sK4)) = sK4
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_7432,c_4315])).

cnf(c_3630,plain,
    ( k6_domain_1(X0_50,sK0(X0_50)) = X0_50
    | v1_zfmisc_1(X0_50) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3578])).

cnf(c_3632,plain,
    ( k6_domain_1(sK4,sK0(sK4)) = sK4
    | v1_zfmisc_1(sK4) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3630])).

cnf(c_7574,plain,
    ( k6_domain_1(sK4,sK0(sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7562,c_31,c_32,c_33,c_34,c_35,c_37,c_38,c_3618,c_3632,c_4714,c_5918,c_6061,c_6196,c_6209,c_6515,c_6757,c_7057])).

cnf(c_7656,plain,
    ( k1_tarski(sK0(sK4)) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_7654,c_7574])).

cnf(c_7919,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7915,c_7656])).

cnf(c_7921,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7919,c_7427])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.10  % Command    : iproveropt_run.sh %d %s
% 0.10/0.30  % Computer   : n001.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % WCLimit    : 600
% 0.10/0.30  % DateTime   : Tue Dec  1 19:48:45 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.30  % Running in FOF mode
% 3.10/0.96  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/0.96  
% 3.10/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.10/0.96  
% 3.10/0.96  ------  iProver source info
% 3.10/0.96  
% 3.10/0.96  git: date: 2020-06-30 10:37:57 +0100
% 3.10/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.10/0.96  git: non_committed_changes: false
% 3.10/0.96  git: last_make_outside_of_git: false
% 3.10/0.96  
% 3.10/0.96  ------ 
% 3.10/0.96  
% 3.10/0.96  ------ Input Options
% 3.10/0.96  
% 3.10/0.96  --out_options                           all
% 3.10/0.96  --tptp_safe_out                         true
% 3.10/0.96  --problem_path                          ""
% 3.10/0.96  --include_path                          ""
% 3.10/0.96  --clausifier                            res/vclausify_rel
% 3.10/0.96  --clausifier_options                    --mode clausify
% 3.10/0.96  --stdin                                 false
% 3.10/0.96  --stats_out                             all
% 3.10/0.96  
% 3.10/0.96  ------ General Options
% 3.10/0.96  
% 3.10/0.96  --fof                                   false
% 3.10/0.96  --time_out_real                         305.
% 3.10/0.96  --time_out_virtual                      -1.
% 3.10/0.96  --symbol_type_check                     false
% 3.10/0.96  --clausify_out                          false
% 3.10/0.96  --sig_cnt_out                           false
% 3.10/0.96  --trig_cnt_out                          false
% 3.10/0.96  --trig_cnt_out_tolerance                1.
% 3.10/0.96  --trig_cnt_out_sk_spl                   false
% 3.10/0.96  --abstr_cl_out                          false
% 3.10/0.96  
% 3.10/0.96  ------ Global Options
% 3.10/0.96  
% 3.10/0.96  --schedule                              default
% 3.10/0.96  --add_important_lit                     false
% 3.10/0.96  --prop_solver_per_cl                    1000
% 3.10/0.96  --min_unsat_core                        false
% 3.10/0.96  --soft_assumptions                      false
% 3.10/0.96  --soft_lemma_size                       3
% 3.10/0.96  --prop_impl_unit_size                   0
% 3.10/0.96  --prop_impl_unit                        []
% 3.10/0.96  --share_sel_clauses                     true
% 3.10/0.96  --reset_solvers                         false
% 3.10/0.96  --bc_imp_inh                            [conj_cone]
% 3.10/0.96  --conj_cone_tolerance                   3.
% 3.10/0.96  --extra_neg_conj                        none
% 3.10/0.96  --large_theory_mode                     true
% 3.10/0.96  --prolific_symb_bound                   200
% 3.10/0.96  --lt_threshold                          2000
% 3.10/0.96  --clause_weak_htbl                      true
% 3.10/0.96  --gc_record_bc_elim                     false
% 3.10/0.96  
% 3.10/0.96  ------ Preprocessing Options
% 3.10/0.96  
% 3.10/0.96  --preprocessing_flag                    true
% 3.10/0.96  --time_out_prep_mult                    0.1
% 3.10/0.96  --splitting_mode                        input
% 3.10/0.96  --splitting_grd                         true
% 3.10/0.96  --splitting_cvd                         false
% 3.10/0.96  --splitting_cvd_svl                     false
% 3.10/0.96  --splitting_nvd                         32
% 3.10/0.96  --sub_typing                            true
% 3.10/0.96  --prep_gs_sim                           true
% 3.10/0.96  --prep_unflatten                        true
% 3.10/0.96  --prep_res_sim                          true
% 3.10/0.96  --prep_upred                            true
% 3.10/0.96  --prep_sem_filter                       exhaustive
% 3.10/0.96  --prep_sem_filter_out                   false
% 3.10/0.96  --pred_elim                             true
% 3.10/0.96  --res_sim_input                         true
% 3.10/0.96  --eq_ax_congr_red                       true
% 3.10/0.96  --pure_diseq_elim                       true
% 3.10/0.96  --brand_transform                       false
% 3.10/0.96  --non_eq_to_eq                          false
% 3.10/0.96  --prep_def_merge                        true
% 3.10/0.96  --prep_def_merge_prop_impl              false
% 3.10/0.96  --prep_def_merge_mbd                    true
% 3.10/0.96  --prep_def_merge_tr_red                 false
% 3.10/0.96  --prep_def_merge_tr_cl                  false
% 3.10/0.96  --smt_preprocessing                     true
% 3.10/0.96  --smt_ac_axioms                         fast
% 3.10/0.96  --preprocessed_out                      false
% 3.10/0.96  --preprocessed_stats                    false
% 3.10/0.96  
% 3.10/0.96  ------ Abstraction refinement Options
% 3.10/0.96  
% 3.10/0.96  --abstr_ref                             []
% 3.10/0.96  --abstr_ref_prep                        false
% 3.10/0.96  --abstr_ref_until_sat                   false
% 3.10/0.96  --abstr_ref_sig_restrict                funpre
% 3.10/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.10/0.96  --abstr_ref_under                       []
% 3.10/0.96  
% 3.10/0.96  ------ SAT Options
% 3.10/0.96  
% 3.10/0.96  --sat_mode                              false
% 3.10/0.96  --sat_fm_restart_options                ""
% 3.10/0.96  --sat_gr_def                            false
% 3.10/0.96  --sat_epr_types                         true
% 3.10/0.96  --sat_non_cyclic_types                  false
% 3.10/0.96  --sat_finite_models                     false
% 3.10/0.96  --sat_fm_lemmas                         false
% 3.10/0.96  --sat_fm_prep                           false
% 3.10/0.96  --sat_fm_uc_incr                        true
% 3.10/0.96  --sat_out_model                         small
% 3.10/0.96  --sat_out_clauses                       false
% 3.10/0.96  
% 3.10/0.96  ------ QBF Options
% 3.10/0.96  
% 3.10/0.96  --qbf_mode                              false
% 3.10/0.96  --qbf_elim_univ                         false
% 3.10/0.96  --qbf_dom_inst                          none
% 3.10/0.96  --qbf_dom_pre_inst                      false
% 3.10/0.96  --qbf_sk_in                             false
% 3.10/0.96  --qbf_pred_elim                         true
% 3.10/0.96  --qbf_split                             512
% 3.10/0.96  
% 3.10/0.96  ------ BMC1 Options
% 3.10/0.96  
% 3.10/0.96  --bmc1_incremental                      false
% 3.10/0.96  --bmc1_axioms                           reachable_all
% 3.10/0.96  --bmc1_min_bound                        0
% 3.10/0.96  --bmc1_max_bound                        -1
% 3.10/0.96  --bmc1_max_bound_default                -1
% 3.10/0.96  --bmc1_symbol_reachability              true
% 3.10/0.96  --bmc1_property_lemmas                  false
% 3.10/0.96  --bmc1_k_induction                      false
% 3.10/0.96  --bmc1_non_equiv_states                 false
% 3.10/0.96  --bmc1_deadlock                         false
% 3.10/0.96  --bmc1_ucm                              false
% 3.10/0.96  --bmc1_add_unsat_core                   none
% 3.10/0.96  --bmc1_unsat_core_children              false
% 3.10/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.10/0.96  --bmc1_out_stat                         full
% 3.10/0.96  --bmc1_ground_init                      false
% 3.10/0.96  --bmc1_pre_inst_next_state              false
% 3.10/0.96  --bmc1_pre_inst_state                   false
% 3.10/0.96  --bmc1_pre_inst_reach_state             false
% 3.10/0.96  --bmc1_out_unsat_core                   false
% 3.10/0.96  --bmc1_aig_witness_out                  false
% 3.10/0.96  --bmc1_verbose                          false
% 3.10/0.96  --bmc1_dump_clauses_tptp                false
% 3.10/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.10/0.96  --bmc1_dump_file                        -
% 3.10/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.10/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.10/0.96  --bmc1_ucm_extend_mode                  1
% 3.10/0.96  --bmc1_ucm_init_mode                    2
% 3.10/0.96  --bmc1_ucm_cone_mode                    none
% 3.10/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.10/0.96  --bmc1_ucm_relax_model                  4
% 3.10/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.10/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.10/0.96  --bmc1_ucm_layered_model                none
% 3.10/0.96  --bmc1_ucm_max_lemma_size               10
% 3.10/0.96  
% 3.10/0.96  ------ AIG Options
% 3.10/0.96  
% 3.10/0.96  --aig_mode                              false
% 3.10/0.96  
% 3.10/0.96  ------ Instantiation Options
% 3.10/0.96  
% 3.10/0.96  --instantiation_flag                    true
% 3.10/0.96  --inst_sos_flag                         false
% 3.10/0.96  --inst_sos_phase                        true
% 3.10/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.10/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.10/0.96  --inst_lit_sel_side                     num_symb
% 3.10/0.96  --inst_solver_per_active                1400
% 3.10/0.96  --inst_solver_calls_frac                1.
% 3.10/0.96  --inst_passive_queue_type               priority_queues
% 3.10/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.10/0.96  --inst_passive_queues_freq              [25;2]
% 3.10/0.96  --inst_dismatching                      true
% 3.10/0.96  --inst_eager_unprocessed_to_passive     true
% 3.10/0.96  --inst_prop_sim_given                   true
% 3.10/0.96  --inst_prop_sim_new                     false
% 3.10/0.96  --inst_subs_new                         false
% 3.10/0.96  --inst_eq_res_simp                      false
% 3.10/0.96  --inst_subs_given                       false
% 3.10/0.96  --inst_orphan_elimination               true
% 3.10/0.96  --inst_learning_loop_flag               true
% 3.10/0.96  --inst_learning_start                   3000
% 3.10/0.96  --inst_learning_factor                  2
% 3.10/0.96  --inst_start_prop_sim_after_learn       3
% 3.10/0.96  --inst_sel_renew                        solver
% 3.10/0.96  --inst_lit_activity_flag                true
% 3.10/0.96  --inst_restr_to_given                   false
% 3.10/0.96  --inst_activity_threshold               500
% 3.10/0.96  --inst_out_proof                        true
% 3.10/0.96  
% 3.10/0.96  ------ Resolution Options
% 3.10/0.96  
% 3.10/0.96  --resolution_flag                       true
% 3.10/0.96  --res_lit_sel                           adaptive
% 3.10/0.96  --res_lit_sel_side                      none
% 3.10/0.96  --res_ordering                          kbo
% 3.10/0.96  --res_to_prop_solver                    active
% 3.10/0.96  --res_prop_simpl_new                    false
% 3.10/0.96  --res_prop_simpl_given                  true
% 3.10/0.96  --res_passive_queue_type                priority_queues
% 3.10/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.10/0.96  --res_passive_queues_freq               [15;5]
% 3.10/0.96  --res_forward_subs                      full
% 3.10/0.96  --res_backward_subs                     full
% 3.10/0.96  --res_forward_subs_resolution           true
% 3.10/0.96  --res_backward_subs_resolution          true
% 3.10/0.96  --res_orphan_elimination                true
% 3.10/0.96  --res_time_limit                        2.
% 3.10/0.96  --res_out_proof                         true
% 3.10/0.96  
% 3.10/0.96  ------ Superposition Options
% 3.10/0.96  
% 3.10/0.96  --superposition_flag                    true
% 3.10/0.96  --sup_passive_queue_type                priority_queues
% 3.10/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.10/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.10/0.96  --demod_completeness_check              fast
% 3.10/0.96  --demod_use_ground                      true
% 3.10/0.96  --sup_to_prop_solver                    passive
% 3.10/0.96  --sup_prop_simpl_new                    true
% 3.10/0.96  --sup_prop_simpl_given                  true
% 3.10/0.96  --sup_fun_splitting                     false
% 3.10/0.96  --sup_smt_interval                      50000
% 3.10/0.96  
% 3.10/0.96  ------ Superposition Simplification Setup
% 3.10/0.96  
% 3.10/0.96  --sup_indices_passive                   []
% 3.10/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.10/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.96  --sup_full_bw                           [BwDemod]
% 3.10/0.96  --sup_immed_triv                        [TrivRules]
% 3.10/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.10/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.96  --sup_immed_bw_main                     []
% 3.10/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.10/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/0.96  
% 3.10/0.96  ------ Combination Options
% 3.10/0.96  
% 3.10/0.96  --comb_res_mult                         3
% 3.10/0.96  --comb_sup_mult                         2
% 3.10/0.96  --comb_inst_mult                        10
% 3.10/0.96  
% 3.10/0.96  ------ Debug Options
% 3.10/0.96  
% 3.10/0.96  --dbg_backtrace                         false
% 3.10/0.96  --dbg_dump_prop_clauses                 false
% 3.10/0.96  --dbg_dump_prop_clauses_file            -
% 3.10/0.96  --dbg_out_stat                          false
% 3.10/0.96  ------ Parsing...
% 3.10/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.10/0.96  
% 3.10/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.10/0.96  
% 3.10/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.10/0.96  
% 3.10/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.10/0.96  ------ Proving...
% 3.10/0.96  ------ Problem Properties 
% 3.10/0.96  
% 3.10/0.96  
% 3.10/0.96  clauses                                 27
% 3.10/0.96  conjectures                             8
% 3.10/0.96  EPR                                     11
% 3.10/0.96  Horn                                    11
% 3.10/0.96  unary                                   6
% 3.10/0.96  binary                                  2
% 3.10/0.96  lits                                    99
% 3.10/0.96  lits eq                                 5
% 3.10/0.96  fd_pure                                 0
% 3.10/0.96  fd_pseudo                               0
% 3.10/0.96  fd_cond                                 0
% 3.10/0.96  fd_pseudo_cond                          0
% 3.10/0.96  AC symbols                              0
% 3.10/0.96  
% 3.10/0.96  ------ Schedule dynamic 5 is on 
% 3.10/0.96  
% 3.10/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.10/0.96  
% 3.10/0.96  
% 3.10/0.96  ------ 
% 3.10/0.96  Current options:
% 3.10/0.96  ------ 
% 3.10/0.96  
% 3.10/0.96  ------ Input Options
% 3.10/0.96  
% 3.10/0.96  --out_options                           all
% 3.10/0.96  --tptp_safe_out                         true
% 3.10/0.96  --problem_path                          ""
% 3.10/0.96  --include_path                          ""
% 3.10/0.96  --clausifier                            res/vclausify_rel
% 3.10/0.96  --clausifier_options                    --mode clausify
% 3.10/0.96  --stdin                                 false
% 3.10/0.96  --stats_out                             all
% 3.10/0.96  
% 3.10/0.96  ------ General Options
% 3.10/0.96  
% 3.10/0.96  --fof                                   false
% 3.10/0.96  --time_out_real                         305.
% 3.10/0.96  --time_out_virtual                      -1.
% 3.10/0.96  --symbol_type_check                     false
% 3.10/0.96  --clausify_out                          false
% 3.10/0.96  --sig_cnt_out                           false
% 3.10/0.96  --trig_cnt_out                          false
% 3.10/0.96  --trig_cnt_out_tolerance                1.
% 3.10/0.96  --trig_cnt_out_sk_spl                   false
% 3.10/0.96  --abstr_cl_out                          false
% 3.10/0.96  
% 3.10/0.96  ------ Global Options
% 3.10/0.96  
% 3.10/0.96  --schedule                              default
% 3.10/0.96  --add_important_lit                     false
% 3.10/0.96  --prop_solver_per_cl                    1000
% 3.10/0.96  --min_unsat_core                        false
% 3.10/0.96  --soft_assumptions                      false
% 3.10/0.96  --soft_lemma_size                       3
% 3.10/0.96  --prop_impl_unit_size                   0
% 3.10/0.96  --prop_impl_unit                        []
% 3.10/0.96  --share_sel_clauses                     true
% 3.10/0.96  --reset_solvers                         false
% 3.10/0.96  --bc_imp_inh                            [conj_cone]
% 3.10/0.96  --conj_cone_tolerance                   3.
% 3.10/0.96  --extra_neg_conj                        none
% 3.10/0.96  --large_theory_mode                     true
% 3.10/0.96  --prolific_symb_bound                   200
% 3.10/0.96  --lt_threshold                          2000
% 3.10/0.96  --clause_weak_htbl                      true
% 3.10/0.96  --gc_record_bc_elim                     false
% 3.10/0.96  
% 3.10/0.96  ------ Preprocessing Options
% 3.10/0.96  
% 3.10/0.96  --preprocessing_flag                    true
% 3.10/0.96  --time_out_prep_mult                    0.1
% 3.10/0.96  --splitting_mode                        input
% 3.10/0.96  --splitting_grd                         true
% 3.10/0.96  --splitting_cvd                         false
% 3.10/0.96  --splitting_cvd_svl                     false
% 3.10/0.96  --splitting_nvd                         32
% 3.10/0.96  --sub_typing                            true
% 3.10/0.96  --prep_gs_sim                           true
% 3.10/0.96  --prep_unflatten                        true
% 3.10/0.96  --prep_res_sim                          true
% 3.10/0.96  --prep_upred                            true
% 3.10/0.96  --prep_sem_filter                       exhaustive
% 3.10/0.96  --prep_sem_filter_out                   false
% 3.10/0.96  --pred_elim                             true
% 3.10/0.96  --res_sim_input                         true
% 3.10/0.96  --eq_ax_congr_red                       true
% 3.10/0.96  --pure_diseq_elim                       true
% 3.10/0.96  --brand_transform                       false
% 3.10/0.96  --non_eq_to_eq                          false
% 3.10/0.96  --prep_def_merge                        true
% 3.10/0.96  --prep_def_merge_prop_impl              false
% 3.10/0.96  --prep_def_merge_mbd                    true
% 3.10/0.96  --prep_def_merge_tr_red                 false
% 3.10/0.96  --prep_def_merge_tr_cl                  false
% 3.10/0.96  --smt_preprocessing                     true
% 3.10/0.96  --smt_ac_axioms                         fast
% 3.10/0.96  --preprocessed_out                      false
% 3.10/0.96  --preprocessed_stats                    false
% 3.10/0.96  
% 3.10/0.96  ------ Abstraction refinement Options
% 3.10/0.96  
% 3.10/0.96  --abstr_ref                             []
% 3.10/0.96  --abstr_ref_prep                        false
% 3.10/0.96  --abstr_ref_until_sat                   false
% 3.10/0.96  --abstr_ref_sig_restrict                funpre
% 3.10/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.10/0.96  --abstr_ref_under                       []
% 3.10/0.96  
% 3.10/0.96  ------ SAT Options
% 3.10/0.96  
% 3.10/0.96  --sat_mode                              false
% 3.10/0.96  --sat_fm_restart_options                ""
% 3.10/0.96  --sat_gr_def                            false
% 3.10/0.96  --sat_epr_types                         true
% 3.10/0.96  --sat_non_cyclic_types                  false
% 3.10/0.96  --sat_finite_models                     false
% 3.10/0.96  --sat_fm_lemmas                         false
% 3.10/0.96  --sat_fm_prep                           false
% 3.10/0.96  --sat_fm_uc_incr                        true
% 3.10/0.96  --sat_out_model                         small
% 3.10/0.96  --sat_out_clauses                       false
% 3.10/0.96  
% 3.10/0.96  ------ QBF Options
% 3.10/0.96  
% 3.10/0.96  --qbf_mode                              false
% 3.10/0.96  --qbf_elim_univ                         false
% 3.10/0.96  --qbf_dom_inst                          none
% 3.10/0.96  --qbf_dom_pre_inst                      false
% 3.10/0.96  --qbf_sk_in                             false
% 3.10/0.96  --qbf_pred_elim                         true
% 3.10/0.96  --qbf_split                             512
% 3.10/0.96  
% 3.10/0.96  ------ BMC1 Options
% 3.10/0.96  
% 3.10/0.96  --bmc1_incremental                      false
% 3.10/0.96  --bmc1_axioms                           reachable_all
% 3.10/0.96  --bmc1_min_bound                        0
% 3.10/0.96  --bmc1_max_bound                        -1
% 3.10/0.96  --bmc1_max_bound_default                -1
% 3.10/0.96  --bmc1_symbol_reachability              true
% 3.10/0.96  --bmc1_property_lemmas                  false
% 3.10/0.96  --bmc1_k_induction                      false
% 3.10/0.96  --bmc1_non_equiv_states                 false
% 3.10/0.96  --bmc1_deadlock                         false
% 3.10/0.96  --bmc1_ucm                              false
% 3.10/0.96  --bmc1_add_unsat_core                   none
% 3.10/0.96  --bmc1_unsat_core_children              false
% 3.10/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.10/0.96  --bmc1_out_stat                         full
% 3.10/0.96  --bmc1_ground_init                      false
% 3.10/0.96  --bmc1_pre_inst_next_state              false
% 3.10/0.96  --bmc1_pre_inst_state                   false
% 3.10/0.96  --bmc1_pre_inst_reach_state             false
% 3.10/0.96  --bmc1_out_unsat_core                   false
% 3.10/0.96  --bmc1_aig_witness_out                  false
% 3.10/0.96  --bmc1_verbose                          false
% 3.10/0.96  --bmc1_dump_clauses_tptp                false
% 3.10/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.10/0.96  --bmc1_dump_file                        -
% 3.10/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.10/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.10/0.96  --bmc1_ucm_extend_mode                  1
% 3.10/0.96  --bmc1_ucm_init_mode                    2
% 3.10/0.96  --bmc1_ucm_cone_mode                    none
% 3.10/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.10/0.96  --bmc1_ucm_relax_model                  4
% 3.10/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.10/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.10/0.96  --bmc1_ucm_layered_model                none
% 3.10/0.96  --bmc1_ucm_max_lemma_size               10
% 3.10/0.96  
% 3.10/0.96  ------ AIG Options
% 3.10/0.96  
% 3.10/0.96  --aig_mode                              false
% 3.10/0.96  
% 3.10/0.96  ------ Instantiation Options
% 3.10/0.96  
% 3.10/0.96  --instantiation_flag                    true
% 3.10/0.96  --inst_sos_flag                         false
% 3.10/0.96  --inst_sos_phase                        true
% 3.10/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.10/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.10/0.96  --inst_lit_sel_side                     none
% 3.10/0.96  --inst_solver_per_active                1400
% 3.10/0.96  --inst_solver_calls_frac                1.
% 3.10/0.96  --inst_passive_queue_type               priority_queues
% 3.10/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.10/0.96  --inst_passive_queues_freq              [25;2]
% 3.10/0.96  --inst_dismatching                      true
% 3.10/0.96  --inst_eager_unprocessed_to_passive     true
% 3.10/0.96  --inst_prop_sim_given                   true
% 3.10/0.96  --inst_prop_sim_new                     false
% 3.10/0.96  --inst_subs_new                         false
% 3.10/0.96  --inst_eq_res_simp                      false
% 3.10/0.96  --inst_subs_given                       false
% 3.10/0.96  --inst_orphan_elimination               true
% 3.10/0.96  --inst_learning_loop_flag               true
% 3.10/0.96  --inst_learning_start                   3000
% 3.10/0.96  --inst_learning_factor                  2
% 3.10/0.96  --inst_start_prop_sim_after_learn       3
% 3.10/0.96  --inst_sel_renew                        solver
% 3.10/0.96  --inst_lit_activity_flag                true
% 3.10/0.96  --inst_restr_to_given                   false
% 3.10/0.96  --inst_activity_threshold               500
% 3.10/0.96  --inst_out_proof                        true
% 3.10/0.96  
% 3.10/0.96  ------ Resolution Options
% 3.10/0.96  
% 3.10/0.96  --resolution_flag                       false
% 3.10/0.96  --res_lit_sel                           adaptive
% 3.10/0.96  --res_lit_sel_side                      none
% 3.10/0.96  --res_ordering                          kbo
% 3.10/0.96  --res_to_prop_solver                    active
% 3.10/0.96  --res_prop_simpl_new                    false
% 3.10/0.96  --res_prop_simpl_given                  true
% 3.10/0.96  --res_passive_queue_type                priority_queues
% 3.10/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.10/0.96  --res_passive_queues_freq               [15;5]
% 3.10/0.96  --res_forward_subs                      full
% 3.10/0.96  --res_backward_subs                     full
% 3.10/0.96  --res_forward_subs_resolution           true
% 3.10/0.96  --res_backward_subs_resolution          true
% 3.10/0.96  --res_orphan_elimination                true
% 3.10/0.96  --res_time_limit                        2.
% 3.10/0.96  --res_out_proof                         true
% 3.10/0.96  
% 3.10/0.96  ------ Superposition Options
% 3.10/0.96  
% 3.10/0.96  --superposition_flag                    true
% 3.10/0.96  --sup_passive_queue_type                priority_queues
% 3.10/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.10/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.10/0.96  --demod_completeness_check              fast
% 3.10/0.96  --demod_use_ground                      true
% 3.10/0.96  --sup_to_prop_solver                    passive
% 3.10/0.96  --sup_prop_simpl_new                    true
% 3.10/0.96  --sup_prop_simpl_given                  true
% 3.10/0.96  --sup_fun_splitting                     false
% 3.10/0.96  --sup_smt_interval                      50000
% 3.10/0.96  
% 3.10/0.96  ------ Superposition Simplification Setup
% 3.10/0.96  
% 3.10/0.96  --sup_indices_passive                   []
% 3.10/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.10/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.96  --sup_full_bw                           [BwDemod]
% 3.10/0.96  --sup_immed_triv                        [TrivRules]
% 3.10/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.10/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.96  --sup_immed_bw_main                     []
% 3.10/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.10/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/0.96  
% 3.10/0.96  ------ Combination Options
% 3.10/0.96  
% 3.10/0.96  --comb_res_mult                         3
% 3.10/0.96  --comb_sup_mult                         2
% 3.10/0.96  --comb_inst_mult                        10
% 3.10/0.96  
% 3.10/0.96  ------ Debug Options
% 3.10/0.96  
% 3.10/0.96  --dbg_backtrace                         false
% 3.10/0.96  --dbg_dump_prop_clauses                 false
% 3.10/0.96  --dbg_dump_prop_clauses_file            -
% 3.10/0.96  --dbg_out_stat                          false
% 3.10/0.96  
% 3.10/0.96  
% 3.10/0.96  
% 3.10/0.96  
% 3.10/0.96  ------ Proving...
% 3.10/0.96  
% 3.10/0.96  
% 3.10/0.96  % SZS status Theorem for theBenchmark.p
% 3.10/0.96  
% 3.10/0.96   Resolution empty clause
% 3.10/0.96  
% 3.10/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 3.10/0.96  
% 3.10/0.96  fof(f11,axiom,(
% 3.10/0.96    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 3.10/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.96  
% 3.10/0.96  fof(f36,plain,(
% 3.10/0.96    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 3.10/0.96    inference(ennf_transformation,[],[f11])).
% 3.10/0.96  
% 3.10/0.96  fof(f45,plain,(
% 3.10/0.96    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 3.10/0.96    inference(nnf_transformation,[],[f36])).
% 3.10/0.96  
% 3.10/0.96  fof(f46,plain,(
% 3.10/0.96    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 3.10/0.96    inference(rectify,[],[f45])).
% 3.10/0.96  
% 3.10/0.96  fof(f47,plain,(
% 3.10/0.96    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK0(X0)) = X0 & m1_subset_1(sK0(X0),X0)))),
% 3.10/0.96    introduced(choice_axiom,[])).
% 3.10/0.96  
% 3.10/0.96  fof(f48,plain,(
% 3.10/0.96    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK0(X0)) = X0 & m1_subset_1(sK0(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 3.10/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f46,f47])).
% 3.10/0.96  
% 3.10/0.96  fof(f70,plain,(
% 3.10/0.96    ( ! [X0] : (m1_subset_1(sK0(X0),X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 3.10/0.96    inference(cnf_transformation,[],[f48])).
% 3.10/0.96  
% 3.10/0.96  fof(f15,conjecture,(
% 3.10/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 3.10/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.96  
% 3.10/0.96  fof(f16,negated_conjecture,(
% 3.10/0.96    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 3.10/0.96    inference(negated_conjecture,[],[f15])).
% 3.10/0.96  
% 3.10/0.96  fof(f43,plain,(
% 3.10/0.96    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.10/0.96    inference(ennf_transformation,[],[f16])).
% 3.10/0.96  
% 3.10/0.96  fof(f44,plain,(
% 3.10/0.96    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.10/0.96    inference(flattening,[],[f43])).
% 3.10/0.96  
% 3.10/0.96  fof(f53,plain,(
% 3.10/0.96    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.10/0.96    inference(nnf_transformation,[],[f44])).
% 3.10/0.96  
% 3.10/0.96  fof(f54,plain,(
% 3.10/0.96    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.10/0.96    inference(flattening,[],[f53])).
% 3.10/0.96  
% 3.10/0.96  fof(f56,plain,(
% 3.10/0.96    ( ! [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,X0)) & (v1_zfmisc_1(sK4) | v2_tex_2(sK4,X0)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK4))) )),
% 3.10/0.96    introduced(choice_axiom,[])).
% 3.10/0.96  
% 3.10/0.96  fof(f55,plain,(
% 3.10/0.96    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK3)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 3.10/0.96    introduced(choice_axiom,[])).
% 3.10/0.96  
% 3.10/0.96  fof(f57,plain,(
% 3.10/0.96    ((~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3)) & (v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 3.10/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f54,f56,f55])).
% 3.10/0.96  
% 3.10/0.96  fof(f86,plain,(
% 3.10/0.96    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 3.10/0.96    inference(cnf_transformation,[],[f57])).
% 3.10/0.96  
% 3.10/0.96  fof(f12,axiom,(
% 3.10/0.96    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 3.10/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.96  
% 3.10/0.96  fof(f17,plain,(
% 3.10/0.96    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2))))),
% 3.10/0.96    inference(pure_predicate_removal,[],[f12])).
% 3.10/0.96  
% 3.10/0.96  fof(f37,plain,(
% 3.10/0.96    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.10/0.96    inference(ennf_transformation,[],[f17])).
% 3.10/0.96  
% 3.10/0.96  fof(f38,plain,(
% 3.10/0.96    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.10/0.96    inference(flattening,[],[f37])).
% 3.10/0.96  
% 3.10/0.96  fof(f49,plain,(
% 3.10/0.96    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(sK1(X0,X1)) = X1 & m1_pre_topc(sK1(X0,X1),X0) & ~v2_struct_0(sK1(X0,X1))))),
% 3.10/0.96    introduced(choice_axiom,[])).
% 3.10/0.96  
% 3.10/0.96  fof(f50,plain,(
% 3.10/0.96    ! [X0] : (! [X1] : ((u1_struct_0(sK1(X0,X1)) = X1 & m1_pre_topc(sK1(X0,X1),X0) & ~v2_struct_0(sK1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.10/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f49])).
% 3.10/0.96  
% 3.10/0.96  fof(f74,plain,(
% 3.10/0.96    ( ! [X0,X1] : (m1_pre_topc(sK1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.10/0.96    inference(cnf_transformation,[],[f50])).
% 3.10/0.96  
% 3.10/0.96  fof(f81,plain,(
% 3.10/0.96    ~v2_struct_0(sK3)),
% 3.10/0.96    inference(cnf_transformation,[],[f57])).
% 3.10/0.96  
% 3.10/0.96  fof(f84,plain,(
% 3.10/0.96    l1_pre_topc(sK3)),
% 3.10/0.96    inference(cnf_transformation,[],[f57])).
% 3.10/0.96  
% 3.10/0.96  fof(f85,plain,(
% 3.10/0.96    ~v1_xboole_0(sK4)),
% 3.10/0.96    inference(cnf_transformation,[],[f57])).
% 3.10/0.96  
% 3.10/0.96  fof(f75,plain,(
% 3.10/0.96    ( ! [X0,X1] : (u1_struct_0(sK1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.10/0.96    inference(cnf_transformation,[],[f50])).
% 3.10/0.96  
% 3.10/0.96  fof(f5,axiom,(
% 3.10/0.96    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 3.10/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.96  
% 3.10/0.96  fof(f24,plain,(
% 3.10/0.96    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.10/0.96    inference(ennf_transformation,[],[f5])).
% 3.10/0.96  
% 3.10/0.96  fof(f25,plain,(
% 3.10/0.96    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.10/0.96    inference(flattening,[],[f24])).
% 3.10/0.96  
% 3.10/0.96  fof(f62,plain,(
% 3.10/0.96    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.10/0.96    inference(cnf_transformation,[],[f25])).
% 3.10/0.96  
% 3.10/0.96  fof(f73,plain,(
% 3.10/0.96    ( ! [X0,X1] : (~v2_struct_0(sK1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.10/0.96    inference(cnf_transformation,[],[f50])).
% 3.10/0.96  
% 3.10/0.96  fof(f6,axiom,(
% 3.10/0.96    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 3.10/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.96  
% 3.10/0.96  fof(f26,plain,(
% 3.10/0.96    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.10/0.96    inference(ennf_transformation,[],[f6])).
% 3.10/0.96  
% 3.10/0.96  fof(f27,plain,(
% 3.10/0.96    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.10/0.96    inference(flattening,[],[f26])).
% 3.10/0.96  
% 3.10/0.96  fof(f63,plain,(
% 3.10/0.96    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.10/0.96    inference(cnf_transformation,[],[f27])).
% 3.10/0.96  
% 3.10/0.96  fof(f1,axiom,(
% 3.10/0.96    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.10/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.96  
% 3.10/0.96  fof(f19,plain,(
% 3.10/0.96    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.10/0.96    inference(ennf_transformation,[],[f1])).
% 3.10/0.96  
% 3.10/0.96  fof(f58,plain,(
% 3.10/0.96    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.10/0.96    inference(cnf_transformation,[],[f19])).
% 3.10/0.96  
% 3.10/0.96  fof(f83,plain,(
% 3.10/0.96    v2_tdlat_3(sK3)),
% 3.10/0.96    inference(cnf_transformation,[],[f57])).
% 3.10/0.96  
% 3.10/0.96  fof(f87,plain,(
% 3.10/0.96    v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3)),
% 3.10/0.96    inference(cnf_transformation,[],[f57])).
% 3.10/0.96  
% 3.10/0.96  fof(f13,axiom,(
% 3.10/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 3.10/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.96  
% 3.10/0.96  fof(f18,plain,(
% 3.10/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 3.10/0.96    inference(pure_predicate_removal,[],[f13])).
% 3.10/0.96  
% 3.10/0.96  fof(f39,plain,(
% 3.10/0.96    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.10/0.96    inference(ennf_transformation,[],[f18])).
% 3.10/0.96  
% 3.10/0.96  fof(f40,plain,(
% 3.10/0.96    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.10/0.96    inference(flattening,[],[f39])).
% 3.10/0.96  
% 3.10/0.96  fof(f51,plain,(
% 3.10/0.96    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_tdlat_3(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))))),
% 3.10/0.96    introduced(choice_axiom,[])).
% 3.10/0.96  
% 3.10/0.96  fof(f52,plain,(
% 3.10/0.96    ! [X0] : (! [X1] : ((u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_tdlat_3(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.10/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f51])).
% 3.10/0.96  
% 3.10/0.96  fof(f76,plain,(
% 3.10/0.96    ( ! [X0,X1] : (~v2_struct_0(sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.10/0.96    inference(cnf_transformation,[],[f52])).
% 3.10/0.96  
% 3.10/0.96  fof(f82,plain,(
% 3.10/0.96    v2_pre_topc(sK3)),
% 3.10/0.96    inference(cnf_transformation,[],[f57])).
% 3.10/0.96  
% 3.10/0.96  fof(f77,plain,(
% 3.10/0.96    ( ! [X0,X1] : (v1_tdlat_3(sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.10/0.96    inference(cnf_transformation,[],[f52])).
% 3.10/0.96  
% 3.10/0.96  fof(f9,axiom,(
% 3.10/0.96    ! [X0] : (l1_pre_topc(X0) => ((v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0))))),
% 3.10/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.96  
% 3.10/0.96  fof(f32,plain,(
% 3.10/0.96    ! [X0] : (((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | (~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.10/0.96    inference(ennf_transformation,[],[f9])).
% 3.10/0.96  
% 3.10/0.96  fof(f33,plain,(
% 3.10/0.96    ! [X0] : ((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.10/0.96    inference(flattening,[],[f32])).
% 3.10/0.96  
% 3.10/0.96  fof(f67,plain,(
% 3.10/0.96    ( ! [X0] : (v7_struct_0(X0) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.10/0.96    inference(cnf_transformation,[],[f33])).
% 3.10/0.96  
% 3.10/0.96  fof(f8,axiom,(
% 3.10/0.96    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 3.10/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.96  
% 3.10/0.96  fof(f30,plain,(
% 3.10/0.96    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 3.10/0.96    inference(ennf_transformation,[],[f8])).
% 3.10/0.96  
% 3.10/0.96  fof(f31,plain,(
% 3.10/0.96    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 3.10/0.96    inference(flattening,[],[f30])).
% 3.10/0.96  
% 3.10/0.96  fof(f65,plain,(
% 3.10/0.96    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 3.10/0.96    inference(cnf_transformation,[],[f31])).
% 3.10/0.96  
% 3.10/0.96  fof(f2,axiom,(
% 3.10/0.96    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.10/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.96  
% 3.10/0.96  fof(f20,plain,(
% 3.10/0.96    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.10/0.96    inference(ennf_transformation,[],[f2])).
% 3.10/0.96  
% 3.10/0.96  fof(f59,plain,(
% 3.10/0.96    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.10/0.96    inference(cnf_transformation,[],[f20])).
% 3.10/0.96  
% 3.10/0.96  fof(f4,axiom,(
% 3.10/0.96    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 3.10/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.96  
% 3.10/0.96  fof(f22,plain,(
% 3.10/0.96    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 3.10/0.96    inference(ennf_transformation,[],[f4])).
% 3.10/0.96  
% 3.10/0.96  fof(f23,plain,(
% 3.10/0.96    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 3.10/0.96    inference(flattening,[],[f22])).
% 3.10/0.96  
% 3.10/0.96  fof(f61,plain,(
% 3.10/0.96    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 3.10/0.96    inference(cnf_transformation,[],[f23])).
% 3.10/0.96  
% 3.10/0.96  fof(f79,plain,(
% 3.10/0.96    ( ! [X0,X1] : (u1_struct_0(sK2(X0,X1)) = X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.10/0.96    inference(cnf_transformation,[],[f52])).
% 3.10/0.96  
% 3.10/0.96  fof(f78,plain,(
% 3.10/0.96    ( ! [X0,X1] : (m1_pre_topc(sK2(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.10/0.96    inference(cnf_transformation,[],[f52])).
% 3.10/0.96  
% 3.10/0.96  fof(f3,axiom,(
% 3.10/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.10/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.96  
% 3.10/0.96  fof(f21,plain,(
% 3.10/0.96    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.10/0.96    inference(ennf_transformation,[],[f3])).
% 3.10/0.96  
% 3.10/0.96  fof(f60,plain,(
% 3.10/0.96    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.10/0.96    inference(cnf_transformation,[],[f21])).
% 3.10/0.96  
% 3.10/0.96  fof(f10,axiom,(
% 3.10/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_tdlat_3(X1)))),
% 3.10/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.96  
% 3.10/0.96  fof(f34,plain,(
% 3.10/0.96    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.10/0.96    inference(ennf_transformation,[],[f10])).
% 3.10/0.96  
% 3.10/0.96  fof(f35,plain,(
% 3.10/0.96    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.10/0.96    inference(flattening,[],[f34])).
% 3.10/0.96  
% 3.10/0.96  fof(f69,plain,(
% 3.10/0.96    ( ! [X0,X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.10/0.96    inference(cnf_transformation,[],[f35])).
% 3.10/0.96  
% 3.10/0.96  fof(f14,axiom,(
% 3.10/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 3.10/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/0.96  
% 3.10/0.96  fof(f41,plain,(
% 3.10/0.96    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.10/0.96    inference(ennf_transformation,[],[f14])).
% 3.10/0.96  
% 3.10/0.96  fof(f42,plain,(
% 3.10/0.96    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.10/0.96    inference(flattening,[],[f41])).
% 3.10/0.96  
% 3.10/0.96  fof(f80,plain,(
% 3.10/0.96    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.10/0.96    inference(cnf_transformation,[],[f42])).
% 3.10/0.96  
% 3.10/0.96  fof(f88,plain,(
% 3.10/0.96    ~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3)),
% 3.10/0.96    inference(cnf_transformation,[],[f57])).
% 3.10/0.96  
% 3.10/0.96  fof(f71,plain,(
% 3.10/0.96    ( ! [X0] : (k6_domain_1(X0,sK0(X0)) = X0 | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 3.10/0.96    inference(cnf_transformation,[],[f48])).
% 3.10/0.96  
% 3.10/0.96  cnf(c_14,plain,
% 3.10/0.96      ( m1_subset_1(sK0(X0),X0) | ~ v1_zfmisc_1(X0) | v1_xboole_0(X0) ),
% 3.10/0.96      inference(cnf_transformation,[],[f70]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_3577,plain,
% 3.10/0.96      ( m1_subset_1(sK0(X0_50),X0_50)
% 3.10/0.96      | ~ v1_zfmisc_1(X0_50)
% 3.10/0.96      | v1_xboole_0(X0_50) ),
% 3.10/0.96      inference(subtyping,[status(esa)],[c_14]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_4316,plain,
% 3.10/0.96      ( m1_subset_1(sK0(X0_50),X0_50) = iProver_top
% 3.10/0.96      | v1_zfmisc_1(X0_50) != iProver_top
% 3.10/0.96      | v1_xboole_0(X0_50) = iProver_top ),
% 3.10/0.96      inference(predicate_to_equality,[status(thm)],[c_3577]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_25,negated_conjecture,
% 3.10/0.96      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.10/0.96      inference(cnf_transformation,[],[f86]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_3566,negated_conjecture,
% 3.10/0.96      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.10/0.96      inference(subtyping,[status(esa)],[c_25]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_4327,plain,
% 3.10/0.96      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.10/0.96      inference(predicate_to_equality,[status(thm)],[c_3566]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_16,plain,
% 3.10/0.96      ( m1_pre_topc(sK1(X0,X1),X0)
% 3.10/0.96      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.10/0.96      | v2_struct_0(X0)
% 3.10/0.96      | ~ l1_pre_topc(X0)
% 3.10/0.96      | v1_xboole_0(X1) ),
% 3.10/0.96      inference(cnf_transformation,[],[f74]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_3575,plain,
% 3.10/0.96      ( m1_pre_topc(sK1(X0_49,X0_50),X0_49)
% 3.10/0.96      | ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49)))
% 3.10/0.96      | v2_struct_0(X0_49)
% 3.10/0.96      | ~ l1_pre_topc(X0_49)
% 3.10/0.96      | v1_xboole_0(X0_50) ),
% 3.10/0.96      inference(subtyping,[status(esa)],[c_16]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_4318,plain,
% 3.10/0.96      ( m1_pre_topc(sK1(X0_49,X0_50),X0_49) = iProver_top
% 3.10/0.96      | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49))) != iProver_top
% 3.10/0.96      | v2_struct_0(X0_49) = iProver_top
% 3.10/0.96      | l1_pre_topc(X0_49) != iProver_top
% 3.10/0.96      | v1_xboole_0(X0_50) = iProver_top ),
% 3.10/0.96      inference(predicate_to_equality,[status(thm)],[c_3575]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_5128,plain,
% 3.10/0.96      ( m1_pre_topc(sK1(sK3,sK4),sK3) = iProver_top
% 3.10/0.96      | v2_struct_0(sK3) = iProver_top
% 3.10/0.96      | l1_pre_topc(sK3) != iProver_top
% 3.10/0.96      | v1_xboole_0(sK4) = iProver_top ),
% 3.10/0.96      inference(superposition,[status(thm)],[c_4327,c_4318]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_30,negated_conjecture,
% 3.10/0.96      ( ~ v2_struct_0(sK3) ),
% 3.10/0.96      inference(cnf_transformation,[],[f81]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_31,plain,
% 3.10/0.96      ( v2_struct_0(sK3) != iProver_top ),
% 3.10/0.96      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_27,negated_conjecture,
% 3.10/0.96      ( l1_pre_topc(sK3) ),
% 3.10/0.96      inference(cnf_transformation,[],[f84]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_34,plain,
% 3.10/0.96      ( l1_pre_topc(sK3) = iProver_top ),
% 3.10/0.96      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_26,negated_conjecture,
% 3.10/0.96      ( ~ v1_xboole_0(sK4) ),
% 3.10/0.96      inference(cnf_transformation,[],[f85]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_35,plain,
% 3.10/0.96      ( v1_xboole_0(sK4) != iProver_top ),
% 3.10/0.96      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_36,plain,
% 3.10/0.96      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.10/0.96      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_3639,plain,
% 3.10/0.96      ( m1_pre_topc(sK1(X0_49,X0_50),X0_49) = iProver_top
% 3.10/0.96      | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49))) != iProver_top
% 3.10/0.96      | v2_struct_0(X0_49) = iProver_top
% 3.10/0.96      | l1_pre_topc(X0_49) != iProver_top
% 3.10/0.96      | v1_xboole_0(X0_50) = iProver_top ),
% 3.10/0.96      inference(predicate_to_equality,[status(thm)],[c_3575]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_3641,plain,
% 3.10/0.96      ( m1_pre_topc(sK1(sK3,sK4),sK3) = iProver_top
% 3.10/0.96      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.10/0.96      | v2_struct_0(sK3) = iProver_top
% 3.10/0.96      | l1_pre_topc(sK3) != iProver_top
% 3.10/0.96      | v1_xboole_0(sK4) = iProver_top ),
% 3.10/0.96      inference(instantiation,[status(thm)],[c_3639]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_5395,plain,
% 3.10/0.96      ( m1_pre_topc(sK1(sK3,sK4),sK3) = iProver_top ),
% 3.10/0.96      inference(global_propositional_subsumption,
% 3.10/0.96                [status(thm)],
% 3.10/0.96                [c_5128,c_31,c_34,c_35,c_36,c_3641]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_15,plain,
% 3.10/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.10/0.96      | v2_struct_0(X1)
% 3.10/0.96      | ~ l1_pre_topc(X1)
% 3.10/0.96      | v1_xboole_0(X0)
% 3.10/0.96      | u1_struct_0(sK1(X1,X0)) = X0 ),
% 3.10/0.96      inference(cnf_transformation,[],[f75]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_3576,plain,
% 3.10/0.96      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49)))
% 3.10/0.96      | v2_struct_0(X0_49)
% 3.10/0.96      | ~ l1_pre_topc(X0_49)
% 3.10/0.96      | v1_xboole_0(X0_50)
% 3.10/0.96      | u1_struct_0(sK1(X0_49,X0_50)) = X0_50 ),
% 3.10/0.96      inference(subtyping,[status(esa)],[c_15]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_4317,plain,
% 3.10/0.96      ( u1_struct_0(sK1(X0_49,X0_50)) = X0_50
% 3.10/0.96      | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49))) != iProver_top
% 3.10/0.96      | v2_struct_0(X0_49) = iProver_top
% 3.10/0.96      | l1_pre_topc(X0_49) != iProver_top
% 3.10/0.96      | v1_xboole_0(X0_50) = iProver_top ),
% 3.10/0.96      inference(predicate_to_equality,[status(thm)],[c_3576]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_5031,plain,
% 3.10/0.96      ( u1_struct_0(sK1(sK3,sK4)) = sK4
% 3.10/0.96      | v2_struct_0(sK3) = iProver_top
% 3.10/0.96      | l1_pre_topc(sK3) != iProver_top
% 3.10/0.96      | v1_xboole_0(sK4) = iProver_top ),
% 3.10/0.96      inference(superposition,[status(thm)],[c_4327,c_4317]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_3637,plain,
% 3.10/0.96      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.10/0.96      | v2_struct_0(sK3)
% 3.10/0.96      | ~ l1_pre_topc(sK3)
% 3.10/0.96      | v1_xboole_0(sK4)
% 3.10/0.96      | u1_struct_0(sK1(sK3,sK4)) = sK4 ),
% 3.10/0.96      inference(instantiation,[status(thm)],[c_3576]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_5242,plain,
% 3.10/0.96      ( u1_struct_0(sK1(sK3,sK4)) = sK4 ),
% 3.10/0.96      inference(global_propositional_subsumption,
% 3.10/0.96                [status(thm)],
% 3.10/0.96                [c_5031,c_30,c_27,c_26,c_25,c_3637]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_4,plain,
% 3.10/0.96      ( ~ m1_pre_topc(X0,X1)
% 3.10/0.96      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.10/0.96      | m1_subset_1(X2,u1_struct_0(X1))
% 3.10/0.96      | v2_struct_0(X1)
% 3.10/0.96      | v2_struct_0(X0)
% 3.10/0.96      | ~ l1_pre_topc(X1) ),
% 3.10/0.96      inference(cnf_transformation,[],[f62]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_3583,plain,
% 3.10/0.96      ( ~ m1_pre_topc(X0_49,X1_49)
% 3.10/0.96      | ~ m1_subset_1(X0_50,u1_struct_0(X0_49))
% 3.10/0.96      | m1_subset_1(X0_50,u1_struct_0(X1_49))
% 3.10/0.96      | v2_struct_0(X1_49)
% 3.10/0.96      | v2_struct_0(X0_49)
% 3.10/0.96      | ~ l1_pre_topc(X1_49) ),
% 3.10/0.96      inference(subtyping,[status(esa)],[c_4]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_4310,plain,
% 3.10/0.96      ( m1_pre_topc(X0_49,X1_49) != iProver_top
% 3.10/0.96      | m1_subset_1(X0_50,u1_struct_0(X0_49)) != iProver_top
% 3.10/0.96      | m1_subset_1(X0_50,u1_struct_0(X1_49)) = iProver_top
% 3.10/0.96      | v2_struct_0(X0_49) = iProver_top
% 3.10/0.96      | v2_struct_0(X1_49) = iProver_top
% 3.10/0.96      | l1_pre_topc(X1_49) != iProver_top ),
% 3.10/0.96      inference(predicate_to_equality,[status(thm)],[c_3583]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_5249,plain,
% 3.10/0.96      ( m1_pre_topc(sK1(sK3,sK4),X0_49) != iProver_top
% 3.10/0.96      | m1_subset_1(X0_50,u1_struct_0(X0_49)) = iProver_top
% 3.10/0.96      | m1_subset_1(X0_50,sK4) != iProver_top
% 3.10/0.96      | v2_struct_0(X0_49) = iProver_top
% 3.10/0.96      | v2_struct_0(sK1(sK3,sK4)) = iProver_top
% 3.10/0.96      | l1_pre_topc(X0_49) != iProver_top ),
% 3.10/0.96      inference(superposition,[status(thm)],[c_5242,c_4310]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_17,plain,
% 3.10/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.10/0.96      | v2_struct_0(X1)
% 3.10/0.96      | ~ v2_struct_0(sK1(X1,X0))
% 3.10/0.96      | ~ l1_pre_topc(X1)
% 3.10/0.96      | v1_xboole_0(X0) ),
% 3.10/0.96      inference(cnf_transformation,[],[f73]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_3574,plain,
% 3.10/0.96      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49)))
% 3.10/0.96      | v2_struct_0(X0_49)
% 3.10/0.96      | ~ v2_struct_0(sK1(X0_49,X0_50))
% 3.10/0.96      | ~ l1_pre_topc(X0_49)
% 3.10/0.96      | v1_xboole_0(X0_50) ),
% 3.10/0.96      inference(subtyping,[status(esa)],[c_17]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_3642,plain,
% 3.10/0.96      ( m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49))) != iProver_top
% 3.10/0.96      | v2_struct_0(X0_49) = iProver_top
% 3.10/0.96      | v2_struct_0(sK1(X0_49,X0_50)) != iProver_top
% 3.10/0.96      | l1_pre_topc(X0_49) != iProver_top
% 3.10/0.96      | v1_xboole_0(X0_50) = iProver_top ),
% 3.10/0.96      inference(predicate_to_equality,[status(thm)],[c_3574]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_3644,plain,
% 3.10/0.96      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.10/0.96      | v2_struct_0(sK1(sK3,sK4)) != iProver_top
% 3.10/0.96      | v2_struct_0(sK3) = iProver_top
% 3.10/0.96      | l1_pre_topc(sK3) != iProver_top
% 3.10/0.96      | v1_xboole_0(sK4) = iProver_top ),
% 3.10/0.96      inference(instantiation,[status(thm)],[c_3642]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_6715,plain,
% 3.10/0.96      ( v2_struct_0(X0_49) = iProver_top
% 3.10/0.96      | m1_subset_1(X0_50,sK4) != iProver_top
% 3.10/0.96      | m1_subset_1(X0_50,u1_struct_0(X0_49)) = iProver_top
% 3.10/0.96      | m1_pre_topc(sK1(sK3,sK4),X0_49) != iProver_top
% 3.10/0.96      | l1_pre_topc(X0_49) != iProver_top ),
% 3.10/0.96      inference(global_propositional_subsumption,
% 3.10/0.96                [status(thm)],
% 3.10/0.96                [c_5249,c_31,c_34,c_35,c_36,c_3644]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_6716,plain,
% 3.10/0.96      ( m1_pre_topc(sK1(sK3,sK4),X0_49) != iProver_top
% 3.10/0.96      | m1_subset_1(X0_50,u1_struct_0(X0_49)) = iProver_top
% 3.10/0.96      | m1_subset_1(X0_50,sK4) != iProver_top
% 3.10/0.96      | v2_struct_0(X0_49) = iProver_top
% 3.10/0.96      | l1_pre_topc(X0_49) != iProver_top ),
% 3.10/0.96      inference(renaming,[status(thm)],[c_6715]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_6726,plain,
% 3.10/0.96      ( m1_subset_1(X0_50,u1_struct_0(sK3)) = iProver_top
% 3.10/0.96      | m1_subset_1(X0_50,sK4) != iProver_top
% 3.10/0.96      | v2_struct_0(sK3) = iProver_top
% 3.10/0.96      | l1_pre_topc(sK3) != iProver_top ),
% 3.10/0.96      inference(superposition,[status(thm)],[c_5395,c_6716]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_6803,plain,
% 3.10/0.96      ( m1_subset_1(X0_50,u1_struct_0(sK3)) = iProver_top
% 3.10/0.96      | m1_subset_1(X0_50,sK4) != iProver_top ),
% 3.10/0.96      inference(global_propositional_subsumption,
% 3.10/0.96                [status(thm)],
% 3.10/0.96                [c_6726,c_31,c_34]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_5,plain,
% 3.10/0.96      ( ~ m1_subset_1(X0,X1)
% 3.10/0.96      | v1_xboole_0(X1)
% 3.10/0.96      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 3.10/0.96      inference(cnf_transformation,[],[f63]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_3582,plain,
% 3.10/0.96      ( ~ m1_subset_1(X0_50,X1_50)
% 3.10/0.96      | v1_xboole_0(X1_50)
% 3.10/0.96      | k6_domain_1(X1_50,X0_50) = k1_tarski(X0_50) ),
% 3.10/0.96      inference(subtyping,[status(esa)],[c_5]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_4311,plain,
% 3.10/0.96      ( k6_domain_1(X0_50,X1_50) = k1_tarski(X1_50)
% 3.10/0.96      | m1_subset_1(X1_50,X0_50) != iProver_top
% 3.10/0.96      | v1_xboole_0(X0_50) = iProver_top ),
% 3.10/0.96      inference(predicate_to_equality,[status(thm)],[c_3582]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_6812,plain,
% 3.10/0.96      ( k6_domain_1(u1_struct_0(sK3),X0_50) = k1_tarski(X0_50)
% 3.10/0.96      | m1_subset_1(X0_50,sK4) != iProver_top
% 3.10/0.96      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.10/0.96      inference(superposition,[status(thm)],[c_6803,c_4311]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_0,plain,
% 3.10/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.10/0.96      | ~ v1_xboole_0(X1)
% 3.10/0.96      | v1_xboole_0(X0) ),
% 3.10/0.96      inference(cnf_transformation,[],[f58]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_3585,plain,
% 3.10/0.96      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
% 3.10/0.96      | ~ v1_xboole_0(X1_50)
% 3.10/0.96      | v1_xboole_0(X0_50) ),
% 3.10/0.96      inference(subtyping,[status(esa)],[c_0]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_4308,plain,
% 3.10/0.96      ( m1_subset_1(X0_50,k1_zfmisc_1(X1_50)) != iProver_top
% 3.10/0.96      | v1_xboole_0(X1_50) != iProver_top
% 3.10/0.96      | v1_xboole_0(X0_50) = iProver_top ),
% 3.10/0.96      inference(predicate_to_equality,[status(thm)],[c_3585]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_4700,plain,
% 3.10/0.96      ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top
% 3.10/0.96      | v1_xboole_0(sK4) = iProver_top ),
% 3.10/0.96      inference(superposition,[status(thm)],[c_4327,c_4308]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_7190,plain,
% 3.10/0.96      ( m1_subset_1(X0_50,sK4) != iProver_top
% 3.10/0.96      | k6_domain_1(u1_struct_0(sK3),X0_50) = k1_tarski(X0_50) ),
% 3.10/0.96      inference(global_propositional_subsumption,
% 3.10/0.96                [status(thm)],
% 3.10/0.96                [c_6812,c_35,c_4700]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_7191,plain,
% 3.10/0.96      ( k6_domain_1(u1_struct_0(sK3),X0_50) = k1_tarski(X0_50)
% 3.10/0.96      | m1_subset_1(X0_50,sK4) != iProver_top ),
% 3.10/0.96      inference(renaming,[status(thm)],[c_7190]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_7198,plain,
% 3.10/0.96      ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k1_tarski(sK0(sK4))
% 3.10/0.96      | v1_zfmisc_1(sK4) != iProver_top
% 3.10/0.96      | v1_xboole_0(sK4) = iProver_top ),
% 3.10/0.96      inference(superposition,[status(thm)],[c_4316,c_7191]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_28,negated_conjecture,
% 3.10/0.96      ( v2_tdlat_3(sK3) ),
% 3.10/0.96      inference(cnf_transformation,[],[f83]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_24,negated_conjecture,
% 3.10/0.96      ( v2_tex_2(sK4,sK3) | v1_zfmisc_1(sK4) ),
% 3.10/0.96      inference(cnf_transformation,[],[f87]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_21,plain,
% 3.10/0.96      ( ~ v2_tex_2(X0,X1)
% 3.10/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.10/0.96      | ~ v2_pre_topc(X1)
% 3.10/0.96      | v2_struct_0(X1)
% 3.10/0.96      | ~ v2_struct_0(sK2(X1,X0))
% 3.10/0.96      | ~ l1_pre_topc(X1)
% 3.10/0.96      | v1_xboole_0(X0) ),
% 3.10/0.96      inference(cnf_transformation,[],[f76]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_223,plain,
% 3.10/0.96      ( v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3) ),
% 3.10/0.96      inference(prop_impl,[status(thm)],[c_24]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_224,plain,
% 3.10/0.96      ( v2_tex_2(sK4,sK3) | v1_zfmisc_1(sK4) ),
% 3.10/0.96      inference(renaming,[status(thm)],[c_223]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_1025,plain,
% 3.10/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.10/0.96      | ~ v2_pre_topc(X1)
% 3.10/0.96      | v2_struct_0(X1)
% 3.10/0.96      | ~ v2_struct_0(sK2(X1,X0))
% 3.10/0.96      | v1_zfmisc_1(sK4)
% 3.10/0.96      | ~ l1_pre_topc(X1)
% 3.10/0.96      | v1_xboole_0(X0)
% 3.10/0.96      | sK3 != X1
% 3.10/0.96      | sK4 != X0 ),
% 3.10/0.96      inference(resolution_lifted,[status(thm)],[c_21,c_224]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_1026,plain,
% 3.10/0.96      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.10/0.96      | ~ v2_pre_topc(sK3)
% 3.10/0.96      | ~ v2_struct_0(sK2(sK3,sK4))
% 3.10/0.96      | v2_struct_0(sK3)
% 3.10/0.96      | v1_zfmisc_1(sK4)
% 3.10/0.96      | ~ l1_pre_topc(sK3)
% 3.10/0.96      | v1_xboole_0(sK4) ),
% 3.10/0.96      inference(unflattening,[status(thm)],[c_1025]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_29,negated_conjecture,
% 3.10/0.96      ( v2_pre_topc(sK3) ),
% 3.10/0.96      inference(cnf_transformation,[],[f82]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_1028,plain,
% 3.10/0.96      ( ~ v2_struct_0(sK2(sK3,sK4)) | v1_zfmisc_1(sK4) ),
% 3.10/0.96      inference(global_propositional_subsumption,
% 3.10/0.96                [status(thm)],
% 3.10/0.96                [c_1026,c_30,c_29,c_27,c_26,c_25]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_20,plain,
% 3.10/0.96      ( ~ v2_tex_2(X0,X1)
% 3.10/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.10/0.96      | v1_tdlat_3(sK2(X1,X0))
% 3.10/0.96      | ~ v2_pre_topc(X1)
% 3.10/0.96      | v2_struct_0(X1)
% 3.10/0.96      | ~ l1_pre_topc(X1)
% 3.10/0.96      | v1_xboole_0(X0) ),
% 3.10/0.96      inference(cnf_transformation,[],[f77]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_1039,plain,
% 3.10/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.10/0.96      | v1_tdlat_3(sK2(X1,X0))
% 3.10/0.96      | ~ v2_pre_topc(X1)
% 3.10/0.96      | v2_struct_0(X1)
% 3.10/0.96      | v1_zfmisc_1(sK4)
% 3.10/0.96      | ~ l1_pre_topc(X1)
% 3.10/0.96      | v1_xboole_0(X0)
% 3.10/0.96      | sK3 != X1
% 3.10/0.96      | sK4 != X0 ),
% 3.10/0.96      inference(resolution_lifted,[status(thm)],[c_20,c_224]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_1040,plain,
% 3.10/0.96      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.10/0.96      | v1_tdlat_3(sK2(sK3,sK4))
% 3.10/0.96      | ~ v2_pre_topc(sK3)
% 3.10/0.96      | v2_struct_0(sK3)
% 3.10/0.96      | v1_zfmisc_1(sK4)
% 3.10/0.96      | ~ l1_pre_topc(sK3)
% 3.10/0.96      | v1_xboole_0(sK4) ),
% 3.10/0.96      inference(unflattening,[status(thm)],[c_1039]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_1042,plain,
% 3.10/0.96      ( v1_tdlat_3(sK2(sK3,sK4)) | v1_zfmisc_1(sK4) ),
% 3.10/0.96      inference(global_propositional_subsumption,
% 3.10/0.96                [status(thm)],
% 3.10/0.96                [c_1040,c_30,c_29,c_27,c_26,c_25]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_3588,plain,( X0_50 = X0_50 ),theory(equality) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_3618,plain,
% 3.10/0.96      ( sK4 = sK4 ),
% 3.10/0.96      inference(instantiation,[status(thm)],[c_3588]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_9,plain,
% 3.10/0.96      ( ~ v2_tdlat_3(X0)
% 3.10/0.96      | ~ v1_tdlat_3(X0)
% 3.10/0.96      | ~ v2_pre_topc(X0)
% 3.10/0.96      | v2_struct_0(X0)
% 3.10/0.96      | v7_struct_0(X0)
% 3.10/0.96      | ~ l1_pre_topc(X0) ),
% 3.10/0.96      inference(cnf_transformation,[],[f67]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_7,plain,
% 3.10/0.96      ( ~ v2_tdlat_3(X0) | v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 3.10/0.96      inference(cnf_transformation,[],[f65]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_175,plain,
% 3.10/0.96      ( ~ v1_tdlat_3(X0)
% 3.10/0.96      | ~ v2_tdlat_3(X0)
% 3.10/0.96      | v2_struct_0(X0)
% 3.10/0.96      | v7_struct_0(X0)
% 3.10/0.96      | ~ l1_pre_topc(X0) ),
% 3.10/0.96      inference(global_propositional_subsumption,[status(thm)],[c_9,c_7]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_176,plain,
% 3.10/0.96      ( ~ v2_tdlat_3(X0)
% 3.10/0.96      | ~ v1_tdlat_3(X0)
% 3.10/0.96      | v2_struct_0(X0)
% 3.10/0.96      | v7_struct_0(X0)
% 3.10/0.96      | ~ l1_pre_topc(X0) ),
% 3.10/0.96      inference(renaming,[status(thm)],[c_175]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_1,plain,
% 3.10/0.96      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.10/0.96      inference(cnf_transformation,[],[f59]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_3,plain,
% 3.10/0.96      ( ~ v7_struct_0(X0) | v1_zfmisc_1(u1_struct_0(X0)) | ~ l1_struct_0(X0) ),
% 3.10/0.96      inference(cnf_transformation,[],[f61]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_383,plain,
% 3.10/0.96      ( ~ v7_struct_0(X0) | v1_zfmisc_1(u1_struct_0(X0)) | ~ l1_pre_topc(X0) ),
% 3.10/0.96      inference(resolution,[status(thm)],[c_1,c_3]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_401,plain,
% 3.10/0.96      ( ~ v2_tdlat_3(X0)
% 3.10/0.96      | ~ v1_tdlat_3(X0)
% 3.10/0.96      | v2_struct_0(X0)
% 3.10/0.96      | v1_zfmisc_1(u1_struct_0(X0))
% 3.10/0.96      | ~ l1_pre_topc(X0) ),
% 3.10/0.96      inference(resolution,[status(thm)],[c_176,c_383]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_3560,plain,
% 3.10/0.96      ( ~ v2_tdlat_3(X0_49)
% 3.10/0.96      | ~ v1_tdlat_3(X0_49)
% 3.10/0.96      | v2_struct_0(X0_49)
% 3.10/0.96      | v1_zfmisc_1(u1_struct_0(X0_49))
% 3.10/0.96      | ~ l1_pre_topc(X0_49) ),
% 3.10/0.96      inference(subtyping,[status(esa)],[c_401]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_4711,plain,
% 3.10/0.96      ( ~ v2_tdlat_3(sK2(X0_49,X0_50))
% 3.10/0.96      | ~ v1_tdlat_3(sK2(X0_49,X0_50))
% 3.10/0.96      | v2_struct_0(sK2(X0_49,X0_50))
% 3.10/0.96      | v1_zfmisc_1(u1_struct_0(sK2(X0_49,X0_50)))
% 3.10/0.96      | ~ l1_pre_topc(sK2(X0_49,X0_50)) ),
% 3.10/0.96      inference(instantiation,[status(thm)],[c_3560]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_4713,plain,
% 3.10/0.96      ( ~ v2_tdlat_3(sK2(sK3,sK4))
% 3.10/0.96      | ~ v1_tdlat_3(sK2(sK3,sK4))
% 3.10/0.96      | v2_struct_0(sK2(sK3,sK4))
% 3.10/0.96      | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
% 3.10/0.96      | ~ l1_pre_topc(sK2(sK3,sK4)) ),
% 3.10/0.96      inference(instantiation,[status(thm)],[c_4711]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_3567,negated_conjecture,
% 3.10/0.96      ( v2_tex_2(sK4,sK3) | v1_zfmisc_1(sK4) ),
% 3.10/0.96      inference(subtyping,[status(esa)],[c_24]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_4326,plain,
% 3.10/0.96      ( v2_tex_2(sK4,sK3) = iProver_top | v1_zfmisc_1(sK4) = iProver_top ),
% 3.10/0.96      inference(predicate_to_equality,[status(thm)],[c_3567]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_18,plain,
% 3.10/0.96      ( ~ v2_tex_2(X0,X1)
% 3.10/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.10/0.96      | ~ v2_pre_topc(X1)
% 3.10/0.96      | v2_struct_0(X1)
% 3.10/0.96      | ~ l1_pre_topc(X1)
% 3.10/0.96      | v1_xboole_0(X0)
% 3.10/0.96      | u1_struct_0(sK2(X1,X0)) = X0 ),
% 3.10/0.96      inference(cnf_transformation,[],[f79]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_3573,plain,
% 3.10/0.96      ( ~ v2_tex_2(X0_50,X0_49)
% 3.10/0.96      | ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49)))
% 3.10/0.96      | ~ v2_pre_topc(X0_49)
% 3.10/0.96      | v2_struct_0(X0_49)
% 3.10/0.96      | ~ l1_pre_topc(X0_49)
% 3.10/0.96      | v1_xboole_0(X0_50)
% 3.10/0.96      | u1_struct_0(sK2(X0_49,X0_50)) = X0_50 ),
% 3.10/0.96      inference(subtyping,[status(esa)],[c_18]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_4320,plain,
% 3.10/0.96      ( u1_struct_0(sK2(X0_49,X0_50)) = X0_50
% 3.10/0.96      | v2_tex_2(X0_50,X0_49) != iProver_top
% 3.10/0.96      | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49))) != iProver_top
% 3.10/0.96      | v2_pre_topc(X0_49) != iProver_top
% 3.10/0.96      | v2_struct_0(X0_49) = iProver_top
% 3.10/0.96      | l1_pre_topc(X0_49) != iProver_top
% 3.10/0.96      | v1_xboole_0(X0_50) = iProver_top ),
% 3.10/0.96      inference(predicate_to_equality,[status(thm)],[c_3573]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_5632,plain,
% 3.10/0.96      ( u1_struct_0(sK2(sK3,sK4)) = sK4
% 3.10/0.96      | v2_tex_2(sK4,sK3) != iProver_top
% 3.10/0.96      | v2_pre_topc(sK3) != iProver_top
% 3.10/0.96      | v2_struct_0(sK3) = iProver_top
% 3.10/0.96      | l1_pre_topc(sK3) != iProver_top
% 3.10/0.96      | v1_xboole_0(sK4) = iProver_top ),
% 3.10/0.96      inference(superposition,[status(thm)],[c_4327,c_4320]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_32,plain,
% 3.10/0.96      ( v2_pre_topc(sK3) = iProver_top ),
% 3.10/0.96      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_6061,plain,
% 3.10/0.96      ( u1_struct_0(sK2(sK3,sK4)) = sK4 | v2_tex_2(sK4,sK3) != iProver_top ),
% 3.10/0.96      inference(global_propositional_subsumption,
% 3.10/0.96                [status(thm)],
% 3.10/0.96                [c_5632,c_31,c_32,c_34,c_35]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_6067,plain,
% 3.10/0.96      ( u1_struct_0(sK2(sK3,sK4)) = sK4 | v1_zfmisc_1(sK4) = iProver_top ),
% 3.10/0.96      inference(superposition,[status(thm)],[c_4326,c_6061]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_6068,plain,
% 3.10/0.96      ( v1_zfmisc_1(sK4) | u1_struct_0(sK2(sK3,sK4)) = sK4 ),
% 3.10/0.96      inference(predicate_to_equality_rev,[status(thm)],[c_6067]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_19,plain,
% 3.10/0.96      ( ~ v2_tex_2(X0,X1)
% 3.10/0.96      | m1_pre_topc(sK2(X1,X0),X1)
% 3.10/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.10/0.96      | ~ v2_pre_topc(X1)
% 3.10/0.96      | v2_struct_0(X1)
% 3.10/0.96      | ~ l1_pre_topc(X1)
% 3.10/0.96      | v1_xboole_0(X0) ),
% 3.10/0.96      inference(cnf_transformation,[],[f78]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_3572,plain,
% 3.10/0.96      ( ~ v2_tex_2(X0_50,X0_49)
% 3.10/0.96      | m1_pre_topc(sK2(X0_49,X0_50),X0_49)
% 3.10/0.96      | ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49)))
% 3.10/0.96      | ~ v2_pre_topc(X0_49)
% 3.10/0.96      | v2_struct_0(X0_49)
% 3.10/0.96      | ~ l1_pre_topc(X0_49)
% 3.10/0.96      | v1_xboole_0(X0_50) ),
% 3.10/0.96      inference(subtyping,[status(esa)],[c_19]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_4321,plain,
% 3.10/0.96      ( v2_tex_2(X0_50,X0_49) != iProver_top
% 3.10/0.96      | m1_pre_topc(sK2(X0_49,X0_50),X0_49) = iProver_top
% 3.10/0.96      | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49))) != iProver_top
% 3.10/0.96      | v2_pre_topc(X0_49) != iProver_top
% 3.10/0.96      | v2_struct_0(X0_49) = iProver_top
% 3.10/0.96      | l1_pre_topc(X0_49) != iProver_top
% 3.10/0.96      | v1_xboole_0(X0_50) = iProver_top ),
% 3.10/0.96      inference(predicate_to_equality,[status(thm)],[c_3572]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_5825,plain,
% 3.10/0.96      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.10/0.96      | m1_pre_topc(sK2(sK3,sK4),sK3) = iProver_top
% 3.10/0.96      | v2_pre_topc(sK3) != iProver_top
% 3.10/0.96      | v2_struct_0(sK3) = iProver_top
% 3.10/0.96      | l1_pre_topc(sK3) != iProver_top
% 3.10/0.96      | v1_xboole_0(sK4) = iProver_top ),
% 3.10/0.96      inference(superposition,[status(thm)],[c_4327,c_4321]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_6203,plain,
% 3.10/0.96      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.10/0.96      | m1_pre_topc(sK2(sK3,sK4),sK3) = iProver_top ),
% 3.10/0.96      inference(global_propositional_subsumption,
% 3.10/0.96                [status(thm)],
% 3.10/0.96                [c_5825,c_31,c_32,c_34,c_35]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_2,plain,
% 3.10/0.96      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.10/0.96      inference(cnf_transformation,[],[f60]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_3584,plain,
% 3.10/0.96      ( ~ m1_pre_topc(X0_49,X1_49)
% 3.10/0.96      | ~ l1_pre_topc(X1_49)
% 3.10/0.96      | l1_pre_topc(X0_49) ),
% 3.10/0.96      inference(subtyping,[status(esa)],[c_2]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_4309,plain,
% 3.10/0.96      ( m1_pre_topc(X0_49,X1_49) != iProver_top
% 3.10/0.96      | l1_pre_topc(X1_49) != iProver_top
% 3.10/0.96      | l1_pre_topc(X0_49) = iProver_top ),
% 3.10/0.96      inference(predicate_to_equality,[status(thm)],[c_3584]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_6209,plain,
% 3.10/0.96      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.10/0.96      | l1_pre_topc(sK2(sK3,sK4)) = iProver_top
% 3.10/0.96      | l1_pre_topc(sK3) != iProver_top ),
% 3.10/0.96      inference(superposition,[status(thm)],[c_6203,c_4309]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_6210,plain,
% 3.10/0.96      ( ~ v2_tex_2(sK4,sK3) | l1_pre_topc(sK2(sK3,sK4)) | ~ l1_pre_topc(sK3) ),
% 3.10/0.96      inference(predicate_to_equality_rev,[status(thm)],[c_6209]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_3589,plain,
% 3.10/0.96      ( X0_50 != X1_50 | X2_50 != X1_50 | X2_50 = X0_50 ),
% 3.10/0.96      theory(equality) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_5735,plain,
% 3.10/0.96      ( X0_50 != X1_50
% 3.10/0.96      | X0_50 = u1_struct_0(X0_49)
% 3.10/0.96      | u1_struct_0(X0_49) != X1_50 ),
% 3.10/0.96      inference(instantiation,[status(thm)],[c_3589]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_6514,plain,
% 3.10/0.96      ( X0_50 != X1_50
% 3.10/0.96      | X0_50 = u1_struct_0(sK2(X0_49,X1_50))
% 3.10/0.96      | u1_struct_0(sK2(X0_49,X1_50)) != X1_50 ),
% 3.10/0.96      inference(instantiation,[status(thm)],[c_5735]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_6515,plain,
% 3.10/0.96      ( u1_struct_0(sK2(sK3,sK4)) != sK4
% 3.10/0.96      | sK4 = u1_struct_0(sK2(sK3,sK4))
% 3.10/0.96      | sK4 != sK4 ),
% 3.10/0.96      inference(instantiation,[status(thm)],[c_6514]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_3596,plain,
% 3.10/0.96      ( ~ v1_zfmisc_1(X0_50) | v1_zfmisc_1(X1_50) | X1_50 != X0_50 ),
% 3.10/0.96      theory(equality) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_6753,plain,
% 3.10/0.96      ( v1_zfmisc_1(X0_50)
% 3.10/0.96      | ~ v1_zfmisc_1(u1_struct_0(sK2(X0_49,X1_50)))
% 3.10/0.96      | X0_50 != u1_struct_0(sK2(X0_49,X1_50)) ),
% 3.10/0.96      inference(instantiation,[status(thm)],[c_3596]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_6756,plain,
% 3.10/0.96      ( ~ v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4)))
% 3.10/0.96      | v1_zfmisc_1(sK4)
% 3.10/0.96      | sK4 != u1_struct_0(sK2(sK3,sK4)) ),
% 3.10/0.96      inference(instantiation,[status(thm)],[c_6753]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_11,plain,
% 3.10/0.96      ( ~ m1_pre_topc(X0,X1)
% 3.10/0.96      | ~ v2_tdlat_3(X1)
% 3.10/0.96      | v2_tdlat_3(X0)
% 3.10/0.96      | ~ v2_pre_topc(X1)
% 3.10/0.96      | v2_struct_0(X1)
% 3.10/0.96      | ~ l1_pre_topc(X1) ),
% 3.10/0.96      inference(cnf_transformation,[],[f69]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_1397,plain,
% 3.10/0.96      ( ~ m1_pre_topc(X0,X1)
% 3.10/0.96      | ~ v2_tdlat_3(X1)
% 3.10/0.96      | ~ v2_tdlat_3(X2)
% 3.10/0.96      | v2_tdlat_3(X0)
% 3.10/0.96      | v2_struct_0(X1)
% 3.10/0.96      | ~ l1_pre_topc(X1)
% 3.10/0.96      | ~ l1_pre_topc(X2)
% 3.10/0.96      | X2 != X1 ),
% 3.10/0.96      inference(resolution_lifted,[status(thm)],[c_11,c_7]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_1398,plain,
% 3.10/0.96      ( ~ m1_pre_topc(X0,X1)
% 3.10/0.96      | ~ v2_tdlat_3(X1)
% 3.10/0.96      | v2_tdlat_3(X0)
% 3.10/0.96      | v2_struct_0(X1)
% 3.10/0.96      | ~ l1_pre_topc(X1) ),
% 3.10/0.96      inference(unflattening,[status(thm)],[c_1397]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_3559,plain,
% 3.10/0.96      ( ~ m1_pre_topc(X0_49,X1_49)
% 3.10/0.96      | ~ v2_tdlat_3(X1_49)
% 3.10/0.96      | v2_tdlat_3(X0_49)
% 3.10/0.96      | v2_struct_0(X1_49)
% 3.10/0.96      | ~ l1_pre_topc(X1_49) ),
% 3.10/0.96      inference(subtyping,[status(esa)],[c_1398]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_4334,plain,
% 3.10/0.96      ( m1_pre_topc(X0_49,X1_49) != iProver_top
% 3.10/0.96      | v2_tdlat_3(X1_49) != iProver_top
% 3.10/0.96      | v2_tdlat_3(X0_49) = iProver_top
% 3.10/0.96      | v2_struct_0(X1_49) = iProver_top
% 3.10/0.96      | l1_pre_topc(X1_49) != iProver_top ),
% 3.10/0.96      inference(predicate_to_equality,[status(thm)],[c_3559]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_7057,plain,
% 3.10/0.96      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.10/0.96      | v2_tdlat_3(sK2(sK3,sK4)) = iProver_top
% 3.10/0.96      | v2_tdlat_3(sK3) != iProver_top
% 3.10/0.96      | v2_struct_0(sK3) = iProver_top
% 3.10/0.96      | l1_pre_topc(sK3) != iProver_top ),
% 3.10/0.96      inference(superposition,[status(thm)],[c_6203,c_4334]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_7107,plain,
% 3.10/0.96      ( ~ v2_tex_2(sK4,sK3)
% 3.10/0.96      | v2_tdlat_3(sK2(sK3,sK4))
% 3.10/0.96      | ~ v2_tdlat_3(sK3)
% 3.10/0.96      | v2_struct_0(sK3)
% 3.10/0.96      | ~ l1_pre_topc(sK3) ),
% 3.10/0.96      inference(predicate_to_equality_rev,[status(thm)],[c_7057]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_7199,plain,
% 3.10/0.96      ( ~ v1_zfmisc_1(sK4)
% 3.10/0.96      | v1_xboole_0(sK4)
% 3.10/0.96      | k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k1_tarski(sK0(sK4)) ),
% 3.10/0.96      inference(predicate_to_equality_rev,[status(thm)],[c_7198]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_7201,plain,
% 3.10/0.96      ( k6_domain_1(u1_struct_0(sK3),sK0(sK4)) = k1_tarski(sK0(sK4)) ),
% 3.10/0.96      inference(global_propositional_subsumption,
% 3.10/0.96                [status(thm)],
% 3.10/0.96                [c_7198,c_31,c_32,c_33,c_34,c_35,c_37,c_38,c_3618,c_4714,
% 3.10/0.96                 c_5918,c_6061,c_6196,c_6209,c_6515,c_6757,c_7057]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_22,plain,
% 3.10/0.96      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 3.10/0.96      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.10/0.96      | ~ v2_pre_topc(X0)
% 3.10/0.96      | v2_struct_0(X0)
% 3.10/0.96      | ~ l1_pre_topc(X0) ),
% 3.10/0.96      inference(cnf_transformation,[],[f80]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_3569,plain,
% 3.10/0.96      ( v2_tex_2(k6_domain_1(u1_struct_0(X0_49),X0_50),X0_49)
% 3.10/0.96      | ~ m1_subset_1(X0_50,u1_struct_0(X0_49))
% 3.10/0.96      | ~ v2_pre_topc(X0_49)
% 3.10/0.96      | v2_struct_0(X0_49)
% 3.10/0.96      | ~ l1_pre_topc(X0_49) ),
% 3.10/0.96      inference(subtyping,[status(esa)],[c_22]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_4324,plain,
% 3.10/0.96      ( v2_tex_2(k6_domain_1(u1_struct_0(X0_49),X0_50),X0_49) = iProver_top
% 3.10/0.96      | m1_subset_1(X0_50,u1_struct_0(X0_49)) != iProver_top
% 3.10/0.96      | v2_pre_topc(X0_49) != iProver_top
% 3.10/0.96      | v2_struct_0(X0_49) = iProver_top
% 3.10/0.96      | l1_pre_topc(X0_49) != iProver_top ),
% 3.10/0.96      inference(predicate_to_equality,[status(thm)],[c_3569]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_7204,plain,
% 3.10/0.96      ( v2_tex_2(k1_tarski(sK0(sK4)),sK3) = iProver_top
% 3.10/0.96      | m1_subset_1(sK0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.10/0.96      | v2_pre_topc(sK3) != iProver_top
% 3.10/0.96      | v2_struct_0(sK3) = iProver_top
% 3.10/0.96      | l1_pre_topc(sK3) != iProver_top ),
% 3.10/0.96      inference(superposition,[status(thm)],[c_7201,c_4324]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_37,plain,
% 3.10/0.96      ( v2_tex_2(sK4,sK3) = iProver_top | v1_zfmisc_1(sK4) = iProver_top ),
% 3.10/0.96      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_33,plain,
% 3.10/0.96      ( v2_tdlat_3(sK3) = iProver_top ),
% 3.10/0.96      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_23,negated_conjecture,
% 3.10/0.96      ( ~ v2_tex_2(sK4,sK3) | ~ v1_zfmisc_1(sK4) ),
% 3.10/0.96      inference(cnf_transformation,[],[f88]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_38,plain,
% 3.10/0.96      ( v2_tex_2(sK4,sK3) != iProver_top | v1_zfmisc_1(sK4) != iProver_top ),
% 3.10/0.96      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_4712,plain,
% 3.10/0.96      ( v2_tdlat_3(sK2(X0_49,X0_50)) != iProver_top
% 3.10/0.96      | v1_tdlat_3(sK2(X0_49,X0_50)) != iProver_top
% 3.10/0.96      | v2_struct_0(sK2(X0_49,X0_50)) = iProver_top
% 3.10/0.96      | v1_zfmisc_1(u1_struct_0(sK2(X0_49,X0_50))) = iProver_top
% 3.10/0.96      | l1_pre_topc(sK2(X0_49,X0_50)) != iProver_top ),
% 3.10/0.96      inference(predicate_to_equality,[status(thm)],[c_4711]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_4714,plain,
% 3.10/0.96      ( v2_tdlat_3(sK2(sK3,sK4)) != iProver_top
% 3.10/0.96      | v1_tdlat_3(sK2(sK3,sK4)) != iProver_top
% 3.10/0.96      | v2_struct_0(sK2(sK3,sK4)) = iProver_top
% 3.10/0.96      | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) = iProver_top
% 3.10/0.96      | l1_pre_topc(sK2(sK3,sK4)) != iProver_top ),
% 3.10/0.96      inference(instantiation,[status(thm)],[c_4712]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_3570,plain,
% 3.10/0.96      ( ~ v2_tex_2(X0_50,X0_49)
% 3.10/0.96      | ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49)))
% 3.10/0.96      | ~ v2_pre_topc(X0_49)
% 3.10/0.96      | v2_struct_0(X0_49)
% 3.10/0.96      | ~ v2_struct_0(sK2(X0_49,X0_50))
% 3.10/0.96      | ~ l1_pre_topc(X0_49)
% 3.10/0.96      | v1_xboole_0(X0_50) ),
% 3.10/0.96      inference(subtyping,[status(esa)],[c_21]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_4323,plain,
% 3.10/0.96      ( v2_tex_2(X0_50,X0_49) != iProver_top
% 3.10/0.96      | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49))) != iProver_top
% 3.10/0.96      | v2_pre_topc(X0_49) != iProver_top
% 3.10/0.96      | v2_struct_0(X0_49) = iProver_top
% 3.10/0.96      | v2_struct_0(sK2(X0_49,X0_50)) != iProver_top
% 3.10/0.96      | l1_pre_topc(X0_49) != iProver_top
% 3.10/0.96      | v1_xboole_0(X0_50) = iProver_top ),
% 3.10/0.96      inference(predicate_to_equality,[status(thm)],[c_3570]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_5918,plain,
% 3.10/0.96      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.10/0.96      | v2_pre_topc(sK3) != iProver_top
% 3.10/0.96      | v2_struct_0(sK2(sK3,sK4)) != iProver_top
% 3.10/0.96      | v2_struct_0(sK3) = iProver_top
% 3.10/0.96      | l1_pre_topc(sK3) != iProver_top
% 3.10/0.96      | v1_xboole_0(sK4) = iProver_top ),
% 3.10/0.96      inference(superposition,[status(thm)],[c_4327,c_4323]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_3571,plain,
% 3.10/0.96      ( ~ v2_tex_2(X0_50,X0_49)
% 3.10/0.96      | ~ m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49)))
% 3.10/0.96      | v1_tdlat_3(sK2(X0_49,X0_50))
% 3.10/0.96      | ~ v2_pre_topc(X0_49)
% 3.10/0.96      | v2_struct_0(X0_49)
% 3.10/0.96      | ~ l1_pre_topc(X0_49)
% 3.10/0.96      | v1_xboole_0(X0_50) ),
% 3.10/0.96      inference(subtyping,[status(esa)],[c_20]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_4322,plain,
% 3.10/0.96      ( v2_tex_2(X0_50,X0_49) != iProver_top
% 3.10/0.96      | m1_subset_1(X0_50,k1_zfmisc_1(u1_struct_0(X0_49))) != iProver_top
% 3.10/0.96      | v1_tdlat_3(sK2(X0_49,X0_50)) = iProver_top
% 3.10/0.96      | v2_pre_topc(X0_49) != iProver_top
% 3.10/0.96      | v2_struct_0(X0_49) = iProver_top
% 3.10/0.96      | l1_pre_topc(X0_49) != iProver_top
% 3.10/0.96      | v1_xboole_0(X0_50) = iProver_top ),
% 3.10/0.96      inference(predicate_to_equality,[status(thm)],[c_3571]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_5765,plain,
% 3.10/0.96      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.10/0.96      | v1_tdlat_3(sK2(sK3,sK4)) = iProver_top
% 3.10/0.96      | v2_pre_topc(sK3) != iProver_top
% 3.10/0.96      | v2_struct_0(sK3) = iProver_top
% 3.10/0.96      | l1_pre_topc(sK3) != iProver_top
% 3.10/0.96      | v1_xboole_0(sK4) = iProver_top ),
% 3.10/0.96      inference(superposition,[status(thm)],[c_4327,c_4322]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_6196,plain,
% 3.10/0.96      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.10/0.96      | v1_tdlat_3(sK2(sK3,sK4)) = iProver_top ),
% 3.10/0.96      inference(global_propositional_subsumption,
% 3.10/0.96                [status(thm)],
% 3.10/0.96                [c_5765,c_31,c_32,c_34,c_35]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_6755,plain,
% 3.10/0.96      ( X0_50 != u1_struct_0(sK2(X0_49,X1_50))
% 3.10/0.96      | v1_zfmisc_1(X0_50) = iProver_top
% 3.10/0.96      | v1_zfmisc_1(u1_struct_0(sK2(X0_49,X1_50))) != iProver_top ),
% 3.10/0.96      inference(predicate_to_equality,[status(thm)],[c_6753]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_6757,plain,
% 3.10/0.96      ( sK4 != u1_struct_0(sK2(sK3,sK4))
% 3.10/0.96      | v1_zfmisc_1(u1_struct_0(sK2(sK3,sK4))) != iProver_top
% 3.10/0.96      | v1_zfmisc_1(sK4) = iProver_top ),
% 3.10/0.96      inference(instantiation,[status(thm)],[c_6755]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_7427,plain,
% 3.10/0.96      ( v2_tex_2(sK4,sK3) != iProver_top ),
% 3.10/0.96      inference(global_propositional_subsumption,
% 3.10/0.96                [status(thm)],
% 3.10/0.96                [c_7057,c_31,c_32,c_33,c_34,c_35,c_38,c_3618,c_4714,c_5918,
% 3.10/0.96                 c_6061,c_6196,c_6209,c_6515,c_6757]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_5023,plain,
% 3.10/0.96      ( m1_pre_topc(X0_49,X1_49) != iProver_top
% 3.10/0.96      | m1_subset_1(sK0(u1_struct_0(X0_49)),u1_struct_0(X1_49)) = iProver_top
% 3.10/0.96      | v2_struct_0(X0_49) = iProver_top
% 3.10/0.96      | v2_struct_0(X1_49) = iProver_top
% 3.10/0.96      | v1_zfmisc_1(u1_struct_0(X0_49)) != iProver_top
% 3.10/0.96      | l1_pre_topc(X1_49) != iProver_top
% 3.10/0.96      | v1_xboole_0(u1_struct_0(X0_49)) = iProver_top ),
% 3.10/0.96      inference(superposition,[status(thm)],[c_4316,c_4310]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_7757,plain,
% 3.10/0.96      ( m1_pre_topc(sK1(sK3,sK4),X0_49) != iProver_top
% 3.10/0.96      | m1_subset_1(sK0(sK4),u1_struct_0(X0_49)) = iProver_top
% 3.10/0.96      | v2_struct_0(X0_49) = iProver_top
% 3.10/0.96      | v2_struct_0(sK1(sK3,sK4)) = iProver_top
% 3.10/0.96      | v1_zfmisc_1(u1_struct_0(sK1(sK3,sK4))) != iProver_top
% 3.10/0.96      | l1_pre_topc(X0_49) != iProver_top
% 3.10/0.96      | v1_xboole_0(u1_struct_0(sK1(sK3,sK4))) = iProver_top ),
% 3.10/0.96      inference(superposition,[status(thm)],[c_5242,c_5023]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_7818,plain,
% 3.10/0.96      ( m1_pre_topc(sK1(sK3,sK4),X0_49) != iProver_top
% 3.10/0.96      | m1_subset_1(sK0(sK4),u1_struct_0(X0_49)) = iProver_top
% 3.10/0.96      | v2_struct_0(X0_49) = iProver_top
% 3.10/0.96      | v2_struct_0(sK1(sK3,sK4)) = iProver_top
% 3.10/0.96      | v1_zfmisc_1(sK4) != iProver_top
% 3.10/0.96      | l1_pre_topc(X0_49) != iProver_top
% 3.10/0.96      | v1_xboole_0(sK4) = iProver_top ),
% 3.10/0.96      inference(light_normalisation,[status(thm)],[c_7757,c_5242]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_7834,plain,
% 3.10/0.96      ( m1_pre_topc(sK1(sK3,sK4),sK3) != iProver_top
% 3.10/0.96      | m1_subset_1(sK0(sK4),u1_struct_0(sK3)) = iProver_top
% 3.10/0.96      | v2_struct_0(sK1(sK3,sK4)) = iProver_top
% 3.10/0.96      | v2_struct_0(sK3) = iProver_top
% 3.10/0.96      | v1_zfmisc_1(sK4) != iProver_top
% 3.10/0.96      | l1_pre_topc(sK3) != iProver_top
% 3.10/0.96      | v1_xboole_0(sK4) = iProver_top ),
% 3.10/0.96      inference(instantiation,[status(thm)],[c_7818]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_7915,plain,
% 3.10/0.96      ( v2_tex_2(k1_tarski(sK0(sK4)),sK3) = iProver_top ),
% 3.10/0.96      inference(global_propositional_subsumption,
% 3.10/0.96                [status(thm)],
% 3.10/0.96                [c_7204,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_3618,
% 3.10/0.96                 c_3641,c_3644,c_4714,c_5918,c_6061,c_6196,c_6209,c_6515,
% 3.10/0.96                 c_6757,c_7057,c_7834]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_7432,plain,
% 3.10/0.96      ( v1_zfmisc_1(sK4) = iProver_top ),
% 3.10/0.96      inference(superposition,[status(thm)],[c_4326,c_7427]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_4917,plain,
% 3.10/0.96      ( k6_domain_1(X0_50,sK0(X0_50)) = k1_tarski(sK0(X0_50))
% 3.10/0.96      | v1_zfmisc_1(X0_50) != iProver_top
% 3.10/0.96      | v1_xboole_0(X0_50) = iProver_top ),
% 3.10/0.96      inference(superposition,[status(thm)],[c_4316,c_4311]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_7561,plain,
% 3.10/0.96      ( k6_domain_1(sK4,sK0(sK4)) = k1_tarski(sK0(sK4))
% 3.10/0.96      | v1_xboole_0(sK4) = iProver_top ),
% 3.10/0.96      inference(superposition,[status(thm)],[c_7432,c_4917]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_4930,plain,
% 3.10/0.96      ( k6_domain_1(sK4,sK0(sK4)) = k1_tarski(sK0(sK4))
% 3.10/0.96      | v1_zfmisc_1(sK4) != iProver_top
% 3.10/0.96      | v1_xboole_0(sK4) = iProver_top ),
% 3.10/0.96      inference(instantiation,[status(thm)],[c_4917]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_7654,plain,
% 3.10/0.96      ( k6_domain_1(sK4,sK0(sK4)) = k1_tarski(sK0(sK4)) ),
% 3.10/0.96      inference(global_propositional_subsumption,
% 3.10/0.96                [status(thm)],
% 3.10/0.96                [c_7561,c_31,c_32,c_33,c_34,c_35,c_37,c_38,c_3618,c_4714,
% 3.10/0.96                 c_4930,c_5918,c_6061,c_6196,c_6209,c_6515,c_6757,c_7057]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_13,plain,
% 3.10/0.96      ( ~ v1_zfmisc_1(X0) | v1_xboole_0(X0) | k6_domain_1(X0,sK0(X0)) = X0 ),
% 3.10/0.96      inference(cnf_transformation,[],[f71]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_3578,plain,
% 3.10/0.96      ( ~ v1_zfmisc_1(X0_50)
% 3.10/0.96      | v1_xboole_0(X0_50)
% 3.10/0.96      | k6_domain_1(X0_50,sK0(X0_50)) = X0_50 ),
% 3.10/0.96      inference(subtyping,[status(esa)],[c_13]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_4315,plain,
% 3.10/0.96      ( k6_domain_1(X0_50,sK0(X0_50)) = X0_50
% 3.10/0.96      | v1_zfmisc_1(X0_50) != iProver_top
% 3.10/0.96      | v1_xboole_0(X0_50) = iProver_top ),
% 3.10/0.96      inference(predicate_to_equality,[status(thm)],[c_3578]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_7562,plain,
% 3.10/0.96      ( k6_domain_1(sK4,sK0(sK4)) = sK4 | v1_xboole_0(sK4) = iProver_top ),
% 3.10/0.96      inference(superposition,[status(thm)],[c_7432,c_4315]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_3630,plain,
% 3.10/0.96      ( k6_domain_1(X0_50,sK0(X0_50)) = X0_50
% 3.10/0.96      | v1_zfmisc_1(X0_50) != iProver_top
% 3.10/0.96      | v1_xboole_0(X0_50) = iProver_top ),
% 3.10/0.96      inference(predicate_to_equality,[status(thm)],[c_3578]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_3632,plain,
% 3.10/0.96      ( k6_domain_1(sK4,sK0(sK4)) = sK4
% 3.10/0.96      | v1_zfmisc_1(sK4) != iProver_top
% 3.10/0.96      | v1_xboole_0(sK4) = iProver_top ),
% 3.10/0.96      inference(instantiation,[status(thm)],[c_3630]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_7574,plain,
% 3.10/0.96      ( k6_domain_1(sK4,sK0(sK4)) = sK4 ),
% 3.10/0.96      inference(global_propositional_subsumption,
% 3.10/0.96                [status(thm)],
% 3.10/0.96                [c_7562,c_31,c_32,c_33,c_34,c_35,c_37,c_38,c_3618,c_3632,
% 3.10/0.96                 c_4714,c_5918,c_6061,c_6196,c_6209,c_6515,c_6757,c_7057]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_7656,plain,
% 3.10/0.96      ( k1_tarski(sK0(sK4)) = sK4 ),
% 3.10/0.96      inference(light_normalisation,[status(thm)],[c_7654,c_7574]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_7919,plain,
% 3.10/0.96      ( v2_tex_2(sK4,sK3) = iProver_top ),
% 3.10/0.96      inference(light_normalisation,[status(thm)],[c_7915,c_7656]) ).
% 3.10/0.96  
% 3.10/0.96  cnf(c_7921,plain,
% 3.10/0.96      ( $false ),
% 3.10/0.96      inference(forward_subsumption_resolution,[status(thm)],[c_7919,c_7427]) ).
% 3.10/0.96  
% 3.10/0.96  
% 3.10/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 3.10/0.96  
% 3.10/0.96  ------                               Statistics
% 3.10/0.96  
% 3.10/0.96  ------ General
% 3.10/0.96  
% 3.10/0.96  abstr_ref_over_cycles:                  0
% 3.10/0.96  abstr_ref_under_cycles:                 0
% 3.10/0.96  gc_basic_clause_elim:                   0
% 3.10/0.96  forced_gc_time:                         0
% 3.10/0.96  parsing_time:                           0.01
% 3.10/0.96  unif_index_cands_time:                  0.
% 3.10/0.96  unif_index_add_time:                    0.
% 3.10/0.96  orderings_time:                         0.
% 3.10/0.96  out_proof_time:                         0.013
% 3.10/0.96  total_time:                             0.196
% 3.10/0.96  num_of_symbols:                         54
% 3.10/0.96  num_of_terms:                           3388
% 3.10/0.96  
% 3.10/0.96  ------ Preprocessing
% 3.10/0.96  
% 3.10/0.96  num_of_splits:                          0
% 3.10/0.96  num_of_split_atoms:                     0
% 3.10/0.96  num_of_reused_defs:                     0
% 3.10/0.96  num_eq_ax_congr_red:                    23
% 3.10/0.96  num_of_sem_filtered_clauses:            1
% 3.10/0.96  num_of_subtypes:                        2
% 3.10/0.96  monotx_restored_types:                  1
% 3.10/0.96  sat_num_of_epr_types:                   0
% 3.10/0.96  sat_num_of_non_cyclic_types:            0
% 3.10/0.96  sat_guarded_non_collapsed_types:        1
% 3.10/0.96  num_pure_diseq_elim:                    0
% 3.10/0.96  simp_replaced_by:                       0
% 3.10/0.96  res_preprocessed:                       143
% 3.10/0.96  prep_upred:                             0
% 3.10/0.96  prep_unflattend:                        130
% 3.10/0.96  smt_new_axioms:                         0
% 3.10/0.96  pred_elim_cands:                        10
% 3.10/0.96  pred_elim:                              2
% 3.10/0.96  pred_elim_cl:                           2
% 3.10/0.96  pred_elim_cycles:                       14
% 3.10/0.96  merged_defs:                            8
% 3.10/0.96  merged_defs_ncl:                        0
% 3.10/0.96  bin_hyper_res:                          8
% 3.10/0.96  prep_cycles:                            4
% 3.10/0.96  pred_elim_time:                         0.045
% 3.10/0.96  splitting_time:                         0.
% 3.10/0.96  sem_filter_time:                        0.
% 3.10/0.96  monotx_time:                            0.001
% 3.10/0.96  subtype_inf_time:                       0.001
% 3.10/0.96  
% 3.10/0.96  ------ Problem properties
% 3.10/0.96  
% 3.10/0.96  clauses:                                27
% 3.10/0.96  conjectures:                            8
% 3.10/0.96  epr:                                    11
% 3.10/0.96  horn:                                   11
% 3.10/0.96  ground:                                 8
% 3.10/0.96  unary:                                  6
% 3.10/0.96  binary:                                 2
% 3.10/0.96  lits:                                   99
% 3.10/0.96  lits_eq:                                5
% 3.10/0.96  fd_pure:                                0
% 3.10/0.96  fd_pseudo:                              0
% 3.10/0.96  fd_cond:                                0
% 3.10/0.96  fd_pseudo_cond:                         0
% 3.10/0.96  ac_symbols:                             0
% 3.10/0.96  
% 3.10/0.96  ------ Propositional Solver
% 3.10/0.96  
% 3.10/0.96  prop_solver_calls:                      29
% 3.10/0.96  prop_fast_solver_calls:                 2214
% 3.10/0.96  smt_solver_calls:                       0
% 3.10/0.96  smt_fast_solver_calls:                  0
% 3.10/0.96  prop_num_of_clauses:                    1455
% 3.10/0.96  prop_preprocess_simplified:             6366
% 3.10/0.96  prop_fo_subsumed:                       176
% 3.10/0.96  prop_solver_time:                       0.
% 3.10/0.96  smt_solver_time:                        0.
% 3.10/0.96  smt_fast_solver_time:                   0.
% 3.10/0.96  prop_fast_solver_time:                  0.
% 3.10/0.96  prop_unsat_core_time:                   0.
% 3.10/0.96  
% 3.10/0.96  ------ QBF
% 3.10/0.96  
% 3.10/0.96  qbf_q_res:                              0
% 3.10/0.96  qbf_num_tautologies:                    0
% 3.10/0.96  qbf_prep_cycles:                        0
% 3.10/0.96  
% 3.10/0.96  ------ BMC1
% 3.10/0.96  
% 3.10/0.96  bmc1_current_bound:                     -1
% 3.10/0.96  bmc1_last_solved_bound:                 -1
% 3.10/0.96  bmc1_unsat_core_size:                   -1
% 3.10/0.96  bmc1_unsat_core_parents_size:           -1
% 3.10/0.96  bmc1_merge_next_fun:                    0
% 3.10/0.96  bmc1_unsat_core_clauses_time:           0.
% 3.10/0.96  
% 3.10/0.96  ------ Instantiation
% 3.10/0.96  
% 3.10/0.96  inst_num_of_clauses:                    371
% 3.10/0.96  inst_num_in_passive:                    61
% 3.10/0.96  inst_num_in_active:                     299
% 3.10/0.96  inst_num_in_unprocessed:                11
% 3.10/0.96  inst_num_of_loops:                      360
% 3.10/0.96  inst_num_of_learning_restarts:          0
% 3.10/0.96  inst_num_moves_active_passive:          55
% 3.10/0.96  inst_lit_activity:                      0
% 3.10/0.96  inst_lit_activity_moves:                0
% 3.10/0.96  inst_num_tautologies:                   0
% 3.10/0.96  inst_num_prop_implied:                  0
% 3.10/0.96  inst_num_existing_simplified:           0
% 3.10/0.96  inst_num_eq_res_simplified:             0
% 3.10/0.96  inst_num_child_elim:                    0
% 3.10/0.96  inst_num_of_dismatching_blockings:      161
% 3.10/0.96  inst_num_of_non_proper_insts:           493
% 3.10/0.96  inst_num_of_duplicates:                 0
% 3.10/0.96  inst_inst_num_from_inst_to_res:         0
% 3.10/0.96  inst_dismatching_checking_time:         0.
% 3.10/0.96  
% 3.10/0.96  ------ Resolution
% 3.10/0.96  
% 3.10/0.96  res_num_of_clauses:                     0
% 3.10/0.96  res_num_in_passive:                     0
% 3.10/0.96  res_num_in_active:                      0
% 3.10/0.96  res_num_of_loops:                       147
% 3.10/0.96  res_forward_subset_subsumed:            61
% 3.10/0.96  res_backward_subset_subsumed:           0
% 3.10/0.96  res_forward_subsumed:                   1
% 3.10/0.96  res_backward_subsumed:                  1
% 3.10/0.96  res_forward_subsumption_resolution:     3
% 3.10/0.96  res_backward_subsumption_resolution:    0
% 3.10/0.96  res_clause_to_clause_subsumption:       161
% 3.10/0.96  res_orphan_elimination:                 0
% 3.10/0.96  res_tautology_del:                      133
% 3.10/0.96  res_num_eq_res_simplified:              0
% 3.10/0.96  res_num_sel_changes:                    0
% 3.10/0.96  res_moves_from_active_to_pass:          0
% 3.10/0.96  
% 3.10/0.96  ------ Superposition
% 3.10/0.96  
% 3.10/0.96  sup_time_total:                         0.
% 3.10/0.96  sup_time_generating:                    0.
% 3.10/0.96  sup_time_sim_full:                      0.
% 3.10/0.96  sup_time_sim_immed:                     0.
% 3.10/0.96  
% 3.10/0.96  sup_num_of_clauses:                     85
% 3.10/0.96  sup_num_in_active:                      61
% 3.10/0.96  sup_num_in_passive:                     24
% 3.10/0.96  sup_num_of_loops:                       71
% 3.10/0.96  sup_fw_superposition:                   39
% 3.10/0.96  sup_bw_superposition:                   39
% 3.10/0.96  sup_immediate_simplified:               8
% 3.10/0.96  sup_given_eliminated:                   0
% 3.10/0.96  comparisons_done:                       0
% 3.10/0.96  comparisons_avoided:                    3
% 3.10/0.96  
% 3.10/0.96  ------ Simplifications
% 3.10/0.96  
% 3.10/0.96  
% 3.10/0.96  sim_fw_subset_subsumed:                 3
% 3.10/0.96  sim_bw_subset_subsumed:                 8
% 3.10/0.96  sim_fw_subsumed:                        2
% 3.10/0.96  sim_bw_subsumed:                        0
% 3.10/0.96  sim_fw_subsumption_res:                 1
% 3.10/0.96  sim_bw_subsumption_res:                 0
% 3.10/0.96  sim_tautology_del:                      1
% 3.10/0.96  sim_eq_tautology_del:                   0
% 3.10/0.96  sim_eq_res_simp:                        0
% 3.10/0.96  sim_fw_demodulated:                     0
% 3.10/0.96  sim_bw_demodulated:                     3
% 3.10/0.96  sim_light_normalised:                   5
% 3.10/0.96  sim_joinable_taut:                      0
% 3.10/0.96  sim_joinable_simp:                      0
% 3.10/0.96  sim_ac_normalised:                      0
% 3.10/0.96  sim_smt_subsumption:                    0
% 3.10/0.96  
%------------------------------------------------------------------------------
