%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:37 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 868 expanded)
%              Number of clauses        :   91 ( 240 expanded)
%              Number of leaves         :   22 ( 178 expanded)
%              Depth                    :   22
%              Number of atoms          :  697 (4386 expanded)
%              Number of equality atoms :  205 ( 427 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v1_subset_1(X2,u1_struct_0(X0))
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f57])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK2(X0,X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
                & u1_struct_0(X1) = sK2(X0,X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f58,f59])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK2(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f62,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f63,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f62])).

fof(f65,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),sK4),u1_struct_0(X0))
          | ~ v1_tex_2(k1_tex_2(X0,sK4),X0) )
        & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),sK4),u1_struct_0(X0))
          | v1_tex_2(k1_tex_2(X0,sK4),X0) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
              | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
            & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
              | v1_tex_2(k1_tex_2(X0,X1),X0) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK3),X1),u1_struct_0(sK3))
            | ~ v1_tex_2(k1_tex_2(sK3,X1),sK3) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),X1),u1_struct_0(sK3))
            | v1_tex_2(k1_tex_2(sK3,X1),sK3) )
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l1_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
      | ~ v1_tex_2(k1_tex_2(sK3,sK4),sK3) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
      | v1_tex_2(k1_tex_2(sK3,sK4),sK3) )
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f63,f65,f64])).

fof(f100,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
    | ~ v1_tex_2(k1_tex_2(sK3,sK4),sK3) ),
    inference(cnf_transformation,[],[f66])).

fof(f97,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f66])).

fof(f98,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f66])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f74,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f54,plain,(
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
    inference(rectify,[],[f53])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK1(X0)) = X0
        & m1_subset_1(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK1(X0)) = X0
            & m1_subset_1(sK1(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f54,f55])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X0)
      | k6_domain_1(X0,X1) != X0
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f99,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
    | v1_tex_2(k1_tex_2(sK3,sK4),sK3) ),
    inference(cnf_transformation,[],[f66])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v7_struct_0(X0)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f96,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f66])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ~ v2_struct_0(X1)
           => ( ~ v1_tex_2(X1,X0)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f47,plain,(
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

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f49])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f51])).

fof(f73,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f77,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f75,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v7_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_pre_topc(k1_tex_2(X1,X0),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_3670,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(k1_tex_2(X1,X0),X1) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_19,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK2(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_3675,plain,
    ( sK2(X0,X1) = u1_struct_0(X1)
    | v1_tex_2(X1,X0) = iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5134,plain,
    ( sK2(X0,k1_tex_2(X0,X1)) = u1_struct_0(k1_tex_2(X0,X1))
    | v1_tex_2(k1_tex_2(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3670,c_3675])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_3682,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_22,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3672,plain,
    ( X0 = X1
    | v1_subset_1(X1,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4565,plain,
    ( k6_domain_1(X0,X1) = X0
    | v1_subset_1(k6_domain_1(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3682,c_3672])).

cnf(c_29,negated_conjecture,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
    | ~ v1_tex_2(k1_tex_2(sK3,sK4),sK3) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_3667,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) != iProver_top
    | v1_tex_2(k1_tex_2(sK3,sK4),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5531,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK4) = u1_struct_0(sK3)
    | v1_tex_2(k1_tex_2(sK3,sK4),sK3) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4565,c_3667])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_35,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_36,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_9,plain,
    ( v7_struct_0(X0)
    | ~ v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_92,plain,
    ( v7_struct_0(X0) = iProver_top
    | v1_zfmisc_1(u1_struct_0(X0)) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_94,plain,
    ( v7_struct_0(sK3) = iProver_top
    | v1_zfmisc_1(u1_struct_0(sK3)) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_92])).

cnf(c_7,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_96,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_98,plain,
    ( l1_pre_topc(sK3) != iProver_top
    | l1_struct_0(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_96])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_zfmisc_1(X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) != X1 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_3953,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v1_zfmisc_1(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | k6_domain_1(u1_struct_0(sK3),sK4) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_3954,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK4) != u1_struct_0(sK3)
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3953])).

cnf(c_30,negated_conjecture,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
    | v1_tex_2(k1_tex_2(sK3,sK4),sK3) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_3666,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) = iProver_top
    | v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_28,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v7_struct_0(X0)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_428,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v7_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_7,c_28])).

cnf(c_3662,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v7_struct_0(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_428])).

cnf(c_4443,plain,
    ( v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v7_struct_0(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3666,c_3662])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_34,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_38,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) != iProver_top
    | v1_tex_2(k1_tex_2(sK3,sK4),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_13,plain,
    ( ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v7_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_253,plain,
    ( v1_tex_2(k1_tex_2(sK3,sK4),sK3)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) ),
    inference(prop_impl,[status(thm)],[c_30])).

cnf(c_254,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
    | v1_tex_2(k1_tex_2(sK3,sK4),sK3) ),
    inference(renaming,[status(thm)],[c_253])).

cnf(c_1505,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v7_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k1_tex_2(sK3,sK4) != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_254])).

cnf(c_1506,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
    | ~ m1_pre_topc(k1_tex_2(sK3,sK4),sK3)
    | v2_struct_0(k1_tex_2(sK3,sK4))
    | v2_struct_0(sK3)
    | ~ v7_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_1505])).

cnf(c_1508,plain,
    ( ~ v7_struct_0(sK3)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
    | ~ m1_pre_topc(k1_tex_2(sK3,sK4),sK3)
    | v2_struct_0(k1_tex_2(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1506,c_33,c_32])).

cnf(c_1509,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
    | ~ m1_pre_topc(k1_tex_2(sK3,sK4),sK3)
    | v2_struct_0(k1_tex_2(sK3,sK4))
    | ~ v7_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_1508])).

cnf(c_1510,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) = iProver_top
    | m1_pre_topc(k1_tex_2(sK3,sK4),sK3) != iProver_top
    | v2_struct_0(k1_tex_2(sK3,sK4)) = iProver_top
    | v7_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1509])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3950,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ v2_struct_0(k1_tex_2(sK3,sK4))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_3951,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(k1_tex_2(sK3,sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3950])).

cnf(c_3961,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | m1_pre_topc(k1_tex_2(sK3,sK4),sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_3962,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tex_2(sK3,sK4),sK3) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3961])).

cnf(c_4633,plain,
    ( v7_struct_0(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4443,c_34,c_35,c_36,c_38,c_1510,c_3951,c_3962])).

cnf(c_5555,plain,
    ( v1_tex_2(k1_tex_2(sK3,sK4),sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5531,c_34,c_35,c_36,c_38,c_94,c_98,c_1510,c_3951,c_3954,c_3962,c_4443])).

cnf(c_7373,plain,
    ( sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(k1_tex_2(sK3,sK4))
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5134,c_5555])).

cnf(c_7851,plain,
    ( sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(k1_tex_2(sK3,sK4))
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7373,c_34,c_35,c_36])).

cnf(c_3665,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3687,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3689,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4014,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3687,c_3689])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_3681,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3685,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4531,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3681,c_3685])).

cnf(c_4835,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4014,c_4531])).

cnf(c_5135,plain,
    ( u1_struct_0(k1_tex_2(X0,X1)) = u1_struct_0(X0)
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3670,c_4835])).

cnf(c_6645,plain,
    ( u1_struct_0(k1_tex_2(sK3,sK4)) = u1_struct_0(sK3)
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3665,c_5135])).

cnf(c_6712,plain,
    ( u1_struct_0(k1_tex_2(sK3,sK4)) = u1_struct_0(sK3)
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6645,c_34,c_35])).

cnf(c_7859,plain,
    ( sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(k1_tex_2(sK3,sK4))
    | u1_struct_0(k1_tex_2(sK3,sK4)) = u1_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_7851,c_6712])).

cnf(c_20,plain,
    ( v1_tex_2(X0,X1)
    | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3674,plain,
    ( v1_tex_2(X0,X1) = iProver_top
    | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5292,plain,
    ( sK2(X0,X1) = u1_struct_0(X0)
    | v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) = iProver_top
    | v1_tex_2(X1,X0) = iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3674,c_3672])).

cnf(c_18,plain,
    ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
    | v1_tex_2(X1,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_67,plain,
    ( v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) != iProver_top
    | v1_tex_2(X1,X0) = iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6721,plain,
    ( sK2(X0,X1) = u1_struct_0(X0)
    | v1_tex_2(X1,X0) = iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5292,c_67])).

cnf(c_6729,plain,
    ( sK2(X0,k1_tex_2(X0,X1)) = u1_struct_0(X0)
    | v1_tex_2(k1_tex_2(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3670,c_6721])).

cnf(c_7465,plain,
    ( sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(sK3)
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6729,c_5555])).

cnf(c_7719,plain,
    ( sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(sK3)
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7465,c_34,c_35,c_36])).

cnf(c_7727,plain,
    ( sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(sK3)
    | u1_struct_0(k1_tex_2(sK3,sK4)) = u1_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_7719,c_6712])).

cnf(c_7878,plain,
    ( u1_struct_0(k1_tex_2(sK3,sK4)) = u1_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_7859,c_7727])).

cnf(c_10,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_448,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_7,c_10])).

cnf(c_3661,plain,
    ( v7_struct_0(X0) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_448])).

cnf(c_8253,plain,
    ( v7_struct_0(k1_tex_2(sK3,sK4)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK3)) = iProver_top
    | l1_pre_topc(k1_tex_2(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7878,c_3661])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_4091,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK3,sK4),X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k1_tex_2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_4092,plain,
    ( m1_pre_topc(k1_tex_2(sK3,sK4),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(k1_tex_2(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4091])).

cnf(c_4094,plain,
    ( m1_pre_topc(k1_tex_2(sK3,sK4),sK3) != iProver_top
    | l1_pre_topc(k1_tex_2(sK3,sK4)) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4092])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v7_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_3947,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | v7_struct_0(k1_tex_2(sK3,sK4))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_3948,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v7_struct_0(k1_tex_2(sK3,sK4)) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3947])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8253,c_4633,c_4094,c_3962,c_3948,c_98,c_94,c_36,c_35,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:48:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.53/1.05  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.05  
% 2.53/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.53/1.05  
% 2.53/1.05  ------  iProver source info
% 2.53/1.05  
% 2.53/1.05  git: date: 2020-06-30 10:37:57 +0100
% 2.53/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.53/1.05  git: non_committed_changes: false
% 2.53/1.05  git: last_make_outside_of_git: false
% 2.53/1.05  
% 2.53/1.05  ------ 
% 2.53/1.05  
% 2.53/1.05  ------ Input Options
% 2.53/1.05  
% 2.53/1.05  --out_options                           all
% 2.53/1.05  --tptp_safe_out                         true
% 2.53/1.05  --problem_path                          ""
% 2.53/1.05  --include_path                          ""
% 2.53/1.05  --clausifier                            res/vclausify_rel
% 2.53/1.05  --clausifier_options                    --mode clausify
% 2.53/1.05  --stdin                                 false
% 2.53/1.05  --stats_out                             all
% 2.53/1.05  
% 2.53/1.05  ------ General Options
% 2.53/1.05  
% 2.53/1.05  --fof                                   false
% 2.53/1.05  --time_out_real                         305.
% 2.53/1.05  --time_out_virtual                      -1.
% 2.53/1.05  --symbol_type_check                     false
% 2.53/1.05  --clausify_out                          false
% 2.53/1.05  --sig_cnt_out                           false
% 2.53/1.05  --trig_cnt_out                          false
% 2.53/1.05  --trig_cnt_out_tolerance                1.
% 2.53/1.05  --trig_cnt_out_sk_spl                   false
% 2.53/1.05  --abstr_cl_out                          false
% 2.53/1.05  
% 2.53/1.05  ------ Global Options
% 2.53/1.05  
% 2.53/1.05  --schedule                              default
% 2.53/1.05  --add_important_lit                     false
% 2.53/1.05  --prop_solver_per_cl                    1000
% 2.53/1.05  --min_unsat_core                        false
% 2.53/1.05  --soft_assumptions                      false
% 2.53/1.05  --soft_lemma_size                       3
% 2.53/1.05  --prop_impl_unit_size                   0
% 2.53/1.05  --prop_impl_unit                        []
% 2.53/1.05  --share_sel_clauses                     true
% 2.53/1.05  --reset_solvers                         false
% 2.53/1.05  --bc_imp_inh                            [conj_cone]
% 2.53/1.05  --conj_cone_tolerance                   3.
% 2.53/1.05  --extra_neg_conj                        none
% 2.53/1.05  --large_theory_mode                     true
% 2.53/1.05  --prolific_symb_bound                   200
% 2.53/1.05  --lt_threshold                          2000
% 2.53/1.05  --clause_weak_htbl                      true
% 2.53/1.05  --gc_record_bc_elim                     false
% 2.53/1.05  
% 2.53/1.05  ------ Preprocessing Options
% 2.53/1.05  
% 2.53/1.05  --preprocessing_flag                    true
% 2.53/1.05  --time_out_prep_mult                    0.1
% 2.53/1.05  --splitting_mode                        input
% 2.53/1.05  --splitting_grd                         true
% 2.53/1.05  --splitting_cvd                         false
% 2.53/1.05  --splitting_cvd_svl                     false
% 2.53/1.05  --splitting_nvd                         32
% 2.53/1.05  --sub_typing                            true
% 2.53/1.05  --prep_gs_sim                           true
% 2.53/1.05  --prep_unflatten                        true
% 2.53/1.05  --prep_res_sim                          true
% 2.53/1.05  --prep_upred                            true
% 2.53/1.05  --prep_sem_filter                       exhaustive
% 2.53/1.05  --prep_sem_filter_out                   false
% 2.53/1.05  --pred_elim                             true
% 2.53/1.05  --res_sim_input                         true
% 2.53/1.05  --eq_ax_congr_red                       true
% 2.53/1.05  --pure_diseq_elim                       true
% 2.53/1.05  --brand_transform                       false
% 2.53/1.05  --non_eq_to_eq                          false
% 2.53/1.05  --prep_def_merge                        true
% 2.53/1.05  --prep_def_merge_prop_impl              false
% 2.53/1.05  --prep_def_merge_mbd                    true
% 2.53/1.05  --prep_def_merge_tr_red                 false
% 2.53/1.05  --prep_def_merge_tr_cl                  false
% 2.53/1.05  --smt_preprocessing                     true
% 2.53/1.05  --smt_ac_axioms                         fast
% 2.53/1.05  --preprocessed_out                      false
% 2.53/1.05  --preprocessed_stats                    false
% 2.53/1.05  
% 2.53/1.05  ------ Abstraction refinement Options
% 2.53/1.05  
% 2.53/1.05  --abstr_ref                             []
% 2.53/1.05  --abstr_ref_prep                        false
% 2.53/1.05  --abstr_ref_until_sat                   false
% 2.53/1.05  --abstr_ref_sig_restrict                funpre
% 2.53/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 2.53/1.05  --abstr_ref_under                       []
% 2.53/1.05  
% 2.53/1.05  ------ SAT Options
% 2.53/1.05  
% 2.53/1.05  --sat_mode                              false
% 2.53/1.05  --sat_fm_restart_options                ""
% 2.53/1.05  --sat_gr_def                            false
% 2.53/1.05  --sat_epr_types                         true
% 2.53/1.05  --sat_non_cyclic_types                  false
% 2.53/1.05  --sat_finite_models                     false
% 2.53/1.05  --sat_fm_lemmas                         false
% 2.53/1.05  --sat_fm_prep                           false
% 2.53/1.05  --sat_fm_uc_incr                        true
% 2.53/1.05  --sat_out_model                         small
% 2.53/1.05  --sat_out_clauses                       false
% 2.53/1.05  
% 2.53/1.05  ------ QBF Options
% 2.53/1.05  
% 2.53/1.05  --qbf_mode                              false
% 2.53/1.05  --qbf_elim_univ                         false
% 2.53/1.05  --qbf_dom_inst                          none
% 2.53/1.05  --qbf_dom_pre_inst                      false
% 2.53/1.05  --qbf_sk_in                             false
% 2.53/1.05  --qbf_pred_elim                         true
% 2.53/1.05  --qbf_split                             512
% 2.53/1.05  
% 2.53/1.05  ------ BMC1 Options
% 2.53/1.05  
% 2.53/1.05  --bmc1_incremental                      false
% 2.53/1.05  --bmc1_axioms                           reachable_all
% 2.53/1.05  --bmc1_min_bound                        0
% 2.53/1.05  --bmc1_max_bound                        -1
% 2.53/1.05  --bmc1_max_bound_default                -1
% 2.53/1.05  --bmc1_symbol_reachability              true
% 2.53/1.05  --bmc1_property_lemmas                  false
% 2.53/1.05  --bmc1_k_induction                      false
% 2.53/1.05  --bmc1_non_equiv_states                 false
% 2.53/1.05  --bmc1_deadlock                         false
% 2.53/1.05  --bmc1_ucm                              false
% 2.53/1.05  --bmc1_add_unsat_core                   none
% 2.53/1.05  --bmc1_unsat_core_children              false
% 2.53/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 2.53/1.05  --bmc1_out_stat                         full
% 2.53/1.05  --bmc1_ground_init                      false
% 2.53/1.05  --bmc1_pre_inst_next_state              false
% 2.53/1.05  --bmc1_pre_inst_state                   false
% 2.53/1.05  --bmc1_pre_inst_reach_state             false
% 2.53/1.05  --bmc1_out_unsat_core                   false
% 2.53/1.05  --bmc1_aig_witness_out                  false
% 2.53/1.05  --bmc1_verbose                          false
% 2.53/1.05  --bmc1_dump_clauses_tptp                false
% 2.53/1.05  --bmc1_dump_unsat_core_tptp             false
% 2.53/1.05  --bmc1_dump_file                        -
% 2.53/1.05  --bmc1_ucm_expand_uc_limit              128
% 2.53/1.05  --bmc1_ucm_n_expand_iterations          6
% 2.53/1.05  --bmc1_ucm_extend_mode                  1
% 2.53/1.05  --bmc1_ucm_init_mode                    2
% 2.53/1.05  --bmc1_ucm_cone_mode                    none
% 2.53/1.05  --bmc1_ucm_reduced_relation_type        0
% 2.53/1.05  --bmc1_ucm_relax_model                  4
% 2.53/1.05  --bmc1_ucm_full_tr_after_sat            true
% 2.53/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 2.53/1.05  --bmc1_ucm_layered_model                none
% 2.53/1.05  --bmc1_ucm_max_lemma_size               10
% 2.53/1.05  
% 2.53/1.05  ------ AIG Options
% 2.53/1.05  
% 2.53/1.05  --aig_mode                              false
% 2.53/1.05  
% 2.53/1.05  ------ Instantiation Options
% 2.53/1.05  
% 2.53/1.05  --instantiation_flag                    true
% 2.53/1.05  --inst_sos_flag                         false
% 2.53/1.05  --inst_sos_phase                        true
% 2.53/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.53/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.53/1.05  --inst_lit_sel_side                     num_symb
% 2.53/1.05  --inst_solver_per_active                1400
% 2.53/1.05  --inst_solver_calls_frac                1.
% 2.53/1.05  --inst_passive_queue_type               priority_queues
% 2.53/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.53/1.05  --inst_passive_queues_freq              [25;2]
% 2.53/1.05  --inst_dismatching                      true
% 2.53/1.05  --inst_eager_unprocessed_to_passive     true
% 2.53/1.05  --inst_prop_sim_given                   true
% 2.53/1.05  --inst_prop_sim_new                     false
% 2.53/1.05  --inst_subs_new                         false
% 2.53/1.05  --inst_eq_res_simp                      false
% 2.53/1.05  --inst_subs_given                       false
% 2.53/1.05  --inst_orphan_elimination               true
% 2.53/1.05  --inst_learning_loop_flag               true
% 2.53/1.05  --inst_learning_start                   3000
% 2.53/1.05  --inst_learning_factor                  2
% 2.53/1.05  --inst_start_prop_sim_after_learn       3
% 2.53/1.05  --inst_sel_renew                        solver
% 2.53/1.05  --inst_lit_activity_flag                true
% 2.53/1.05  --inst_restr_to_given                   false
% 2.53/1.05  --inst_activity_threshold               500
% 2.53/1.05  --inst_out_proof                        true
% 2.53/1.05  
% 2.53/1.05  ------ Resolution Options
% 2.53/1.05  
% 2.53/1.05  --resolution_flag                       true
% 2.53/1.05  --res_lit_sel                           adaptive
% 2.53/1.05  --res_lit_sel_side                      none
% 2.53/1.05  --res_ordering                          kbo
% 2.53/1.05  --res_to_prop_solver                    active
% 2.53/1.05  --res_prop_simpl_new                    false
% 2.53/1.05  --res_prop_simpl_given                  true
% 2.53/1.05  --res_passive_queue_type                priority_queues
% 2.53/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.53/1.05  --res_passive_queues_freq               [15;5]
% 2.53/1.05  --res_forward_subs                      full
% 2.53/1.05  --res_backward_subs                     full
% 2.53/1.05  --res_forward_subs_resolution           true
% 2.53/1.05  --res_backward_subs_resolution          true
% 2.53/1.05  --res_orphan_elimination                true
% 2.53/1.05  --res_time_limit                        2.
% 2.53/1.05  --res_out_proof                         true
% 2.53/1.05  
% 2.53/1.05  ------ Superposition Options
% 2.53/1.05  
% 2.53/1.05  --superposition_flag                    true
% 2.53/1.05  --sup_passive_queue_type                priority_queues
% 2.53/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.53/1.05  --sup_passive_queues_freq               [8;1;4]
% 2.53/1.05  --demod_completeness_check              fast
% 2.53/1.05  --demod_use_ground                      true
% 2.53/1.05  --sup_to_prop_solver                    passive
% 2.53/1.05  --sup_prop_simpl_new                    true
% 2.53/1.05  --sup_prop_simpl_given                  true
% 2.53/1.05  --sup_fun_splitting                     false
% 2.53/1.05  --sup_smt_interval                      50000
% 2.53/1.05  
% 2.53/1.05  ------ Superposition Simplification Setup
% 2.53/1.05  
% 2.53/1.05  --sup_indices_passive                   []
% 2.53/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 2.53/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.05  --sup_full_bw                           [BwDemod]
% 2.53/1.05  --sup_immed_triv                        [TrivRules]
% 2.53/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.53/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.05  --sup_immed_bw_main                     []
% 2.53/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 2.53/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/1.05  
% 2.53/1.05  ------ Combination Options
% 2.53/1.05  
% 2.53/1.05  --comb_res_mult                         3
% 2.53/1.05  --comb_sup_mult                         2
% 2.53/1.05  --comb_inst_mult                        10
% 2.53/1.05  
% 2.53/1.05  ------ Debug Options
% 2.53/1.05  
% 2.53/1.05  --dbg_backtrace                         false
% 2.53/1.05  --dbg_dump_prop_clauses                 false
% 2.53/1.05  --dbg_dump_prop_clauses_file            -
% 2.53/1.05  --dbg_out_stat                          false
% 2.53/1.05  ------ Parsing...
% 2.53/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.53/1.05  
% 2.53/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.53/1.05  
% 2.53/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.53/1.05  
% 2.53/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.53/1.05  ------ Proving...
% 2.53/1.05  ------ Problem Properties 
% 2.53/1.05  
% 2.53/1.05  
% 2.53/1.05  clauses                                 30
% 2.53/1.05  conjectures                             5
% 2.53/1.05  EPR                                     8
% 2.53/1.05  Horn                                    18
% 2.53/1.05  unary                                   4
% 2.53/1.05  binary                                  6
% 2.53/1.05  lits                                    90
% 2.53/1.05  lits eq                                 5
% 2.53/1.05  fd_pure                                 0
% 2.53/1.05  fd_pseudo                               0
% 2.53/1.05  fd_cond                                 0
% 2.53/1.05  fd_pseudo_cond                          2
% 2.53/1.05  AC symbols                              0
% 2.53/1.05  
% 2.53/1.05  ------ Schedule dynamic 5 is on 
% 2.53/1.05  
% 2.53/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.53/1.05  
% 2.53/1.05  
% 2.53/1.05  ------ 
% 2.53/1.05  Current options:
% 2.53/1.05  ------ 
% 2.53/1.05  
% 2.53/1.05  ------ Input Options
% 2.53/1.05  
% 2.53/1.05  --out_options                           all
% 2.53/1.05  --tptp_safe_out                         true
% 2.53/1.05  --problem_path                          ""
% 2.53/1.05  --include_path                          ""
% 2.53/1.05  --clausifier                            res/vclausify_rel
% 2.53/1.05  --clausifier_options                    --mode clausify
% 2.53/1.05  --stdin                                 false
% 2.53/1.05  --stats_out                             all
% 2.53/1.05  
% 2.53/1.05  ------ General Options
% 2.53/1.05  
% 2.53/1.05  --fof                                   false
% 2.53/1.05  --time_out_real                         305.
% 2.53/1.05  --time_out_virtual                      -1.
% 2.53/1.05  --symbol_type_check                     false
% 2.53/1.05  --clausify_out                          false
% 2.53/1.05  --sig_cnt_out                           false
% 2.53/1.05  --trig_cnt_out                          false
% 2.53/1.05  --trig_cnt_out_tolerance                1.
% 2.53/1.05  --trig_cnt_out_sk_spl                   false
% 2.53/1.05  --abstr_cl_out                          false
% 2.53/1.05  
% 2.53/1.05  ------ Global Options
% 2.53/1.05  
% 2.53/1.05  --schedule                              default
% 2.53/1.05  --add_important_lit                     false
% 2.53/1.05  --prop_solver_per_cl                    1000
% 2.53/1.05  --min_unsat_core                        false
% 2.53/1.05  --soft_assumptions                      false
% 2.53/1.05  --soft_lemma_size                       3
% 2.53/1.05  --prop_impl_unit_size                   0
% 2.53/1.05  --prop_impl_unit                        []
% 2.53/1.05  --share_sel_clauses                     true
% 2.53/1.05  --reset_solvers                         false
% 2.53/1.05  --bc_imp_inh                            [conj_cone]
% 2.53/1.05  --conj_cone_tolerance                   3.
% 2.53/1.05  --extra_neg_conj                        none
% 2.53/1.05  --large_theory_mode                     true
% 2.53/1.05  --prolific_symb_bound                   200
% 2.53/1.05  --lt_threshold                          2000
% 2.53/1.05  --clause_weak_htbl                      true
% 2.53/1.05  --gc_record_bc_elim                     false
% 2.53/1.05  
% 2.53/1.05  ------ Preprocessing Options
% 2.53/1.05  
% 2.53/1.05  --preprocessing_flag                    true
% 2.53/1.05  --time_out_prep_mult                    0.1
% 2.53/1.05  --splitting_mode                        input
% 2.53/1.05  --splitting_grd                         true
% 2.53/1.05  --splitting_cvd                         false
% 2.53/1.05  --splitting_cvd_svl                     false
% 2.53/1.05  --splitting_nvd                         32
% 2.53/1.05  --sub_typing                            true
% 2.53/1.05  --prep_gs_sim                           true
% 2.53/1.05  --prep_unflatten                        true
% 2.53/1.05  --prep_res_sim                          true
% 2.53/1.05  --prep_upred                            true
% 2.53/1.05  --prep_sem_filter                       exhaustive
% 2.53/1.05  --prep_sem_filter_out                   false
% 2.53/1.05  --pred_elim                             true
% 2.53/1.05  --res_sim_input                         true
% 2.53/1.05  --eq_ax_congr_red                       true
% 2.53/1.05  --pure_diseq_elim                       true
% 2.53/1.05  --brand_transform                       false
% 2.53/1.05  --non_eq_to_eq                          false
% 2.53/1.05  --prep_def_merge                        true
% 2.53/1.05  --prep_def_merge_prop_impl              false
% 2.53/1.05  --prep_def_merge_mbd                    true
% 2.53/1.05  --prep_def_merge_tr_red                 false
% 2.53/1.05  --prep_def_merge_tr_cl                  false
% 2.53/1.05  --smt_preprocessing                     true
% 2.53/1.05  --smt_ac_axioms                         fast
% 2.53/1.05  --preprocessed_out                      false
% 2.53/1.05  --preprocessed_stats                    false
% 2.53/1.05  
% 2.53/1.05  ------ Abstraction refinement Options
% 2.53/1.05  
% 2.53/1.05  --abstr_ref                             []
% 2.53/1.05  --abstr_ref_prep                        false
% 2.53/1.05  --abstr_ref_until_sat                   false
% 2.53/1.05  --abstr_ref_sig_restrict                funpre
% 2.53/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 2.53/1.05  --abstr_ref_under                       []
% 2.53/1.05  
% 2.53/1.05  ------ SAT Options
% 2.53/1.05  
% 2.53/1.05  --sat_mode                              false
% 2.53/1.05  --sat_fm_restart_options                ""
% 2.53/1.05  --sat_gr_def                            false
% 2.53/1.05  --sat_epr_types                         true
% 2.53/1.05  --sat_non_cyclic_types                  false
% 2.53/1.05  --sat_finite_models                     false
% 2.53/1.05  --sat_fm_lemmas                         false
% 2.53/1.05  --sat_fm_prep                           false
% 2.53/1.05  --sat_fm_uc_incr                        true
% 2.53/1.05  --sat_out_model                         small
% 2.53/1.05  --sat_out_clauses                       false
% 2.53/1.05  
% 2.53/1.05  ------ QBF Options
% 2.53/1.05  
% 2.53/1.05  --qbf_mode                              false
% 2.53/1.05  --qbf_elim_univ                         false
% 2.53/1.05  --qbf_dom_inst                          none
% 2.53/1.05  --qbf_dom_pre_inst                      false
% 2.53/1.05  --qbf_sk_in                             false
% 2.53/1.05  --qbf_pred_elim                         true
% 2.53/1.05  --qbf_split                             512
% 2.53/1.05  
% 2.53/1.05  ------ BMC1 Options
% 2.53/1.05  
% 2.53/1.05  --bmc1_incremental                      false
% 2.53/1.05  --bmc1_axioms                           reachable_all
% 2.53/1.05  --bmc1_min_bound                        0
% 2.53/1.05  --bmc1_max_bound                        -1
% 2.53/1.05  --bmc1_max_bound_default                -1
% 2.53/1.05  --bmc1_symbol_reachability              true
% 2.53/1.05  --bmc1_property_lemmas                  false
% 2.53/1.05  --bmc1_k_induction                      false
% 2.53/1.05  --bmc1_non_equiv_states                 false
% 2.53/1.05  --bmc1_deadlock                         false
% 2.53/1.05  --bmc1_ucm                              false
% 2.53/1.05  --bmc1_add_unsat_core                   none
% 2.53/1.05  --bmc1_unsat_core_children              false
% 2.53/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 2.53/1.05  --bmc1_out_stat                         full
% 2.53/1.05  --bmc1_ground_init                      false
% 2.53/1.05  --bmc1_pre_inst_next_state              false
% 2.53/1.05  --bmc1_pre_inst_state                   false
% 2.53/1.05  --bmc1_pre_inst_reach_state             false
% 2.53/1.05  --bmc1_out_unsat_core                   false
% 2.53/1.05  --bmc1_aig_witness_out                  false
% 2.53/1.05  --bmc1_verbose                          false
% 2.53/1.05  --bmc1_dump_clauses_tptp                false
% 2.53/1.05  --bmc1_dump_unsat_core_tptp             false
% 2.53/1.05  --bmc1_dump_file                        -
% 2.53/1.05  --bmc1_ucm_expand_uc_limit              128
% 2.53/1.05  --bmc1_ucm_n_expand_iterations          6
% 2.53/1.05  --bmc1_ucm_extend_mode                  1
% 2.53/1.05  --bmc1_ucm_init_mode                    2
% 2.53/1.05  --bmc1_ucm_cone_mode                    none
% 2.53/1.05  --bmc1_ucm_reduced_relation_type        0
% 2.53/1.05  --bmc1_ucm_relax_model                  4
% 2.53/1.05  --bmc1_ucm_full_tr_after_sat            true
% 2.53/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 2.53/1.05  --bmc1_ucm_layered_model                none
% 2.53/1.05  --bmc1_ucm_max_lemma_size               10
% 2.53/1.05  
% 2.53/1.05  ------ AIG Options
% 2.53/1.05  
% 2.53/1.05  --aig_mode                              false
% 2.53/1.05  
% 2.53/1.05  ------ Instantiation Options
% 2.53/1.05  
% 2.53/1.05  --instantiation_flag                    true
% 2.53/1.05  --inst_sos_flag                         false
% 2.53/1.05  --inst_sos_phase                        true
% 2.53/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.53/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.53/1.05  --inst_lit_sel_side                     none
% 2.53/1.05  --inst_solver_per_active                1400
% 2.53/1.05  --inst_solver_calls_frac                1.
% 2.53/1.05  --inst_passive_queue_type               priority_queues
% 2.53/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.53/1.05  --inst_passive_queues_freq              [25;2]
% 2.53/1.05  --inst_dismatching                      true
% 2.53/1.05  --inst_eager_unprocessed_to_passive     true
% 2.53/1.05  --inst_prop_sim_given                   true
% 2.53/1.05  --inst_prop_sim_new                     false
% 2.53/1.05  --inst_subs_new                         false
% 2.53/1.05  --inst_eq_res_simp                      false
% 2.53/1.05  --inst_subs_given                       false
% 2.53/1.05  --inst_orphan_elimination               true
% 2.53/1.05  --inst_learning_loop_flag               true
% 2.53/1.05  --inst_learning_start                   3000
% 2.53/1.05  --inst_learning_factor                  2
% 2.53/1.05  --inst_start_prop_sim_after_learn       3
% 2.53/1.05  --inst_sel_renew                        solver
% 2.53/1.05  --inst_lit_activity_flag                true
% 2.53/1.05  --inst_restr_to_given                   false
% 2.53/1.05  --inst_activity_threshold               500
% 2.53/1.05  --inst_out_proof                        true
% 2.53/1.05  
% 2.53/1.05  ------ Resolution Options
% 2.53/1.05  
% 2.53/1.05  --resolution_flag                       false
% 2.53/1.05  --res_lit_sel                           adaptive
% 2.53/1.05  --res_lit_sel_side                      none
% 2.53/1.05  --res_ordering                          kbo
% 2.53/1.05  --res_to_prop_solver                    active
% 2.53/1.05  --res_prop_simpl_new                    false
% 2.53/1.05  --res_prop_simpl_given                  true
% 2.53/1.05  --res_passive_queue_type                priority_queues
% 2.53/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.53/1.05  --res_passive_queues_freq               [15;5]
% 2.53/1.05  --res_forward_subs                      full
% 2.53/1.05  --res_backward_subs                     full
% 2.53/1.05  --res_forward_subs_resolution           true
% 2.53/1.05  --res_backward_subs_resolution          true
% 2.53/1.05  --res_orphan_elimination                true
% 2.53/1.05  --res_time_limit                        2.
% 2.53/1.05  --res_out_proof                         true
% 2.53/1.05  
% 2.53/1.05  ------ Superposition Options
% 2.53/1.05  
% 2.53/1.05  --superposition_flag                    true
% 2.53/1.05  --sup_passive_queue_type                priority_queues
% 2.53/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.53/1.05  --sup_passive_queues_freq               [8;1;4]
% 2.53/1.05  --demod_completeness_check              fast
% 2.53/1.05  --demod_use_ground                      true
% 2.53/1.05  --sup_to_prop_solver                    passive
% 2.53/1.05  --sup_prop_simpl_new                    true
% 2.53/1.05  --sup_prop_simpl_given                  true
% 2.53/1.05  --sup_fun_splitting                     false
% 2.53/1.05  --sup_smt_interval                      50000
% 2.53/1.05  
% 2.53/1.05  ------ Superposition Simplification Setup
% 2.53/1.05  
% 2.53/1.05  --sup_indices_passive                   []
% 2.53/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 2.53/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.05  --sup_full_bw                           [BwDemod]
% 2.53/1.05  --sup_immed_triv                        [TrivRules]
% 2.53/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.53/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.05  --sup_immed_bw_main                     []
% 2.53/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 2.53/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/1.05  
% 2.53/1.05  ------ Combination Options
% 2.53/1.05  
% 2.53/1.05  --comb_res_mult                         3
% 2.53/1.05  --comb_sup_mult                         2
% 2.53/1.05  --comb_inst_mult                        10
% 2.53/1.05  
% 2.53/1.05  ------ Debug Options
% 2.53/1.05  
% 2.53/1.05  --dbg_backtrace                         false
% 2.53/1.05  --dbg_dump_prop_clauses                 false
% 2.53/1.05  --dbg_dump_prop_clauses_file            -
% 2.53/1.05  --dbg_out_stat                          false
% 2.53/1.05  
% 2.53/1.05  
% 2.53/1.05  
% 2.53/1.05  
% 2.53/1.05  ------ Proving...
% 2.53/1.05  
% 2.53/1.05  
% 2.53/1.05  % SZS status Theorem for theBenchmark.p
% 2.53/1.05  
% 2.53/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 2.53/1.05  
% 2.53/1.05  fof(f14,axiom,(
% 2.53/1.05    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.53/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.05  
% 2.53/1.05  fof(f20,plain,(
% 2.53/1.05    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.53/1.05    inference(pure_predicate_removal,[],[f14])).
% 2.53/1.05  
% 2.53/1.05  fof(f39,plain,(
% 2.53/1.05    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.53/1.05    inference(ennf_transformation,[],[f20])).
% 2.53/1.05  
% 2.53/1.05  fof(f40,plain,(
% 2.53/1.05    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.53/1.05    inference(flattening,[],[f39])).
% 2.53/1.05  
% 2.53/1.05  fof(f92,plain,(
% 2.53/1.05    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.53/1.05    inference(cnf_transformation,[],[f40])).
% 2.53/1.05  
% 2.53/1.05  fof(f12,axiom,(
% 2.53/1.05    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 2.53/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.05  
% 2.53/1.05  fof(f36,plain,(
% 2.53/1.05    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.53/1.05    inference(ennf_transformation,[],[f12])).
% 2.53/1.05  
% 2.53/1.05  fof(f37,plain,(
% 2.53/1.05    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.53/1.05    inference(flattening,[],[f36])).
% 2.53/1.05  
% 2.53/1.05  fof(f57,plain,(
% 2.53/1.05    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.53/1.05    inference(nnf_transformation,[],[f37])).
% 2.53/1.05  
% 2.53/1.05  fof(f58,plain,(
% 2.53/1.05    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.53/1.05    inference(rectify,[],[f57])).
% 2.53/1.05  
% 2.53/1.05  fof(f59,plain,(
% 2.53/1.05    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.53/1.05    introduced(choice_axiom,[])).
% 2.53/1.05  
% 2.53/1.05  fof(f60,plain,(
% 2.53/1.05    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.53/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f58,f59])).
% 2.53/1.05  
% 2.53/1.05  fof(f87,plain,(
% 2.53/1.05    ( ! [X0,X1] : (v1_tex_2(X1,X0) | u1_struct_0(X1) = sK2(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.53/1.05    inference(cnf_transformation,[],[f60])).
% 2.53/1.05  
% 2.53/1.05  fof(f8,axiom,(
% 2.53/1.05    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.53/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.05  
% 2.53/1.05  fof(f30,plain,(
% 2.53/1.05    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.53/1.05    inference(ennf_transformation,[],[f8])).
% 2.53/1.05  
% 2.53/1.05  fof(f31,plain,(
% 2.53/1.05    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.53/1.05    inference(flattening,[],[f30])).
% 2.53/1.05  
% 2.53/1.05  fof(f78,plain,(
% 2.53/1.05    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.53/1.05    inference(cnf_transformation,[],[f31])).
% 2.53/1.05  
% 2.53/1.05  fof(f13,axiom,(
% 2.53/1.05    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 2.53/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.05  
% 2.53/1.05  fof(f38,plain,(
% 2.53/1.05    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.53/1.05    inference(ennf_transformation,[],[f13])).
% 2.53/1.05  
% 2.53/1.05  fof(f61,plain,(
% 2.53/1.05    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.53/1.05    inference(nnf_transformation,[],[f38])).
% 2.53/1.05  
% 2.53/1.05  fof(f90,plain,(
% 2.53/1.05    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.53/1.05    inference(cnf_transformation,[],[f61])).
% 2.53/1.05  
% 2.53/1.05  fof(f17,conjecture,(
% 2.53/1.05    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 2.53/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.05  
% 2.53/1.05  fof(f18,negated_conjecture,(
% 2.53/1.05    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 2.53/1.05    inference(negated_conjecture,[],[f17])).
% 2.53/1.05  
% 2.53/1.05  fof(f45,plain,(
% 2.53/1.05    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.53/1.05    inference(ennf_transformation,[],[f18])).
% 2.53/1.05  
% 2.53/1.05  fof(f46,plain,(
% 2.53/1.05    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.53/1.05    inference(flattening,[],[f45])).
% 2.53/1.05  
% 2.53/1.05  fof(f62,plain,(
% 2.53/1.05    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.53/1.05    inference(nnf_transformation,[],[f46])).
% 2.53/1.05  
% 2.53/1.05  fof(f63,plain,(
% 2.53/1.05    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.53/1.05    inference(flattening,[],[f62])).
% 2.53/1.05  
% 2.53/1.05  fof(f65,plain,(
% 2.53/1.05    ( ! [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),sK4),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,sK4),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),sK4),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,sK4),X0)) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 2.53/1.05    introduced(choice_axiom,[])).
% 2.53/1.05  
% 2.53/1.05  fof(f64,plain,(
% 2.53/1.05    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK3),X1),u1_struct_0(sK3)) | ~v1_tex_2(k1_tex_2(sK3,X1),sK3)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK3),X1),u1_struct_0(sK3)) | v1_tex_2(k1_tex_2(sK3,X1),sK3)) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 2.53/1.05    introduced(choice_axiom,[])).
% 2.53/1.05  
% 2.53/1.05  fof(f66,plain,(
% 2.53/1.05    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) | ~v1_tex_2(k1_tex_2(sK3,sK4),sK3)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) | v1_tex_2(k1_tex_2(sK3,sK4),sK3)) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 2.53/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f63,f65,f64])).
% 2.53/1.05  
% 2.53/1.05  fof(f100,plain,(
% 2.53/1.05    ~v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) | ~v1_tex_2(k1_tex_2(sK3,sK4),sK3)),
% 2.53/1.05    inference(cnf_transformation,[],[f66])).
% 2.53/1.05  
% 2.53/1.05  fof(f97,plain,(
% 2.53/1.05    l1_pre_topc(sK3)),
% 2.53/1.05    inference(cnf_transformation,[],[f66])).
% 2.53/1.05  
% 2.53/1.05  fof(f98,plain,(
% 2.53/1.05    m1_subset_1(sK4,u1_struct_0(sK3))),
% 2.53/1.05    inference(cnf_transformation,[],[f66])).
% 2.53/1.05  
% 2.53/1.05  fof(f6,axiom,(
% 2.53/1.05    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0)) => ~v1_zfmisc_1(u1_struct_0(X0)))),
% 2.53/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.05  
% 2.53/1.05  fof(f26,plain,(
% 2.53/1.05    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v7_struct_0(X0)))),
% 2.53/1.05    inference(ennf_transformation,[],[f6])).
% 2.53/1.05  
% 2.53/1.05  fof(f27,plain,(
% 2.53/1.05    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 2.53/1.05    inference(flattening,[],[f26])).
% 2.53/1.05  
% 2.53/1.05  fof(f76,plain,(
% 2.53/1.05    ( ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0)) )),
% 2.53/1.05    inference(cnf_transformation,[],[f27])).
% 2.53/1.05  
% 2.53/1.05  fof(f4,axiom,(
% 2.53/1.05    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.53/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.05  
% 2.53/1.05  fof(f24,plain,(
% 2.53/1.05    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.53/1.05    inference(ennf_transformation,[],[f4])).
% 2.53/1.05  
% 2.53/1.05  fof(f74,plain,(
% 2.53/1.05    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.53/1.05    inference(cnf_transformation,[],[f24])).
% 2.53/1.05  
% 2.53/1.05  fof(f11,axiom,(
% 2.53/1.05    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 2.53/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.05  
% 2.53/1.05  fof(f35,plain,(
% 2.53/1.05    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 2.53/1.05    inference(ennf_transformation,[],[f11])).
% 2.53/1.05  
% 2.53/1.05  fof(f53,plain,(
% 2.53/1.05    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 2.53/1.05    inference(nnf_transformation,[],[f35])).
% 2.53/1.05  
% 2.53/1.05  fof(f54,plain,(
% 2.53/1.05    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 2.53/1.05    inference(rectify,[],[f53])).
% 2.53/1.05  
% 2.53/1.05  fof(f55,plain,(
% 2.53/1.05    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK1(X0)) = X0 & m1_subset_1(sK1(X0),X0)))),
% 2.53/1.05    introduced(choice_axiom,[])).
% 2.53/1.05  
% 2.53/1.05  fof(f56,plain,(
% 2.53/1.05    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK1(X0)) = X0 & m1_subset_1(sK1(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 2.53/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f54,f55])).
% 2.53/1.05  
% 2.53/1.05  fof(f84,plain,(
% 2.53/1.05    ( ! [X0,X1] : (v1_zfmisc_1(X0) | k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.53/1.05    inference(cnf_transformation,[],[f56])).
% 2.53/1.05  
% 2.53/1.05  fof(f99,plain,(
% 2.53/1.05    v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) | v1_tex_2(k1_tex_2(sK3,sK4),sK3)),
% 2.53/1.05    inference(cnf_transformation,[],[f66])).
% 2.53/1.05  
% 2.53/1.05  fof(f16,axiom,(
% 2.53/1.05    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 2.53/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.05  
% 2.53/1.05  fof(f43,plain,(
% 2.53/1.05    ! [X0] : (! [X1] : ((~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.53/1.05    inference(ennf_transformation,[],[f16])).
% 2.53/1.05  
% 2.53/1.05  fof(f44,plain,(
% 2.53/1.05    ! [X0] : (! [X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.53/1.05    inference(flattening,[],[f43])).
% 2.53/1.05  
% 2.53/1.05  fof(f95,plain,(
% 2.53/1.05    ( ! [X0,X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.53/1.05    inference(cnf_transformation,[],[f44])).
% 2.53/1.05  
% 2.53/1.05  fof(f96,plain,(
% 2.53/1.05    ~v2_struct_0(sK3)),
% 2.53/1.05    inference(cnf_transformation,[],[f66])).
% 2.53/1.05  
% 2.53/1.05  fof(f10,axiom,(
% 2.53/1.05    ! [X0] : ((l1_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (~v2_struct_0(X1) => (~v1_tex_2(X1,X0) & ~v2_struct_0(X1)))))),
% 2.53/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.05  
% 2.53/1.05  fof(f33,plain,(
% 2.53/1.05    ! [X0] : (! [X1] : (((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)))),
% 2.53/1.05    inference(ennf_transformation,[],[f10])).
% 2.53/1.05  
% 2.53/1.05  fof(f34,plain,(
% 2.53/1.05    ! [X0] : (! [X1] : ((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))),
% 2.53/1.05    inference(flattening,[],[f33])).
% 2.53/1.05  
% 2.53/1.05  fof(f81,plain,(
% 2.53/1.05    ( ! [X0,X1] : (~v1_tex_2(X1,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)) )),
% 2.53/1.05    inference(cnf_transformation,[],[f34])).
% 2.53/1.05  
% 2.53/1.05  fof(f15,axiom,(
% 2.53/1.05    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.53/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.05  
% 2.53/1.05  fof(f21,plain,(
% 2.53/1.05    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.53/1.05    inference(pure_predicate_removal,[],[f15])).
% 2.53/1.05  
% 2.53/1.05  fof(f41,plain,(
% 2.53/1.05    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.53/1.05    inference(ennf_transformation,[],[f21])).
% 2.53/1.05  
% 2.53/1.05  fof(f42,plain,(
% 2.53/1.05    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.53/1.05    inference(flattening,[],[f41])).
% 2.53/1.05  
% 2.53/1.05  fof(f93,plain,(
% 2.53/1.05    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.53/1.05    inference(cnf_transformation,[],[f42])).
% 2.53/1.05  
% 2.53/1.05  fof(f2,axiom,(
% 2.53/1.05    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.53/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.05  
% 2.53/1.05  fof(f23,plain,(
% 2.53/1.05    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.53/1.05    inference(ennf_transformation,[],[f2])).
% 2.53/1.05  
% 2.53/1.05  fof(f47,plain,(
% 2.53/1.05    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.53/1.05    inference(nnf_transformation,[],[f23])).
% 2.53/1.05  
% 2.53/1.05  fof(f48,plain,(
% 2.53/1.05    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.53/1.05    inference(rectify,[],[f47])).
% 2.53/1.05  
% 2.53/1.05  fof(f49,plain,(
% 2.53/1.05    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.53/1.05    introduced(choice_axiom,[])).
% 2.53/1.05  
% 2.53/1.05  fof(f50,plain,(
% 2.53/1.05    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.53/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f49])).
% 2.53/1.05  
% 2.53/1.05  fof(f69,plain,(
% 2.53/1.05    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.53/1.05    inference(cnf_transformation,[],[f50])).
% 2.53/1.05  
% 2.53/1.05  fof(f1,axiom,(
% 2.53/1.05    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.53/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.05  
% 2.53/1.05  fof(f19,plain,(
% 2.53/1.05    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 2.53/1.05    inference(unused_predicate_definition_removal,[],[f1])).
% 2.53/1.05  
% 2.53/1.05  fof(f22,plain,(
% 2.53/1.05    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 2.53/1.05    inference(ennf_transformation,[],[f19])).
% 2.53/1.05  
% 2.53/1.05  fof(f67,plain,(
% 2.53/1.05    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 2.53/1.05    inference(cnf_transformation,[],[f22])).
% 2.53/1.05  
% 2.53/1.05  fof(f9,axiom,(
% 2.53/1.05    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 2.53/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.05  
% 2.53/1.05  fof(f32,plain,(
% 2.53/1.05    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.53/1.05    inference(ennf_transformation,[],[f9])).
% 2.53/1.05  
% 2.53/1.05  fof(f79,plain,(
% 2.53/1.05    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.53/1.05    inference(cnf_transformation,[],[f32])).
% 2.53/1.05  
% 2.53/1.05  fof(f3,axiom,(
% 2.53/1.05    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.53/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.05  
% 2.53/1.05  fof(f51,plain,(
% 2.53/1.05    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.53/1.05    inference(nnf_transformation,[],[f3])).
% 2.53/1.05  
% 2.53/1.05  fof(f52,plain,(
% 2.53/1.05    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.53/1.05    inference(flattening,[],[f51])).
% 2.53/1.05  
% 2.53/1.05  fof(f73,plain,(
% 2.53/1.05    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.53/1.05    inference(cnf_transformation,[],[f52])).
% 2.53/1.05  
% 2.53/1.05  fof(f86,plain,(
% 2.53/1.05    ( ! [X0,X1] : (v1_tex_2(X1,X0) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.53/1.05    inference(cnf_transformation,[],[f60])).
% 2.53/1.05  
% 2.53/1.05  fof(f88,plain,(
% 2.53/1.05    ( ! [X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.53/1.05    inference(cnf_transformation,[],[f60])).
% 2.53/1.05  
% 2.53/1.05  fof(f7,axiom,(
% 2.53/1.05    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 2.53/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.05  
% 2.53/1.05  fof(f28,plain,(
% 2.53/1.05    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 2.53/1.05    inference(ennf_transformation,[],[f7])).
% 2.53/1.05  
% 2.53/1.05  fof(f29,plain,(
% 2.53/1.05    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 2.53/1.05    inference(flattening,[],[f28])).
% 2.53/1.05  
% 2.53/1.05  fof(f77,plain,(
% 2.53/1.05    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 2.53/1.05    inference(cnf_transformation,[],[f29])).
% 2.53/1.05  
% 2.53/1.05  fof(f5,axiom,(
% 2.53/1.05    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.53/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.05  
% 2.53/1.05  fof(f25,plain,(
% 2.53/1.05    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.53/1.05    inference(ennf_transformation,[],[f5])).
% 2.53/1.05  
% 2.53/1.05  fof(f75,plain,(
% 2.53/1.05    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.53/1.05    inference(cnf_transformation,[],[f25])).
% 2.53/1.05  
% 2.53/1.05  fof(f94,plain,(
% 2.53/1.05    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.53/1.05    inference(cnf_transformation,[],[f42])).
% 2.53/1.05  
% 2.53/1.05  cnf(c_24,plain,
% 2.53/1.05      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.53/1.05      | m1_pre_topc(k1_tex_2(X1,X0),X1)
% 2.53/1.05      | v2_struct_0(X1)
% 2.53/1.05      | ~ l1_pre_topc(X1) ),
% 2.53/1.05      inference(cnf_transformation,[],[f92]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3670,plain,
% 2.53/1.05      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 2.53/1.05      | m1_pre_topc(k1_tex_2(X1,X0),X1) = iProver_top
% 2.53/1.05      | v2_struct_0(X1) = iProver_top
% 2.53/1.05      | l1_pre_topc(X1) != iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_19,plain,
% 2.53/1.05      ( v1_tex_2(X0,X1)
% 2.53/1.05      | ~ m1_pre_topc(X0,X1)
% 2.53/1.05      | ~ l1_pre_topc(X1)
% 2.53/1.05      | sK2(X1,X0) = u1_struct_0(X0) ),
% 2.53/1.05      inference(cnf_transformation,[],[f87]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3675,plain,
% 2.53/1.05      ( sK2(X0,X1) = u1_struct_0(X1)
% 2.53/1.05      | v1_tex_2(X1,X0) = iProver_top
% 2.53/1.05      | m1_pre_topc(X1,X0) != iProver_top
% 2.53/1.05      | l1_pre_topc(X0) != iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_5134,plain,
% 2.53/1.05      ( sK2(X0,k1_tex_2(X0,X1)) = u1_struct_0(k1_tex_2(X0,X1))
% 2.53/1.05      | v1_tex_2(k1_tex_2(X0,X1),X0) = iProver_top
% 2.53/1.05      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 2.53/1.05      | v2_struct_0(X0) = iProver_top
% 2.53/1.05      | l1_pre_topc(X0) != iProver_top ),
% 2.53/1.05      inference(superposition,[status(thm)],[c_3670,c_3675]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_11,plain,
% 2.53/1.05      ( ~ m1_subset_1(X0,X1)
% 2.53/1.05      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 2.53/1.05      | v1_xboole_0(X1) ),
% 2.53/1.05      inference(cnf_transformation,[],[f78]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3682,plain,
% 2.53/1.05      ( m1_subset_1(X0,X1) != iProver_top
% 2.53/1.05      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
% 2.53/1.05      | v1_xboole_0(X1) = iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_22,plain,
% 2.53/1.05      ( v1_subset_1(X0,X1)
% 2.53/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.53/1.05      | X1 = X0 ),
% 2.53/1.05      inference(cnf_transformation,[],[f90]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3672,plain,
% 2.53/1.05      ( X0 = X1
% 2.53/1.05      | v1_subset_1(X1,X0) = iProver_top
% 2.53/1.05      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_4565,plain,
% 2.53/1.05      ( k6_domain_1(X0,X1) = X0
% 2.53/1.05      | v1_subset_1(k6_domain_1(X0,X1),X0) = iProver_top
% 2.53/1.05      | m1_subset_1(X1,X0) != iProver_top
% 2.53/1.05      | v1_xboole_0(X0) = iProver_top ),
% 2.53/1.05      inference(superposition,[status(thm)],[c_3682,c_3672]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_29,negated_conjecture,
% 2.53/1.05      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
% 2.53/1.05      | ~ v1_tex_2(k1_tex_2(sK3,sK4),sK3) ),
% 2.53/1.05      inference(cnf_transformation,[],[f100]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3667,plain,
% 2.53/1.05      ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) != iProver_top
% 2.53/1.05      | v1_tex_2(k1_tex_2(sK3,sK4),sK3) != iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_5531,plain,
% 2.53/1.05      ( k6_domain_1(u1_struct_0(sK3),sK4) = u1_struct_0(sK3)
% 2.53/1.05      | v1_tex_2(k1_tex_2(sK3,sK4),sK3) != iProver_top
% 2.53/1.05      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 2.53/1.05      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 2.53/1.05      inference(superposition,[status(thm)],[c_4565,c_3667]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_32,negated_conjecture,
% 2.53/1.05      ( l1_pre_topc(sK3) ),
% 2.53/1.05      inference(cnf_transformation,[],[f97]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_35,plain,
% 2.53/1.05      ( l1_pre_topc(sK3) = iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_31,negated_conjecture,
% 2.53/1.05      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 2.53/1.05      inference(cnf_transformation,[],[f98]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_36,plain,
% 2.53/1.05      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_9,plain,
% 2.53/1.05      ( v7_struct_0(X0)
% 2.53/1.05      | ~ v1_zfmisc_1(u1_struct_0(X0))
% 2.53/1.05      | ~ l1_struct_0(X0) ),
% 2.53/1.05      inference(cnf_transformation,[],[f76]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_92,plain,
% 2.53/1.05      ( v7_struct_0(X0) = iProver_top
% 2.53/1.05      | v1_zfmisc_1(u1_struct_0(X0)) != iProver_top
% 2.53/1.05      | l1_struct_0(X0) != iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_94,plain,
% 2.53/1.05      ( v7_struct_0(sK3) = iProver_top
% 2.53/1.05      | v1_zfmisc_1(u1_struct_0(sK3)) != iProver_top
% 2.53/1.05      | l1_struct_0(sK3) != iProver_top ),
% 2.53/1.05      inference(instantiation,[status(thm)],[c_92]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_7,plain,
% 2.53/1.05      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.53/1.05      inference(cnf_transformation,[],[f74]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_96,plain,
% 2.53/1.05      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_98,plain,
% 2.53/1.05      ( l1_pre_topc(sK3) != iProver_top
% 2.53/1.05      | l1_struct_0(sK3) = iProver_top ),
% 2.53/1.05      inference(instantiation,[status(thm)],[c_96]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_15,plain,
% 2.53/1.05      ( ~ m1_subset_1(X0,X1)
% 2.53/1.05      | v1_zfmisc_1(X1)
% 2.53/1.05      | v1_xboole_0(X1)
% 2.53/1.05      | k6_domain_1(X1,X0) != X1 ),
% 2.53/1.05      inference(cnf_transformation,[],[f84]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3953,plain,
% 2.53/1.05      ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 2.53/1.05      | v1_zfmisc_1(u1_struct_0(sK3))
% 2.53/1.05      | v1_xboole_0(u1_struct_0(sK3))
% 2.53/1.05      | k6_domain_1(u1_struct_0(sK3),sK4) != u1_struct_0(sK3) ),
% 2.53/1.05      inference(instantiation,[status(thm)],[c_15]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3954,plain,
% 2.53/1.05      ( k6_domain_1(u1_struct_0(sK3),sK4) != u1_struct_0(sK3)
% 2.53/1.05      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 2.53/1.05      | v1_zfmisc_1(u1_struct_0(sK3)) = iProver_top
% 2.53/1.05      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_3953]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_30,negated_conjecture,
% 2.53/1.05      ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
% 2.53/1.05      | v1_tex_2(k1_tex_2(sK3,sK4),sK3) ),
% 2.53/1.05      inference(cnf_transformation,[],[f99]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3666,plain,
% 2.53/1.05      ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) = iProver_top
% 2.53/1.05      | v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_28,plain,
% 2.53/1.05      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
% 2.53/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.53/1.05      | v2_struct_0(X0)
% 2.53/1.05      | ~ v7_struct_0(X0)
% 2.53/1.05      | ~ l1_struct_0(X0) ),
% 2.53/1.05      inference(cnf_transformation,[],[f95]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_428,plain,
% 2.53/1.05      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
% 2.53/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.53/1.05      | v2_struct_0(X0)
% 2.53/1.05      | ~ v7_struct_0(X0)
% 2.53/1.05      | ~ l1_pre_topc(X0) ),
% 2.53/1.05      inference(resolution,[status(thm)],[c_7,c_28]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3662,plain,
% 2.53/1.05      ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) != iProver_top
% 2.53/1.05      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 2.53/1.05      | v2_struct_0(X0) = iProver_top
% 2.53/1.05      | v7_struct_0(X0) != iProver_top
% 2.53/1.05      | l1_pre_topc(X0) != iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_428]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_4443,plain,
% 2.53/1.05      ( v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top
% 2.53/1.05      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 2.53/1.05      | v2_struct_0(sK3) = iProver_top
% 2.53/1.05      | v7_struct_0(sK3) != iProver_top
% 2.53/1.05      | l1_pre_topc(sK3) != iProver_top ),
% 2.53/1.05      inference(superposition,[status(thm)],[c_3666,c_3662]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_33,negated_conjecture,
% 2.53/1.05      ( ~ v2_struct_0(sK3) ),
% 2.53/1.05      inference(cnf_transformation,[],[f96]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_34,plain,
% 2.53/1.05      ( v2_struct_0(sK3) != iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_38,plain,
% 2.53/1.05      ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) != iProver_top
% 2.53/1.05      | v1_tex_2(k1_tex_2(sK3,sK4),sK3) != iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_13,plain,
% 2.53/1.05      ( ~ v1_tex_2(X0,X1)
% 2.53/1.05      | ~ m1_pre_topc(X0,X1)
% 2.53/1.05      | v2_struct_0(X1)
% 2.53/1.05      | v2_struct_0(X0)
% 2.53/1.05      | ~ v7_struct_0(X1)
% 2.53/1.05      | ~ l1_pre_topc(X1) ),
% 2.53/1.05      inference(cnf_transformation,[],[f81]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_253,plain,
% 2.53/1.05      ( v1_tex_2(k1_tex_2(sK3,sK4),sK3)
% 2.53/1.05      | v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) ),
% 2.53/1.05      inference(prop_impl,[status(thm)],[c_30]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_254,plain,
% 2.53/1.05      ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
% 2.53/1.05      | v1_tex_2(k1_tex_2(sK3,sK4),sK3) ),
% 2.53/1.05      inference(renaming,[status(thm)],[c_253]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_1505,plain,
% 2.53/1.05      ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
% 2.53/1.05      | ~ m1_pre_topc(X0,X1)
% 2.53/1.05      | v2_struct_0(X1)
% 2.53/1.05      | v2_struct_0(X0)
% 2.53/1.05      | ~ v7_struct_0(X1)
% 2.53/1.05      | ~ l1_pre_topc(X1)
% 2.53/1.05      | k1_tex_2(sK3,sK4) != X0
% 2.53/1.05      | sK3 != X1 ),
% 2.53/1.05      inference(resolution_lifted,[status(thm)],[c_13,c_254]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_1506,plain,
% 2.53/1.05      ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
% 2.53/1.05      | ~ m1_pre_topc(k1_tex_2(sK3,sK4),sK3)
% 2.53/1.05      | v2_struct_0(k1_tex_2(sK3,sK4))
% 2.53/1.05      | v2_struct_0(sK3)
% 2.53/1.05      | ~ v7_struct_0(sK3)
% 2.53/1.05      | ~ l1_pre_topc(sK3) ),
% 2.53/1.05      inference(unflattening,[status(thm)],[c_1505]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_1508,plain,
% 2.53/1.05      ( ~ v7_struct_0(sK3)
% 2.53/1.05      | v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
% 2.53/1.05      | ~ m1_pre_topc(k1_tex_2(sK3,sK4),sK3)
% 2.53/1.05      | v2_struct_0(k1_tex_2(sK3,sK4)) ),
% 2.53/1.05      inference(global_propositional_subsumption,
% 2.53/1.05                [status(thm)],
% 2.53/1.05                [c_1506,c_33,c_32]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_1509,plain,
% 2.53/1.05      ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
% 2.53/1.05      | ~ m1_pre_topc(k1_tex_2(sK3,sK4),sK3)
% 2.53/1.05      | v2_struct_0(k1_tex_2(sK3,sK4))
% 2.53/1.05      | ~ v7_struct_0(sK3) ),
% 2.53/1.05      inference(renaming,[status(thm)],[c_1508]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_1510,plain,
% 2.53/1.05      ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) = iProver_top
% 2.53/1.05      | m1_pre_topc(k1_tex_2(sK3,sK4),sK3) != iProver_top
% 2.53/1.05      | v2_struct_0(k1_tex_2(sK3,sK4)) = iProver_top
% 2.53/1.05      | v7_struct_0(sK3) != iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_1509]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_27,plain,
% 2.53/1.05      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.53/1.05      | v2_struct_0(X1)
% 2.53/1.05      | ~ v2_struct_0(k1_tex_2(X1,X0))
% 2.53/1.05      | ~ l1_pre_topc(X1) ),
% 2.53/1.05      inference(cnf_transformation,[],[f93]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3950,plain,
% 2.53/1.05      ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 2.53/1.05      | ~ v2_struct_0(k1_tex_2(sK3,sK4))
% 2.53/1.05      | v2_struct_0(sK3)
% 2.53/1.05      | ~ l1_pre_topc(sK3) ),
% 2.53/1.05      inference(instantiation,[status(thm)],[c_27]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3951,plain,
% 2.53/1.05      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 2.53/1.05      | v2_struct_0(k1_tex_2(sK3,sK4)) != iProver_top
% 2.53/1.05      | v2_struct_0(sK3) = iProver_top
% 2.53/1.05      | l1_pre_topc(sK3) != iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_3950]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3961,plain,
% 2.53/1.05      ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 2.53/1.05      | m1_pre_topc(k1_tex_2(sK3,sK4),sK3)
% 2.53/1.05      | v2_struct_0(sK3)
% 2.53/1.05      | ~ l1_pre_topc(sK3) ),
% 2.53/1.05      inference(instantiation,[status(thm)],[c_24]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3962,plain,
% 2.53/1.05      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 2.53/1.05      | m1_pre_topc(k1_tex_2(sK3,sK4),sK3) = iProver_top
% 2.53/1.05      | v2_struct_0(sK3) = iProver_top
% 2.53/1.05      | l1_pre_topc(sK3) != iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_3961]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_4633,plain,
% 2.53/1.05      ( v7_struct_0(sK3) != iProver_top ),
% 2.53/1.05      inference(global_propositional_subsumption,
% 2.53/1.05                [status(thm)],
% 2.53/1.05                [c_4443,c_34,c_35,c_36,c_38,c_1510,c_3951,c_3962]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_5555,plain,
% 2.53/1.05      ( v1_tex_2(k1_tex_2(sK3,sK4),sK3) != iProver_top
% 2.53/1.05      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 2.53/1.05      inference(global_propositional_subsumption,
% 2.53/1.05                [status(thm)],
% 2.53/1.05                [c_5531,c_34,c_35,c_36,c_38,c_94,c_98,c_1510,c_3951,
% 2.53/1.05                 c_3954,c_3962,c_4443]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_7373,plain,
% 2.53/1.05      ( sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(k1_tex_2(sK3,sK4))
% 2.53/1.05      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 2.53/1.05      | v2_struct_0(sK3) = iProver_top
% 2.53/1.05      | l1_pre_topc(sK3) != iProver_top
% 2.53/1.05      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 2.53/1.05      inference(superposition,[status(thm)],[c_5134,c_5555]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_7851,plain,
% 2.53/1.05      ( sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(k1_tex_2(sK3,sK4))
% 2.53/1.05      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 2.53/1.05      inference(global_propositional_subsumption,
% 2.53/1.05                [status(thm)],
% 2.53/1.05                [c_7373,c_34,c_35,c_36]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3665,plain,
% 2.53/1.05      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_2,plain,
% 2.53/1.05      ( r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0) ),
% 2.53/1.05      inference(cnf_transformation,[],[f69]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3687,plain,
% 2.53/1.05      ( r1_tarski(X0,X1) = iProver_top
% 2.53/1.05      | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_0,plain,
% 2.53/1.05      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.53/1.05      inference(cnf_transformation,[],[f67]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3689,plain,
% 2.53/1.05      ( r2_hidden(X0,X1) != iProver_top
% 2.53/1.05      | v1_xboole_0(X1) != iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_4014,plain,
% 2.53/1.05      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 2.53/1.05      inference(superposition,[status(thm)],[c_3687,c_3689]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_12,plain,
% 2.53/1.05      ( ~ m1_pre_topc(X0,X1)
% 2.53/1.05      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 2.53/1.05      | ~ l1_pre_topc(X1) ),
% 2.53/1.05      inference(cnf_transformation,[],[f79]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3681,plain,
% 2.53/1.05      ( m1_pre_topc(X0,X1) != iProver_top
% 2.53/1.05      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 2.53/1.05      | l1_pre_topc(X1) != iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_4,plain,
% 2.53/1.05      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.53/1.05      inference(cnf_transformation,[],[f73]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3685,plain,
% 2.53/1.05      ( X0 = X1
% 2.53/1.05      | r1_tarski(X0,X1) != iProver_top
% 2.53/1.05      | r1_tarski(X1,X0) != iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_4531,plain,
% 2.53/1.05      ( u1_struct_0(X0) = u1_struct_0(X1)
% 2.53/1.05      | m1_pre_topc(X0,X1) != iProver_top
% 2.53/1.05      | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
% 2.53/1.05      | l1_pre_topc(X1) != iProver_top ),
% 2.53/1.05      inference(superposition,[status(thm)],[c_3681,c_3685]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_4835,plain,
% 2.53/1.05      ( u1_struct_0(X0) = u1_struct_0(X1)
% 2.53/1.05      | m1_pre_topc(X1,X0) != iProver_top
% 2.53/1.05      | l1_pre_topc(X0) != iProver_top
% 2.53/1.05      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 2.53/1.05      inference(superposition,[status(thm)],[c_4014,c_4531]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_5135,plain,
% 2.53/1.05      ( u1_struct_0(k1_tex_2(X0,X1)) = u1_struct_0(X0)
% 2.53/1.05      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 2.53/1.05      | v2_struct_0(X0) = iProver_top
% 2.53/1.05      | l1_pre_topc(X0) != iProver_top
% 2.53/1.05      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 2.53/1.05      inference(superposition,[status(thm)],[c_3670,c_4835]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_6645,plain,
% 2.53/1.05      ( u1_struct_0(k1_tex_2(sK3,sK4)) = u1_struct_0(sK3)
% 2.53/1.05      | v2_struct_0(sK3) = iProver_top
% 2.53/1.05      | l1_pre_topc(sK3) != iProver_top
% 2.53/1.05      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 2.53/1.05      inference(superposition,[status(thm)],[c_3665,c_5135]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_6712,plain,
% 2.53/1.05      ( u1_struct_0(k1_tex_2(sK3,sK4)) = u1_struct_0(sK3)
% 2.53/1.05      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 2.53/1.05      inference(global_propositional_subsumption,
% 2.53/1.05                [status(thm)],
% 2.53/1.05                [c_6645,c_34,c_35]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_7859,plain,
% 2.53/1.05      ( sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(k1_tex_2(sK3,sK4))
% 2.53/1.05      | u1_struct_0(k1_tex_2(sK3,sK4)) = u1_struct_0(sK3) ),
% 2.53/1.05      inference(superposition,[status(thm)],[c_7851,c_6712]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_20,plain,
% 2.53/1.05      ( v1_tex_2(X0,X1)
% 2.53/1.05      | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.05      | ~ m1_pre_topc(X0,X1)
% 2.53/1.05      | ~ l1_pre_topc(X1) ),
% 2.53/1.05      inference(cnf_transformation,[],[f86]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3674,plain,
% 2.53/1.05      ( v1_tex_2(X0,X1) = iProver_top
% 2.53/1.05      | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 2.53/1.05      | m1_pre_topc(X0,X1) != iProver_top
% 2.53/1.05      | l1_pre_topc(X1) != iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_5292,plain,
% 2.53/1.05      ( sK2(X0,X1) = u1_struct_0(X0)
% 2.53/1.05      | v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) = iProver_top
% 2.53/1.05      | v1_tex_2(X1,X0) = iProver_top
% 2.53/1.05      | m1_pre_topc(X1,X0) != iProver_top
% 2.53/1.05      | l1_pre_topc(X0) != iProver_top ),
% 2.53/1.05      inference(superposition,[status(thm)],[c_3674,c_3672]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_18,plain,
% 2.53/1.05      ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
% 2.53/1.05      | v1_tex_2(X1,X0)
% 2.53/1.05      | ~ m1_pre_topc(X1,X0)
% 2.53/1.05      | ~ l1_pre_topc(X0) ),
% 2.53/1.05      inference(cnf_transformation,[],[f88]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_67,plain,
% 2.53/1.05      ( v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) != iProver_top
% 2.53/1.05      | v1_tex_2(X1,X0) = iProver_top
% 2.53/1.05      | m1_pre_topc(X1,X0) != iProver_top
% 2.53/1.05      | l1_pre_topc(X0) != iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_6721,plain,
% 2.53/1.05      ( sK2(X0,X1) = u1_struct_0(X0)
% 2.53/1.05      | v1_tex_2(X1,X0) = iProver_top
% 2.53/1.05      | m1_pre_topc(X1,X0) != iProver_top
% 2.53/1.05      | l1_pre_topc(X0) != iProver_top ),
% 2.53/1.05      inference(global_propositional_subsumption,
% 2.53/1.05                [status(thm)],
% 2.53/1.05                [c_5292,c_67]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_6729,plain,
% 2.53/1.05      ( sK2(X0,k1_tex_2(X0,X1)) = u1_struct_0(X0)
% 2.53/1.05      | v1_tex_2(k1_tex_2(X0,X1),X0) = iProver_top
% 2.53/1.05      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 2.53/1.05      | v2_struct_0(X0) = iProver_top
% 2.53/1.05      | l1_pre_topc(X0) != iProver_top ),
% 2.53/1.05      inference(superposition,[status(thm)],[c_3670,c_6721]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_7465,plain,
% 2.53/1.05      ( sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(sK3)
% 2.53/1.05      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 2.53/1.05      | v2_struct_0(sK3) = iProver_top
% 2.53/1.05      | l1_pre_topc(sK3) != iProver_top
% 2.53/1.05      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 2.53/1.05      inference(superposition,[status(thm)],[c_6729,c_5555]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_7719,plain,
% 2.53/1.05      ( sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(sK3)
% 2.53/1.05      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 2.53/1.05      inference(global_propositional_subsumption,
% 2.53/1.05                [status(thm)],
% 2.53/1.05                [c_7465,c_34,c_35,c_36]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_7727,plain,
% 2.53/1.05      ( sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(sK3)
% 2.53/1.05      | u1_struct_0(k1_tex_2(sK3,sK4)) = u1_struct_0(sK3) ),
% 2.53/1.05      inference(superposition,[status(thm)],[c_7719,c_6712]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_7878,plain,
% 2.53/1.05      ( u1_struct_0(k1_tex_2(sK3,sK4)) = u1_struct_0(sK3) ),
% 2.53/1.05      inference(superposition,[status(thm)],[c_7859,c_7727]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_10,plain,
% 2.53/1.05      ( ~ v7_struct_0(X0)
% 2.53/1.05      | v1_zfmisc_1(u1_struct_0(X0))
% 2.53/1.05      | ~ l1_struct_0(X0) ),
% 2.53/1.05      inference(cnf_transformation,[],[f77]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_448,plain,
% 2.53/1.05      ( ~ v7_struct_0(X0)
% 2.53/1.05      | v1_zfmisc_1(u1_struct_0(X0))
% 2.53/1.05      | ~ l1_pre_topc(X0) ),
% 2.53/1.05      inference(resolution,[status(thm)],[c_7,c_10]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3661,plain,
% 2.53/1.05      ( v7_struct_0(X0) != iProver_top
% 2.53/1.05      | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top
% 2.53/1.05      | l1_pre_topc(X0) != iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_448]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_8253,plain,
% 2.53/1.05      ( v7_struct_0(k1_tex_2(sK3,sK4)) != iProver_top
% 2.53/1.05      | v1_zfmisc_1(u1_struct_0(sK3)) = iProver_top
% 2.53/1.05      | l1_pre_topc(k1_tex_2(sK3,sK4)) != iProver_top ),
% 2.53/1.05      inference(superposition,[status(thm)],[c_7878,c_3661]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_8,plain,
% 2.53/1.05      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.53/1.05      inference(cnf_transformation,[],[f75]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_4091,plain,
% 2.53/1.05      ( ~ m1_pre_topc(k1_tex_2(sK3,sK4),X0)
% 2.53/1.05      | ~ l1_pre_topc(X0)
% 2.53/1.05      | l1_pre_topc(k1_tex_2(sK3,sK4)) ),
% 2.53/1.05      inference(instantiation,[status(thm)],[c_8]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_4092,plain,
% 2.53/1.05      ( m1_pre_topc(k1_tex_2(sK3,sK4),X0) != iProver_top
% 2.53/1.05      | l1_pre_topc(X0) != iProver_top
% 2.53/1.05      | l1_pre_topc(k1_tex_2(sK3,sK4)) = iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_4091]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_4094,plain,
% 2.53/1.05      ( m1_pre_topc(k1_tex_2(sK3,sK4),sK3) != iProver_top
% 2.53/1.05      | l1_pre_topc(k1_tex_2(sK3,sK4)) = iProver_top
% 2.53/1.05      | l1_pre_topc(sK3) != iProver_top ),
% 2.53/1.05      inference(instantiation,[status(thm)],[c_4092]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_26,plain,
% 2.53/1.05      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.53/1.05      | v2_struct_0(X1)
% 2.53/1.05      | v7_struct_0(k1_tex_2(X1,X0))
% 2.53/1.05      | ~ l1_pre_topc(X1) ),
% 2.53/1.05      inference(cnf_transformation,[],[f94]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3947,plain,
% 2.53/1.05      ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 2.53/1.05      | v2_struct_0(sK3)
% 2.53/1.05      | v7_struct_0(k1_tex_2(sK3,sK4))
% 2.53/1.05      | ~ l1_pre_topc(sK3) ),
% 2.53/1.05      inference(instantiation,[status(thm)],[c_26]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(c_3948,plain,
% 2.53/1.05      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 2.53/1.05      | v2_struct_0(sK3) = iProver_top
% 2.53/1.05      | v7_struct_0(k1_tex_2(sK3,sK4)) = iProver_top
% 2.53/1.05      | l1_pre_topc(sK3) != iProver_top ),
% 2.53/1.05      inference(predicate_to_equality,[status(thm)],[c_3947]) ).
% 2.53/1.05  
% 2.53/1.05  cnf(contradiction,plain,
% 2.53/1.05      ( $false ),
% 2.53/1.05      inference(minisat,
% 2.53/1.05                [status(thm)],
% 2.53/1.05                [c_8253,c_4633,c_4094,c_3962,c_3948,c_98,c_94,c_36,c_35,
% 2.53/1.05                 c_34]) ).
% 2.53/1.05  
% 2.53/1.05  
% 2.53/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 2.53/1.05  
% 2.53/1.05  ------                               Statistics
% 2.53/1.05  
% 2.53/1.05  ------ General
% 2.53/1.05  
% 2.53/1.05  abstr_ref_over_cycles:                  0
% 2.53/1.05  abstr_ref_under_cycles:                 0
% 2.53/1.05  gc_basic_clause_elim:                   0
% 2.53/1.05  forced_gc_time:                         0
% 2.53/1.05  parsing_time:                           0.014
% 2.53/1.05  unif_index_cands_time:                  0.
% 2.53/1.05  unif_index_add_time:                    0.
% 2.53/1.05  orderings_time:                         0.
% 2.53/1.05  out_proof_time:                         0.026
% 2.53/1.05  total_time:                             0.322
% 2.53/1.05  num_of_symbols:                         52
% 2.53/1.05  num_of_terms:                           3848
% 2.53/1.05  
% 2.53/1.05  ------ Preprocessing
% 2.53/1.05  
% 2.53/1.05  num_of_splits:                          0
% 2.53/1.05  num_of_split_atoms:                     0
% 2.53/1.05  num_of_reused_defs:                     0
% 2.53/1.05  num_eq_ax_congr_red:                    25
% 2.53/1.05  num_of_sem_filtered_clauses:            1
% 2.53/1.05  num_of_subtypes:                        0
% 2.53/1.05  monotx_restored_types:                  0
% 2.53/1.05  sat_num_of_epr_types:                   0
% 2.53/1.05  sat_num_of_non_cyclic_types:            0
% 2.53/1.05  sat_guarded_non_collapsed_types:        0
% 2.53/1.05  num_pure_diseq_elim:                    0
% 2.53/1.05  simp_replaced_by:                       0
% 2.53/1.05  res_preprocessed:                       154
% 2.53/1.05  prep_upred:                             0
% 2.53/1.05  prep_unflattend:                        98
% 2.53/1.05  smt_new_axioms:                         0
% 2.53/1.05  pred_elim_cands:                        11
% 2.53/1.05  pred_elim:                              1
% 2.53/1.05  pred_elim_cl:                           1
% 2.53/1.05  pred_elim_cycles:                       13
% 2.53/1.05  merged_defs:                            8
% 2.53/1.05  merged_defs_ncl:                        0
% 2.53/1.05  bin_hyper_res:                          8
% 2.53/1.05  prep_cycles:                            4
% 2.53/1.05  pred_elim_time:                         0.038
% 2.53/1.05  splitting_time:                         0.
% 2.53/1.05  sem_filter_time:                        0.
% 2.53/1.05  monotx_time:                            0.
% 2.53/1.05  subtype_inf_time:                       0.
% 2.53/1.05  
% 2.53/1.05  ------ Problem properties
% 2.53/1.05  
% 2.53/1.05  clauses:                                30
% 2.53/1.05  conjectures:                            5
% 2.53/1.05  epr:                                    8
% 2.53/1.05  horn:                                   18
% 2.53/1.05  ground:                                 5
% 2.53/1.05  unary:                                  4
% 2.53/1.05  binary:                                 6
% 2.53/1.05  lits:                                   90
% 2.53/1.05  lits_eq:                                5
% 2.53/1.05  fd_pure:                                0
% 2.53/1.05  fd_pseudo:                              0
% 2.53/1.05  fd_cond:                                0
% 2.53/1.05  fd_pseudo_cond:                         2
% 2.53/1.05  ac_symbols:                             0
% 2.53/1.05  
% 2.53/1.05  ------ Propositional Solver
% 2.53/1.05  
% 2.53/1.05  prop_solver_calls:                      30
% 2.53/1.05  prop_fast_solver_calls:                 1851
% 2.53/1.05  smt_solver_calls:                       0
% 2.53/1.05  smt_fast_solver_calls:                  0
% 2.53/1.05  prop_num_of_clauses:                    1766
% 2.53/1.05  prop_preprocess_simplified:             7051
% 2.53/1.05  prop_fo_subsumed:                       48
% 2.53/1.05  prop_solver_time:                       0.
% 2.53/1.05  smt_solver_time:                        0.
% 2.53/1.05  smt_fast_solver_time:                   0.
% 2.53/1.05  prop_fast_solver_time:                  0.
% 2.53/1.05  prop_unsat_core_time:                   0.
% 2.53/1.05  
% 2.53/1.05  ------ QBF
% 2.53/1.05  
% 2.53/1.05  qbf_q_res:                              0
% 2.53/1.05  qbf_num_tautologies:                    0
% 2.53/1.05  qbf_prep_cycles:                        0
% 2.53/1.05  
% 2.53/1.05  ------ BMC1
% 2.53/1.05  
% 2.53/1.05  bmc1_current_bound:                     -1
% 2.53/1.05  bmc1_last_solved_bound:                 -1
% 2.53/1.05  bmc1_unsat_core_size:                   -1
% 2.53/1.05  bmc1_unsat_core_parents_size:           -1
% 2.53/1.05  bmc1_merge_next_fun:                    0
% 2.53/1.05  bmc1_unsat_core_clauses_time:           0.
% 2.53/1.05  
% 2.53/1.05  ------ Instantiation
% 2.53/1.05  
% 2.53/1.05  inst_num_of_clauses:                    487
% 2.53/1.05  inst_num_in_passive:                    71
% 2.53/1.05  inst_num_in_active:                     320
% 2.53/1.05  inst_num_in_unprocessed:                96
% 2.53/1.05  inst_num_of_loops:                      410
% 2.53/1.05  inst_num_of_learning_restarts:          0
% 2.53/1.05  inst_num_moves_active_passive:          85
% 2.53/1.05  inst_lit_activity:                      0
% 2.53/1.05  inst_lit_activity_moves:                0
% 2.53/1.05  inst_num_tautologies:                   0
% 2.53/1.05  inst_num_prop_implied:                  0
% 2.53/1.05  inst_num_existing_simplified:           0
% 2.53/1.05  inst_num_eq_res_simplified:             0
% 2.53/1.05  inst_num_child_elim:                    0
% 2.53/1.05  inst_num_of_dismatching_blockings:      213
% 2.53/1.05  inst_num_of_non_proper_insts:           625
% 2.53/1.05  inst_num_of_duplicates:                 0
% 2.53/1.05  inst_inst_num_from_inst_to_res:         0
% 2.53/1.05  inst_dismatching_checking_time:         0.
% 2.53/1.05  
% 2.53/1.05  ------ Resolution
% 2.53/1.05  
% 2.53/1.05  res_num_of_clauses:                     0
% 2.53/1.05  res_num_in_passive:                     0
% 2.53/1.05  res_num_in_active:                      0
% 2.53/1.05  res_num_of_loops:                       158
% 2.53/1.05  res_forward_subset_subsumed:            79
% 2.53/1.05  res_backward_subset_subsumed:           8
% 2.53/1.05  res_forward_subsumed:                   0
% 2.53/1.05  res_backward_subsumed:                  0
% 2.53/1.05  res_forward_subsumption_resolution:     3
% 2.53/1.05  res_backward_subsumption_resolution:    0
% 2.53/1.05  res_clause_to_clause_subsumption:       830
% 2.53/1.05  res_orphan_elimination:                 0
% 2.53/1.05  res_tautology_del:                      97
% 2.53/1.05  res_num_eq_res_simplified:              0
% 2.53/1.05  res_num_sel_changes:                    0
% 2.53/1.05  res_moves_from_active_to_pass:          0
% 2.53/1.05  
% 2.53/1.05  ------ Superposition
% 2.53/1.05  
% 2.53/1.05  sup_time_total:                         0.
% 2.53/1.05  sup_time_generating:                    0.
% 2.53/1.05  sup_time_sim_full:                      0.
% 2.53/1.05  sup_time_sim_immed:                     0.
% 2.53/1.05  
% 2.53/1.05  sup_num_of_clauses:                     106
% 2.53/1.05  sup_num_in_active:                      64
% 2.53/1.05  sup_num_in_passive:                     42
% 2.53/1.05  sup_num_of_loops:                       80
% 2.53/1.05  sup_fw_superposition:                   50
% 2.53/1.05  sup_bw_superposition:                   75
% 2.53/1.05  sup_immediate_simplified:               22
% 2.53/1.05  sup_given_eliminated:                   1
% 2.53/1.05  comparisons_done:                       0
% 2.53/1.05  comparisons_avoided:                    101
% 2.53/1.05  
% 2.53/1.05  ------ Simplifications
% 2.53/1.05  
% 2.53/1.05  
% 2.53/1.05  sim_fw_subset_subsumed:                 8
% 2.53/1.05  sim_bw_subset_subsumed:                 3
% 2.53/1.05  sim_fw_subsumed:                        6
% 2.53/1.05  sim_bw_subsumed:                        0
% 2.53/1.05  sim_fw_subsumption_res:                 0
% 2.53/1.05  sim_bw_subsumption_res:                 0
% 2.53/1.05  sim_tautology_del:                      4
% 2.53/1.05  sim_eq_tautology_del:                   10
% 2.53/1.05  sim_eq_res_simp:                        0
% 2.53/1.05  sim_fw_demodulated:                     3
% 2.53/1.05  sim_bw_demodulated:                     16
% 2.53/1.05  sim_light_normalised:                   9
% 2.53/1.05  sim_joinable_taut:                      0
% 2.53/1.05  sim_joinable_simp:                      0
% 2.53/1.05  sim_ac_normalised:                      0
% 2.53/1.05  sim_smt_subsumption:                    0
% 2.53/1.05  
%------------------------------------------------------------------------------
