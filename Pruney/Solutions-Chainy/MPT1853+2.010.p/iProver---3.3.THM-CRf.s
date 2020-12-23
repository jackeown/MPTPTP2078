%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:36 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :  188 (1011 expanded)
%              Number of clauses        :  113 ( 339 expanded)
%              Number of leaves         :   18 ( 190 expanded)
%              Depth                    :   22
%              Number of atoms          :  724 (4846 expanded)
%              Number of equality atoms :  220 ( 576 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
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

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK1(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK1(X0,X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ( ~ v1_subset_1(sK1(X0,X1),u1_struct_0(X0))
                & u1_struct_0(X1) = sK1(X0,X1)
                & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f46,f47])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK1(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f55,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK0(X0)) = X0
        & m1_subset_1(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK0(X0)) = X0
            & m1_subset_1(sK0(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X0)
      | k6_domain_1(X0,X1) != X0
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),sK3),u1_struct_0(X0))
          | ~ v1_tex_2(k1_tex_2(X0,sK3),X0) )
        & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),sK3),u1_struct_0(X0))
          | v1_tex_2(k1_tex_2(X0,sK3),X0) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
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
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),X1),u1_struct_0(sK2))
            | ~ v1_tex_2(k1_tex_2(sK2,X1),sK2) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),X1),u1_struct_0(sK2))
            | v1_tex_2(k1_tex_2(sK2,X1),sK2) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
      | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
      | v1_tex_2(k1_tex_2(sK2,sK3),sK2) )
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f51,f53,f52])).

fof(f81,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f78,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f79,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f54])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f56,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f80,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v7_struct_0(X0)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f77,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f7,axiom,(
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

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(sK1(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f59,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f57,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v7_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_pre_topc(k1_tex_2(X1,X0),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2473,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
    | m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47)
    | v2_struct_0(X0_47)
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_3088,plain,
    ( m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
    | m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47) = iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2473])).

cnf(c_12,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2478,plain,
    ( v1_tex_2(X0_47,X1_47)
    | ~ m1_pre_topc(X0_47,X1_47)
    | ~ l1_pre_topc(X1_47)
    | sK1(X1_47,X0_47) = u1_struct_0(X0_47) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_3083,plain,
    ( sK1(X0_47,X1_47) = u1_struct_0(X1_47)
    | v1_tex_2(X1_47,X0_47) = iProver_top
    | m1_pre_topc(X1_47,X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2478])).

cnf(c_3503,plain,
    ( sK1(X0_47,k1_tex_2(X0_47,X0_46)) = u1_struct_0(k1_tex_2(X0_47,X0_46))
    | v1_tex_2(k1_tex_2(X0_47,X0_46),X0_47) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_3088,c_3083])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | v1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_428,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_zfmisc_1(X2)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_5])).

cnf(c_429,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_2461,plain,
    ( ~ m1_subset_1(X0_46,X1_46)
    | m1_subset_1(k6_domain_1(X1_46,X0_46),k1_zfmisc_1(X1_46))
    | v1_zfmisc_1(X1_46) ),
    inference(subtyping,[status(esa)],[c_429])).

cnf(c_3100,plain,
    ( m1_subset_1(X0_46,X1_46) != iProver_top
    | m1_subset_1(k6_domain_1(X1_46,X0_46),k1_zfmisc_1(X1_46)) = iProver_top
    | v1_zfmisc_1(X1_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2461])).

cnf(c_15,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2475,plain,
    ( v1_subset_1(X0_46,X1_46)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
    | X0_46 = X1_46 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_3086,plain,
    ( X0_46 = X1_46
    | v1_subset_1(X0_46,X1_46) = iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(X1_46)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2475])).

cnf(c_4194,plain,
    ( k6_domain_1(X0_46,X1_46) = X0_46
    | v1_subset_1(k6_domain_1(X0_46,X1_46),X0_46) = iProver_top
    | m1_subset_1(X1_46,X0_46) != iProver_top
    | v1_zfmisc_1(X0_46) = iProver_top ),
    inference(superposition,[status(thm)],[c_3100,c_3086])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | v1_zfmisc_1(X1)
    | k6_domain_1(X1,X0) != X1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_413,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_zfmisc_1(X2)
    | v1_zfmisc_1(X1)
    | X1 != X2
    | k6_domain_1(X1,X0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_8])).

cnf(c_414,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_zfmisc_1(X1)
    | k6_domain_1(X1,X0) != X1 ),
    inference(unflattening,[status(thm)],[c_413])).

cnf(c_2462,plain,
    ( ~ m1_subset_1(X0_46,X1_46)
    | v1_zfmisc_1(X1_46)
    | k6_domain_1(X1_46,X0_46) != X1_46 ),
    inference(subtyping,[status(esa)],[c_414])).

cnf(c_2544,plain,
    ( k6_domain_1(X0_46,X1_46) != X0_46
    | m1_subset_1(X1_46,X0_46) != iProver_top
    | v1_zfmisc_1(X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2462])).

cnf(c_4199,plain,
    ( v1_subset_1(k6_domain_1(X0_46,X1_46),X0_46) = iProver_top
    | m1_subset_1(X1_46,X0_46) != iProver_top
    | v1_zfmisc_1(X0_46) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4194,c_2544])).

cnf(c_22,negated_conjecture,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2470,negated_conjecture,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_3091,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2470])).

cnf(c_4208,plain,
    ( v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4199,c_3091])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_28,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_29,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_31,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3,plain,
    ( v7_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_zfmisc_1(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_82,plain,
    ( v7_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_84,plain,
    ( v7_struct_0(sK2) = iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_82])).

cnf(c_1,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_86,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_88,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_struct_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_86])).

cnf(c_3289,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2461])).

cnf(c_3290,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3289])).

cnf(c_3292,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v1_zfmisc_1(u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK3) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2462])).

cnf(c_3293,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) != u1_struct_0(sK2)
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3292])).

cnf(c_3372,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | k6_domain_1(u1_struct_0(sK2),sK3) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2475])).

cnf(c_3373,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) = u1_struct_0(sK2)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3372])).

cnf(c_23,negated_conjecture,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2469,negated_conjecture,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_3092,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) = iProver_top
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2469])).

cnf(c_21,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v7_struct_0(X0)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_349,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v7_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_1,c_21])).

cnf(c_2465,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0_47),X0_46),u1_struct_0(X0_47))
    | ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
    | v2_struct_0(X0_47)
    | ~ v7_struct_0(X0_47)
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_349])).

cnf(c_3096,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(X0_47),X0_46),u1_struct_0(X0_47)) != iProver_top
    | m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | v7_struct_0(X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2465])).

cnf(c_4089,plain,
    ( v1_tex_2(k1_tex_2(sK2,sK3),sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v7_struct_0(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3092,c_3096])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_27,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_6,plain,
    ( ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v7_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_204,plain,
    ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(prop_impl,[status(thm)],[c_23])).

cnf(c_205,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(renaming,[status(thm)],[c_204])).

cnf(c_1317,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v7_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k1_tex_2(sK2,sK3) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_205])).

cnf(c_1318,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | v2_struct_0(k1_tex_2(sK2,sK3))
    | v2_struct_0(sK2)
    | ~ v7_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1317])).

cnf(c_1320,plain,
    ( ~ v7_struct_0(sK2)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | v2_struct_0(k1_tex_2(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1318,c_26,c_25])).

cnf(c_1321,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | v2_struct_0(k1_tex_2(sK2,sK3))
    | ~ v7_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_1320])).

cnf(c_1322,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) = iProver_top
    | m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | v2_struct_0(k1_tex_2(sK2,sK3)) = iProver_top
    | v7_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1321])).

cnf(c_2525,plain,
    ( m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
    | m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47) = iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2473])).

cnf(c_2527,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(k1_tex_2(sK2,sK3),sK2) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2525])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2472,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
    | v2_struct_0(X0_47)
    | ~ v2_struct_0(k1_tex_2(X0_47,X0_46))
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_2528,plain,
    ( m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | v2_struct_0(k1_tex_2(X0_47,X0_46)) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2472])).

cnf(c_2530,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(k1_tex_2(sK2,sK3)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2528])).

cnf(c_2539,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(X0_47),X0_46),u1_struct_0(X0_47)) != iProver_top
    | m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | v7_struct_0(X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2465])).

cnf(c_2541,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v7_struct_0(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2539])).

cnf(c_4092,plain,
    ( v7_struct_0(sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4089,c_27,c_28,c_29,c_1322,c_2527,c_2530,c_2541])).

cnf(c_4285,plain,
    ( v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4208,c_27,c_28,c_29,c_31,c_84,c_88,c_1322,c_2527,c_2530,c_2541,c_3290,c_3293,c_3373])).

cnf(c_4512,plain,
    ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3503,c_4285])).

cnf(c_13,plain,
    ( v1_tex_2(X0,X1)
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2477,plain,
    ( v1_tex_2(X0_47,X1_47)
    | m1_subset_1(sK1(X1_47,X0_47),k1_zfmisc_1(u1_struct_0(X1_47)))
    | ~ m1_pre_topc(X0_47,X1_47)
    | ~ l1_pre_topc(X1_47) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_3084,plain,
    ( v1_tex_2(X0_47,X1_47) = iProver_top
    | m1_subset_1(sK1(X1_47,X0_47),k1_zfmisc_1(u1_struct_0(X1_47))) = iProver_top
    | m1_pre_topc(X0_47,X1_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2477])).

cnf(c_3806,plain,
    ( sK1(X0_47,X1_47) = u1_struct_0(X0_47)
    | v1_subset_1(sK1(X0_47,X1_47),u1_struct_0(X0_47)) = iProver_top
    | v1_tex_2(X1_47,X0_47) = iProver_top
    | m1_pre_topc(X1_47,X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_3084,c_3086])).

cnf(c_11,plain,
    ( ~ v1_subset_1(sK1(X0,X1),u1_struct_0(X0))
    | v1_tex_2(X1,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2479,plain,
    ( ~ v1_subset_1(sK1(X0_47,X1_47),u1_struct_0(X0_47))
    | v1_tex_2(X1_47,X0_47)
    | ~ m1_pre_topc(X1_47,X0_47)
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_2515,plain,
    ( v1_subset_1(sK1(X0_47,X1_47),u1_struct_0(X0_47)) != iProver_top
    | v1_tex_2(X1_47,X0_47) = iProver_top
    | m1_pre_topc(X1_47,X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2479])).

cnf(c_4006,plain,
    ( sK1(X0_47,X1_47) = u1_struct_0(X0_47)
    | v1_tex_2(X1_47,X0_47) = iProver_top
    | m1_pre_topc(X1_47,X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3806,c_2515])).

cnf(c_4014,plain,
    ( sK1(X0_47,k1_tex_2(X0_47,X0_46)) = u1_struct_0(X0_47)
    | v1_tex_2(k1_tex_2(X0_47,X0_46),X0_47) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_3088,c_4006])).

cnf(c_4296,plain,
    ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(sK2)
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4014,c_4285])).

cnf(c_202,plain,
    ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(prop_impl,[status(thm)],[c_22])).

cnf(c_203,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(renaming,[status(thm)],[c_202])).

cnf(c_1246,plain,
    ( ~ v1_subset_1(sK1(X0,X1),u1_struct_0(X0))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | k1_tex_2(sK2,sK3) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_203])).

cnf(c_1247,plain,
    ( ~ v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1246])).

cnf(c_1248,plain,
    ( v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1247])).

cnf(c_1263,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | k1_tex_2(sK2,sK3) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_203])).

cnf(c_1264,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1263])).

cnf(c_1265,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1264])).

cnf(c_3388,plain,
    ( v1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
    | X0_46 = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2475])).

cnf(c_3667,plain,
    ( v1_subset_1(sK1(sK2,k1_tex_2(sK2,X0_46)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK1(sK2,k1_tex_2(sK2,X0_46)),k1_zfmisc_1(u1_struct_0(sK2)))
    | sK1(sK2,k1_tex_2(sK2,X0_46)) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3388])).

cnf(c_3670,plain,
    ( sK1(sK2,k1_tex_2(sK2,X0_46)) = u1_struct_0(sK2)
    | v1_subset_1(sK1(sK2,k1_tex_2(sK2,X0_46)),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK1(sK2,k1_tex_2(sK2,X0_46)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3667])).

cnf(c_3672,plain,
    ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(sK2)
    | v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3670])).

cnf(c_4412,plain,
    ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4296,c_27,c_28,c_29,c_84,c_88,c_1248,c_1265,c_1322,c_2527,c_2530,c_2541,c_3290,c_3293,c_3373,c_3672])).

cnf(c_4532,plain,
    ( u1_struct_0(k1_tex_2(sK2,sK3)) = u1_struct_0(sK2)
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4512,c_4412])).

cnf(c_4753,plain,
    ( u1_struct_0(k1_tex_2(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4532,c_27,c_28,c_29])).

cnf(c_4,plain,
    ( ~ v7_struct_0(X0)
    | ~ l1_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_369,plain,
    ( ~ v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_zfmisc_1(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_1,c_4])).

cnf(c_2464,plain,
    ( ~ v7_struct_0(X0_47)
    | ~ l1_pre_topc(X0_47)
    | v1_zfmisc_1(u1_struct_0(X0_47)) ),
    inference(subtyping,[status(esa)],[c_369])).

cnf(c_3097,plain,
    ( v7_struct_0(X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X0_47)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2464])).

cnf(c_4765,plain,
    ( v7_struct_0(k1_tex_2(sK2,sK3)) != iProver_top
    | l1_pre_topc(k1_tex_2(sK2,sK3)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4753,c_3097])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2481,plain,
    ( ~ m1_pre_topc(X0_47,X1_47)
    | ~ l1_pre_topc(X1_47)
    | l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_3411,plain,
    ( ~ m1_pre_topc(k1_tex_2(X0_47,X0_46),X1_47)
    | ~ l1_pre_topc(X1_47)
    | l1_pre_topc(k1_tex_2(X0_47,X0_46)) ),
    inference(instantiation,[status(thm)],[c_2481])).

cnf(c_3412,plain,
    ( m1_pre_topc(k1_tex_2(X0_47,X0_46),X1_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top
    | l1_pre_topc(k1_tex_2(X0_47,X0_46)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3411])).

cnf(c_3414,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | l1_pre_topc(k1_tex_2(sK2,sK3)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3412])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v7_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2471,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
    | v2_struct_0(X0_47)
    | v7_struct_0(k1_tex_2(X0_47,X0_46))
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_2531,plain,
    ( m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | v7_struct_0(k1_tex_2(X0_47,X0_46)) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2471])).

cnf(c_2533,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v7_struct_0(k1_tex_2(sK2,sK3)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2531])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4765,c_4092,c_3414,c_2533,c_2527,c_88,c_84,c_29,c_28,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:12:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.85/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.01  
% 1.85/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.85/1.01  
% 1.85/1.01  ------  iProver source info
% 1.85/1.01  
% 1.85/1.01  git: date: 2020-06-30 10:37:57 +0100
% 1.85/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.85/1.01  git: non_committed_changes: false
% 1.85/1.01  git: last_make_outside_of_git: false
% 1.85/1.01  
% 1.85/1.01  ------ 
% 1.85/1.01  
% 1.85/1.01  ------ Input Options
% 1.85/1.01  
% 1.85/1.01  --out_options                           all
% 1.85/1.01  --tptp_safe_out                         true
% 1.85/1.01  --problem_path                          ""
% 1.85/1.01  --include_path                          ""
% 1.85/1.01  --clausifier                            res/vclausify_rel
% 1.85/1.01  --clausifier_options                    --mode clausify
% 1.85/1.01  --stdin                                 false
% 1.85/1.01  --stats_out                             all
% 1.85/1.01  
% 1.85/1.01  ------ General Options
% 1.85/1.01  
% 1.85/1.01  --fof                                   false
% 1.85/1.01  --time_out_real                         305.
% 1.85/1.01  --time_out_virtual                      -1.
% 1.85/1.01  --symbol_type_check                     false
% 1.85/1.01  --clausify_out                          false
% 1.85/1.01  --sig_cnt_out                           false
% 1.85/1.01  --trig_cnt_out                          false
% 1.85/1.01  --trig_cnt_out_tolerance                1.
% 1.85/1.01  --trig_cnt_out_sk_spl                   false
% 1.85/1.01  --abstr_cl_out                          false
% 1.85/1.01  
% 1.85/1.01  ------ Global Options
% 1.85/1.01  
% 1.85/1.01  --schedule                              default
% 1.85/1.01  --add_important_lit                     false
% 1.85/1.01  --prop_solver_per_cl                    1000
% 1.85/1.01  --min_unsat_core                        false
% 1.85/1.01  --soft_assumptions                      false
% 1.85/1.01  --soft_lemma_size                       3
% 1.85/1.01  --prop_impl_unit_size                   0
% 1.85/1.01  --prop_impl_unit                        []
% 1.85/1.01  --share_sel_clauses                     true
% 1.85/1.01  --reset_solvers                         false
% 1.85/1.01  --bc_imp_inh                            [conj_cone]
% 1.85/1.01  --conj_cone_tolerance                   3.
% 1.85/1.01  --extra_neg_conj                        none
% 1.85/1.01  --large_theory_mode                     true
% 1.85/1.01  --prolific_symb_bound                   200
% 1.85/1.01  --lt_threshold                          2000
% 1.85/1.01  --clause_weak_htbl                      true
% 1.85/1.01  --gc_record_bc_elim                     false
% 1.85/1.01  
% 1.85/1.01  ------ Preprocessing Options
% 1.85/1.01  
% 1.85/1.01  --preprocessing_flag                    true
% 1.85/1.01  --time_out_prep_mult                    0.1
% 1.85/1.01  --splitting_mode                        input
% 1.85/1.01  --splitting_grd                         true
% 1.85/1.01  --splitting_cvd                         false
% 1.85/1.01  --splitting_cvd_svl                     false
% 1.85/1.01  --splitting_nvd                         32
% 1.85/1.01  --sub_typing                            true
% 1.85/1.01  --prep_gs_sim                           true
% 1.85/1.01  --prep_unflatten                        true
% 1.85/1.01  --prep_res_sim                          true
% 1.85/1.01  --prep_upred                            true
% 1.85/1.01  --prep_sem_filter                       exhaustive
% 1.85/1.01  --prep_sem_filter_out                   false
% 1.85/1.01  --pred_elim                             true
% 1.85/1.01  --res_sim_input                         true
% 1.85/1.01  --eq_ax_congr_red                       true
% 1.85/1.01  --pure_diseq_elim                       true
% 1.85/1.01  --brand_transform                       false
% 1.85/1.01  --non_eq_to_eq                          false
% 1.85/1.01  --prep_def_merge                        true
% 1.85/1.01  --prep_def_merge_prop_impl              false
% 1.85/1.01  --prep_def_merge_mbd                    true
% 1.85/1.01  --prep_def_merge_tr_red                 false
% 1.85/1.01  --prep_def_merge_tr_cl                  false
% 1.85/1.01  --smt_preprocessing                     true
% 1.85/1.01  --smt_ac_axioms                         fast
% 1.85/1.01  --preprocessed_out                      false
% 1.85/1.01  --preprocessed_stats                    false
% 1.85/1.01  
% 1.85/1.01  ------ Abstraction refinement Options
% 1.85/1.01  
% 1.85/1.01  --abstr_ref                             []
% 1.85/1.01  --abstr_ref_prep                        false
% 1.85/1.01  --abstr_ref_until_sat                   false
% 1.85/1.01  --abstr_ref_sig_restrict                funpre
% 1.85/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.85/1.01  --abstr_ref_under                       []
% 1.85/1.01  
% 1.85/1.01  ------ SAT Options
% 1.85/1.01  
% 1.85/1.01  --sat_mode                              false
% 1.85/1.01  --sat_fm_restart_options                ""
% 1.85/1.01  --sat_gr_def                            false
% 1.85/1.01  --sat_epr_types                         true
% 1.85/1.01  --sat_non_cyclic_types                  false
% 1.85/1.01  --sat_finite_models                     false
% 1.85/1.01  --sat_fm_lemmas                         false
% 1.85/1.01  --sat_fm_prep                           false
% 1.85/1.01  --sat_fm_uc_incr                        true
% 1.85/1.01  --sat_out_model                         small
% 1.85/1.01  --sat_out_clauses                       false
% 1.85/1.01  
% 1.85/1.01  ------ QBF Options
% 1.85/1.01  
% 1.85/1.01  --qbf_mode                              false
% 1.85/1.01  --qbf_elim_univ                         false
% 1.85/1.01  --qbf_dom_inst                          none
% 1.85/1.01  --qbf_dom_pre_inst                      false
% 1.85/1.01  --qbf_sk_in                             false
% 1.85/1.01  --qbf_pred_elim                         true
% 1.85/1.01  --qbf_split                             512
% 1.85/1.01  
% 1.85/1.01  ------ BMC1 Options
% 1.85/1.01  
% 1.85/1.01  --bmc1_incremental                      false
% 1.85/1.01  --bmc1_axioms                           reachable_all
% 1.85/1.01  --bmc1_min_bound                        0
% 1.85/1.01  --bmc1_max_bound                        -1
% 1.85/1.01  --bmc1_max_bound_default                -1
% 1.85/1.01  --bmc1_symbol_reachability              true
% 1.85/1.01  --bmc1_property_lemmas                  false
% 1.85/1.01  --bmc1_k_induction                      false
% 1.85/1.01  --bmc1_non_equiv_states                 false
% 1.85/1.01  --bmc1_deadlock                         false
% 1.85/1.01  --bmc1_ucm                              false
% 1.85/1.01  --bmc1_add_unsat_core                   none
% 1.85/1.01  --bmc1_unsat_core_children              false
% 1.85/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.85/1.01  --bmc1_out_stat                         full
% 1.85/1.01  --bmc1_ground_init                      false
% 1.85/1.01  --bmc1_pre_inst_next_state              false
% 1.85/1.01  --bmc1_pre_inst_state                   false
% 1.85/1.01  --bmc1_pre_inst_reach_state             false
% 1.85/1.01  --bmc1_out_unsat_core                   false
% 1.85/1.01  --bmc1_aig_witness_out                  false
% 1.85/1.01  --bmc1_verbose                          false
% 1.85/1.01  --bmc1_dump_clauses_tptp                false
% 1.85/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.85/1.01  --bmc1_dump_file                        -
% 1.85/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.85/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.85/1.01  --bmc1_ucm_extend_mode                  1
% 1.85/1.01  --bmc1_ucm_init_mode                    2
% 1.85/1.01  --bmc1_ucm_cone_mode                    none
% 1.85/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.85/1.01  --bmc1_ucm_relax_model                  4
% 1.85/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.85/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.85/1.01  --bmc1_ucm_layered_model                none
% 1.85/1.01  --bmc1_ucm_max_lemma_size               10
% 1.85/1.01  
% 1.85/1.01  ------ AIG Options
% 1.85/1.01  
% 1.85/1.01  --aig_mode                              false
% 1.85/1.01  
% 1.85/1.01  ------ Instantiation Options
% 1.85/1.01  
% 1.85/1.01  --instantiation_flag                    true
% 1.85/1.01  --inst_sos_flag                         false
% 1.85/1.01  --inst_sos_phase                        true
% 1.85/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.85/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.85/1.01  --inst_lit_sel_side                     num_symb
% 1.85/1.01  --inst_solver_per_active                1400
% 1.85/1.01  --inst_solver_calls_frac                1.
% 1.85/1.01  --inst_passive_queue_type               priority_queues
% 1.85/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.85/1.01  --inst_passive_queues_freq              [25;2]
% 1.85/1.01  --inst_dismatching                      true
% 1.85/1.01  --inst_eager_unprocessed_to_passive     true
% 1.85/1.01  --inst_prop_sim_given                   true
% 1.85/1.01  --inst_prop_sim_new                     false
% 1.85/1.01  --inst_subs_new                         false
% 1.85/1.01  --inst_eq_res_simp                      false
% 1.85/1.01  --inst_subs_given                       false
% 1.85/1.01  --inst_orphan_elimination               true
% 1.85/1.01  --inst_learning_loop_flag               true
% 1.85/1.01  --inst_learning_start                   3000
% 1.85/1.01  --inst_learning_factor                  2
% 1.85/1.01  --inst_start_prop_sim_after_learn       3
% 1.85/1.01  --inst_sel_renew                        solver
% 1.85/1.01  --inst_lit_activity_flag                true
% 1.85/1.01  --inst_restr_to_given                   false
% 1.85/1.01  --inst_activity_threshold               500
% 1.85/1.01  --inst_out_proof                        true
% 1.85/1.01  
% 1.85/1.01  ------ Resolution Options
% 1.85/1.01  
% 1.85/1.01  --resolution_flag                       true
% 1.85/1.01  --res_lit_sel                           adaptive
% 1.85/1.01  --res_lit_sel_side                      none
% 1.85/1.01  --res_ordering                          kbo
% 1.85/1.01  --res_to_prop_solver                    active
% 1.85/1.01  --res_prop_simpl_new                    false
% 1.85/1.01  --res_prop_simpl_given                  true
% 1.85/1.01  --res_passive_queue_type                priority_queues
% 1.85/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.85/1.01  --res_passive_queues_freq               [15;5]
% 1.85/1.01  --res_forward_subs                      full
% 1.85/1.01  --res_backward_subs                     full
% 1.85/1.01  --res_forward_subs_resolution           true
% 1.85/1.01  --res_backward_subs_resolution          true
% 1.85/1.01  --res_orphan_elimination                true
% 1.85/1.01  --res_time_limit                        2.
% 1.85/1.01  --res_out_proof                         true
% 1.85/1.01  
% 1.85/1.01  ------ Superposition Options
% 1.85/1.01  
% 1.85/1.01  --superposition_flag                    true
% 1.85/1.01  --sup_passive_queue_type                priority_queues
% 1.85/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.85/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.85/1.01  --demod_completeness_check              fast
% 1.85/1.01  --demod_use_ground                      true
% 1.85/1.01  --sup_to_prop_solver                    passive
% 1.85/1.01  --sup_prop_simpl_new                    true
% 1.85/1.01  --sup_prop_simpl_given                  true
% 1.85/1.01  --sup_fun_splitting                     false
% 1.85/1.01  --sup_smt_interval                      50000
% 1.85/1.01  
% 1.85/1.01  ------ Superposition Simplification Setup
% 1.85/1.01  
% 1.85/1.01  --sup_indices_passive                   []
% 1.85/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.85/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.85/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.85/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.85/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.85/1.01  --sup_full_bw                           [BwDemod]
% 1.85/1.01  --sup_immed_triv                        [TrivRules]
% 1.85/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.85/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.85/1.01  --sup_immed_bw_main                     []
% 1.85/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.85/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.85/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.85/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.85/1.01  
% 1.85/1.01  ------ Combination Options
% 1.85/1.01  
% 1.85/1.01  --comb_res_mult                         3
% 1.85/1.01  --comb_sup_mult                         2
% 1.85/1.01  --comb_inst_mult                        10
% 1.85/1.01  
% 1.85/1.01  ------ Debug Options
% 1.85/1.01  
% 1.85/1.01  --dbg_backtrace                         false
% 1.85/1.01  --dbg_dump_prop_clauses                 false
% 1.85/1.01  --dbg_dump_prop_clauses_file            -
% 1.85/1.01  --dbg_out_stat                          false
% 1.85/1.01  ------ Parsing...
% 1.85/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.85/1.01  
% 1.85/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.85/1.01  
% 1.85/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.85/1.01  
% 1.85/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.85/1.01  ------ Proving...
% 1.85/1.01  ------ Problem Properties 
% 1.85/1.01  
% 1.85/1.01  
% 1.85/1.01  clauses                                 21
% 1.85/1.01  conjectures                             5
% 1.85/1.01  EPR                                     4
% 1.85/1.01  Horn                                    13
% 1.85/1.01  unary                                   3
% 1.85/1.01  binary                                  3
% 1.85/1.01  lits                                    67
% 1.85/1.01  lits eq                                 3
% 1.85/1.01  fd_pure                                 0
% 1.85/1.01  fd_pseudo                               0
% 1.85/1.01  fd_cond                                 0
% 1.85/1.01  fd_pseudo_cond                          1
% 1.85/1.01  AC symbols                              0
% 1.85/1.01  
% 1.85/1.01  ------ Schedule dynamic 5 is on 
% 1.85/1.01  
% 1.85/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.85/1.01  
% 1.85/1.01  
% 1.85/1.01  ------ 
% 1.85/1.01  Current options:
% 1.85/1.01  ------ 
% 1.85/1.01  
% 1.85/1.01  ------ Input Options
% 1.85/1.01  
% 1.85/1.01  --out_options                           all
% 1.85/1.01  --tptp_safe_out                         true
% 1.85/1.01  --problem_path                          ""
% 1.85/1.01  --include_path                          ""
% 1.85/1.01  --clausifier                            res/vclausify_rel
% 1.85/1.01  --clausifier_options                    --mode clausify
% 1.85/1.01  --stdin                                 false
% 1.85/1.01  --stats_out                             all
% 1.85/1.01  
% 1.85/1.01  ------ General Options
% 1.85/1.01  
% 1.85/1.01  --fof                                   false
% 1.85/1.01  --time_out_real                         305.
% 1.85/1.01  --time_out_virtual                      -1.
% 1.85/1.01  --symbol_type_check                     false
% 1.85/1.01  --clausify_out                          false
% 1.85/1.01  --sig_cnt_out                           false
% 1.85/1.01  --trig_cnt_out                          false
% 1.85/1.01  --trig_cnt_out_tolerance                1.
% 1.85/1.01  --trig_cnt_out_sk_spl                   false
% 1.85/1.01  --abstr_cl_out                          false
% 1.85/1.01  
% 1.85/1.01  ------ Global Options
% 1.85/1.01  
% 1.85/1.01  --schedule                              default
% 1.85/1.01  --add_important_lit                     false
% 1.85/1.01  --prop_solver_per_cl                    1000
% 1.85/1.01  --min_unsat_core                        false
% 1.85/1.01  --soft_assumptions                      false
% 1.85/1.01  --soft_lemma_size                       3
% 1.85/1.01  --prop_impl_unit_size                   0
% 1.85/1.01  --prop_impl_unit                        []
% 1.85/1.01  --share_sel_clauses                     true
% 1.85/1.01  --reset_solvers                         false
% 1.85/1.01  --bc_imp_inh                            [conj_cone]
% 1.85/1.01  --conj_cone_tolerance                   3.
% 1.85/1.01  --extra_neg_conj                        none
% 1.85/1.01  --large_theory_mode                     true
% 1.85/1.01  --prolific_symb_bound                   200
% 1.85/1.01  --lt_threshold                          2000
% 1.85/1.01  --clause_weak_htbl                      true
% 1.85/1.01  --gc_record_bc_elim                     false
% 1.85/1.01  
% 1.85/1.01  ------ Preprocessing Options
% 1.85/1.01  
% 1.85/1.01  --preprocessing_flag                    true
% 1.85/1.01  --time_out_prep_mult                    0.1
% 1.85/1.01  --splitting_mode                        input
% 1.85/1.01  --splitting_grd                         true
% 1.85/1.01  --splitting_cvd                         false
% 1.85/1.01  --splitting_cvd_svl                     false
% 1.85/1.01  --splitting_nvd                         32
% 1.85/1.01  --sub_typing                            true
% 1.85/1.01  --prep_gs_sim                           true
% 1.85/1.01  --prep_unflatten                        true
% 1.85/1.01  --prep_res_sim                          true
% 1.85/1.01  --prep_upred                            true
% 1.85/1.01  --prep_sem_filter                       exhaustive
% 1.85/1.01  --prep_sem_filter_out                   false
% 1.85/1.01  --pred_elim                             true
% 1.85/1.01  --res_sim_input                         true
% 1.85/1.01  --eq_ax_congr_red                       true
% 1.85/1.01  --pure_diseq_elim                       true
% 1.85/1.01  --brand_transform                       false
% 1.85/1.01  --non_eq_to_eq                          false
% 1.85/1.01  --prep_def_merge                        true
% 1.85/1.01  --prep_def_merge_prop_impl              false
% 1.85/1.01  --prep_def_merge_mbd                    true
% 1.85/1.01  --prep_def_merge_tr_red                 false
% 1.85/1.01  --prep_def_merge_tr_cl                  false
% 1.85/1.01  --smt_preprocessing                     true
% 1.85/1.01  --smt_ac_axioms                         fast
% 1.85/1.01  --preprocessed_out                      false
% 1.85/1.01  --preprocessed_stats                    false
% 1.85/1.01  
% 1.85/1.01  ------ Abstraction refinement Options
% 1.85/1.01  
% 1.85/1.01  --abstr_ref                             []
% 1.85/1.01  --abstr_ref_prep                        false
% 1.85/1.01  --abstr_ref_until_sat                   false
% 1.85/1.01  --abstr_ref_sig_restrict                funpre
% 1.85/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.85/1.01  --abstr_ref_under                       []
% 1.85/1.01  
% 1.85/1.01  ------ SAT Options
% 1.85/1.01  
% 1.85/1.01  --sat_mode                              false
% 1.85/1.01  --sat_fm_restart_options                ""
% 1.85/1.01  --sat_gr_def                            false
% 1.85/1.01  --sat_epr_types                         true
% 1.85/1.01  --sat_non_cyclic_types                  false
% 1.85/1.01  --sat_finite_models                     false
% 1.85/1.01  --sat_fm_lemmas                         false
% 1.85/1.01  --sat_fm_prep                           false
% 1.85/1.01  --sat_fm_uc_incr                        true
% 1.85/1.01  --sat_out_model                         small
% 1.85/1.01  --sat_out_clauses                       false
% 1.85/1.01  
% 1.85/1.01  ------ QBF Options
% 1.85/1.01  
% 1.85/1.01  --qbf_mode                              false
% 1.85/1.01  --qbf_elim_univ                         false
% 1.85/1.01  --qbf_dom_inst                          none
% 1.85/1.01  --qbf_dom_pre_inst                      false
% 1.85/1.01  --qbf_sk_in                             false
% 1.85/1.01  --qbf_pred_elim                         true
% 1.85/1.01  --qbf_split                             512
% 1.85/1.01  
% 1.85/1.01  ------ BMC1 Options
% 1.85/1.01  
% 1.85/1.01  --bmc1_incremental                      false
% 1.85/1.01  --bmc1_axioms                           reachable_all
% 1.85/1.01  --bmc1_min_bound                        0
% 1.85/1.01  --bmc1_max_bound                        -1
% 1.85/1.01  --bmc1_max_bound_default                -1
% 1.85/1.01  --bmc1_symbol_reachability              true
% 1.85/1.01  --bmc1_property_lemmas                  false
% 1.85/1.01  --bmc1_k_induction                      false
% 1.85/1.01  --bmc1_non_equiv_states                 false
% 1.85/1.01  --bmc1_deadlock                         false
% 1.85/1.01  --bmc1_ucm                              false
% 1.85/1.01  --bmc1_add_unsat_core                   none
% 1.85/1.01  --bmc1_unsat_core_children              false
% 1.85/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.85/1.01  --bmc1_out_stat                         full
% 1.85/1.01  --bmc1_ground_init                      false
% 1.85/1.01  --bmc1_pre_inst_next_state              false
% 1.85/1.01  --bmc1_pre_inst_state                   false
% 1.85/1.01  --bmc1_pre_inst_reach_state             false
% 1.85/1.01  --bmc1_out_unsat_core                   false
% 1.85/1.01  --bmc1_aig_witness_out                  false
% 1.85/1.01  --bmc1_verbose                          false
% 1.85/1.01  --bmc1_dump_clauses_tptp                false
% 1.85/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.85/1.01  --bmc1_dump_file                        -
% 1.85/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.85/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.85/1.01  --bmc1_ucm_extend_mode                  1
% 1.85/1.01  --bmc1_ucm_init_mode                    2
% 1.85/1.01  --bmc1_ucm_cone_mode                    none
% 1.85/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.85/1.01  --bmc1_ucm_relax_model                  4
% 1.85/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.85/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.85/1.01  --bmc1_ucm_layered_model                none
% 1.85/1.01  --bmc1_ucm_max_lemma_size               10
% 1.85/1.01  
% 1.85/1.01  ------ AIG Options
% 1.85/1.01  
% 1.85/1.01  --aig_mode                              false
% 1.85/1.01  
% 1.85/1.01  ------ Instantiation Options
% 1.85/1.01  
% 1.85/1.01  --instantiation_flag                    true
% 1.85/1.01  --inst_sos_flag                         false
% 1.85/1.01  --inst_sos_phase                        true
% 1.85/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.85/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.85/1.01  --inst_lit_sel_side                     none
% 1.85/1.01  --inst_solver_per_active                1400
% 1.85/1.01  --inst_solver_calls_frac                1.
% 1.85/1.01  --inst_passive_queue_type               priority_queues
% 1.85/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.85/1.01  --inst_passive_queues_freq              [25;2]
% 1.85/1.01  --inst_dismatching                      true
% 1.85/1.01  --inst_eager_unprocessed_to_passive     true
% 1.85/1.01  --inst_prop_sim_given                   true
% 1.85/1.01  --inst_prop_sim_new                     false
% 1.85/1.01  --inst_subs_new                         false
% 1.85/1.01  --inst_eq_res_simp                      false
% 1.85/1.01  --inst_subs_given                       false
% 1.85/1.01  --inst_orphan_elimination               true
% 1.85/1.01  --inst_learning_loop_flag               true
% 1.85/1.01  --inst_learning_start                   3000
% 1.85/1.01  --inst_learning_factor                  2
% 1.85/1.01  --inst_start_prop_sim_after_learn       3
% 1.85/1.01  --inst_sel_renew                        solver
% 1.85/1.01  --inst_lit_activity_flag                true
% 1.85/1.01  --inst_restr_to_given                   false
% 1.85/1.01  --inst_activity_threshold               500
% 1.85/1.01  --inst_out_proof                        true
% 1.85/1.01  
% 1.85/1.01  ------ Resolution Options
% 1.85/1.01  
% 1.85/1.01  --resolution_flag                       false
% 1.85/1.01  --res_lit_sel                           adaptive
% 1.85/1.01  --res_lit_sel_side                      none
% 1.85/1.01  --res_ordering                          kbo
% 1.85/1.01  --res_to_prop_solver                    active
% 1.85/1.01  --res_prop_simpl_new                    false
% 1.85/1.01  --res_prop_simpl_given                  true
% 1.85/1.01  --res_passive_queue_type                priority_queues
% 1.85/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.85/1.01  --res_passive_queues_freq               [15;5]
% 1.85/1.01  --res_forward_subs                      full
% 1.85/1.01  --res_backward_subs                     full
% 1.85/1.01  --res_forward_subs_resolution           true
% 1.85/1.01  --res_backward_subs_resolution          true
% 1.85/1.01  --res_orphan_elimination                true
% 1.85/1.01  --res_time_limit                        2.
% 1.85/1.01  --res_out_proof                         true
% 1.85/1.01  
% 1.85/1.01  ------ Superposition Options
% 1.85/1.01  
% 1.85/1.01  --superposition_flag                    true
% 1.85/1.01  --sup_passive_queue_type                priority_queues
% 1.85/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.85/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.85/1.01  --demod_completeness_check              fast
% 1.85/1.01  --demod_use_ground                      true
% 1.85/1.01  --sup_to_prop_solver                    passive
% 1.85/1.01  --sup_prop_simpl_new                    true
% 1.85/1.01  --sup_prop_simpl_given                  true
% 1.85/1.01  --sup_fun_splitting                     false
% 1.85/1.01  --sup_smt_interval                      50000
% 1.85/1.01  
% 1.85/1.01  ------ Superposition Simplification Setup
% 1.85/1.01  
% 1.85/1.01  --sup_indices_passive                   []
% 1.85/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.85/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.85/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.85/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.85/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.85/1.01  --sup_full_bw                           [BwDemod]
% 1.85/1.01  --sup_immed_triv                        [TrivRules]
% 1.85/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.85/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.85/1.01  --sup_immed_bw_main                     []
% 1.85/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.85/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.85/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.85/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.85/1.01  
% 1.85/1.01  ------ Combination Options
% 1.85/1.01  
% 1.85/1.01  --comb_res_mult                         3
% 1.85/1.01  --comb_sup_mult                         2
% 1.85/1.01  --comb_inst_mult                        10
% 1.85/1.01  
% 1.85/1.01  ------ Debug Options
% 1.85/1.01  
% 1.85/1.01  --dbg_backtrace                         false
% 1.85/1.01  --dbg_dump_prop_clauses                 false
% 1.85/1.01  --dbg_dump_prop_clauses_file            -
% 1.85/1.01  --dbg_out_stat                          false
% 1.85/1.01  
% 1.85/1.01  
% 1.85/1.01  
% 1.85/1.01  
% 1.85/1.01  ------ Proving...
% 1.85/1.01  
% 1.85/1.01  
% 1.85/1.01  % SZS status Theorem for theBenchmark.p
% 1.85/1.01  
% 1.85/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 1.85/1.01  
% 1.85/1.01  fof(f11,axiom,(
% 1.85/1.01    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.85/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/1.01  
% 1.85/1.01  fof(f17,plain,(
% 1.85/1.01    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.85/1.01    inference(pure_predicate_removal,[],[f11])).
% 1.85/1.01  
% 1.85/1.01  fof(f33,plain,(
% 1.85/1.01    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.85/1.01    inference(ennf_transformation,[],[f17])).
% 1.85/1.01  
% 1.85/1.01  fof(f34,plain,(
% 1.85/1.01    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.85/1.01    inference(flattening,[],[f33])).
% 1.85/1.01  
% 1.85/1.01  fof(f73,plain,(
% 1.85/1.01    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.85/1.01    inference(cnf_transformation,[],[f34])).
% 1.85/1.01  
% 1.85/1.01  fof(f9,axiom,(
% 1.85/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 1.85/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/1.01  
% 1.85/1.01  fof(f30,plain,(
% 1.85/1.01    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.85/1.01    inference(ennf_transformation,[],[f9])).
% 1.85/1.01  
% 1.85/1.01  fof(f31,plain,(
% 1.85/1.01    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.85/1.01    inference(flattening,[],[f30])).
% 1.85/1.01  
% 1.85/1.01  fof(f45,plain,(
% 1.85/1.01    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.85/1.01    inference(nnf_transformation,[],[f31])).
% 1.85/1.01  
% 1.85/1.01  fof(f46,plain,(
% 1.85/1.01    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.85/1.01    inference(rectify,[],[f45])).
% 1.85/1.01  
% 1.85/1.01  fof(f47,plain,(
% 1.85/1.01    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK1(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK1(X0,X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.85/1.01    introduced(choice_axiom,[])).
% 1.85/1.01  
% 1.85/1.01  fof(f48,plain,(
% 1.85/1.01    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK1(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK1(X0,X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.85/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f46,f47])).
% 1.85/1.01  
% 1.85/1.01  fof(f68,plain,(
% 1.85/1.01    ( ! [X0,X1] : (v1_tex_2(X1,X0) | u1_struct_0(X1) = sK1(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.85/1.01    inference(cnf_transformation,[],[f48])).
% 1.85/1.01  
% 1.85/1.01  fof(f1,axiom,(
% 1.85/1.01    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 1.85/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/1.01  
% 1.85/1.01  fof(f18,plain,(
% 1.85/1.01    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 1.85/1.01    inference(ennf_transformation,[],[f1])).
% 1.85/1.01  
% 1.85/1.01  fof(f55,plain,(
% 1.85/1.01    ( ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0)) )),
% 1.85/1.01    inference(cnf_transformation,[],[f18])).
% 1.85/1.01  
% 1.85/1.01  fof(f6,axiom,(
% 1.85/1.01    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.85/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/1.01  
% 1.85/1.01  fof(f25,plain,(
% 1.85/1.01    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.85/1.01    inference(ennf_transformation,[],[f6])).
% 1.85/1.01  
% 1.85/1.01  fof(f26,plain,(
% 1.85/1.01    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.85/1.01    inference(flattening,[],[f25])).
% 1.85/1.01  
% 1.85/1.01  fof(f60,plain,(
% 1.85/1.01    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.85/1.01    inference(cnf_transformation,[],[f26])).
% 1.85/1.01  
% 1.85/1.01  fof(f10,axiom,(
% 1.85/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.85/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/1.01  
% 1.85/1.01  fof(f32,plain,(
% 1.85/1.01    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.85/1.01    inference(ennf_transformation,[],[f10])).
% 1.85/1.01  
% 1.85/1.01  fof(f49,plain,(
% 1.85/1.01    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.85/1.01    inference(nnf_transformation,[],[f32])).
% 1.85/1.01  
% 1.85/1.01  fof(f71,plain,(
% 1.85/1.01    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.85/1.01    inference(cnf_transformation,[],[f49])).
% 1.85/1.01  
% 1.85/1.01  fof(f8,axiom,(
% 1.85/1.01    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 1.85/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/1.01  
% 1.85/1.01  fof(f29,plain,(
% 1.85/1.01    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 1.85/1.01    inference(ennf_transformation,[],[f8])).
% 1.85/1.01  
% 1.85/1.01  fof(f41,plain,(
% 1.85/1.01    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 1.85/1.01    inference(nnf_transformation,[],[f29])).
% 1.85/1.01  
% 1.85/1.01  fof(f42,plain,(
% 1.85/1.01    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 1.85/1.01    inference(rectify,[],[f41])).
% 1.85/1.01  
% 1.85/1.01  fof(f43,plain,(
% 1.85/1.01    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK0(X0)) = X0 & m1_subset_1(sK0(X0),X0)))),
% 1.85/1.01    introduced(choice_axiom,[])).
% 1.85/1.01  
% 1.85/1.01  fof(f44,plain,(
% 1.85/1.01    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK0(X0)) = X0 & m1_subset_1(sK0(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 1.85/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).
% 1.85/1.01  
% 1.85/1.01  fof(f65,plain,(
% 1.85/1.01    ( ! [X0,X1] : (v1_zfmisc_1(X0) | k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.85/1.01    inference(cnf_transformation,[],[f44])).
% 1.85/1.01  
% 1.85/1.01  fof(f14,conjecture,(
% 1.85/1.01    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 1.85/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/1.01  
% 1.85/1.01  fof(f15,negated_conjecture,(
% 1.85/1.01    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 1.85/1.01    inference(negated_conjecture,[],[f14])).
% 1.85/1.01  
% 1.85/1.01  fof(f39,plain,(
% 1.85/1.01    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.85/1.01    inference(ennf_transformation,[],[f15])).
% 1.85/1.01  
% 1.85/1.01  fof(f40,plain,(
% 1.85/1.01    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.85/1.01    inference(flattening,[],[f39])).
% 1.85/1.01  
% 1.85/1.01  fof(f50,plain,(
% 1.85/1.01    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.85/1.01    inference(nnf_transformation,[],[f40])).
% 1.85/1.01  
% 1.85/1.01  fof(f51,plain,(
% 1.85/1.01    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.85/1.01    inference(flattening,[],[f50])).
% 1.85/1.01  
% 1.85/1.01  fof(f53,plain,(
% 1.85/1.01    ( ! [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),sK3),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,sK3),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),sK3),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,sK3),X0)) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 1.85/1.01    introduced(choice_axiom,[])).
% 1.85/1.01  
% 1.85/1.01  fof(f52,plain,(
% 1.85/1.01    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK2),X1),u1_struct_0(sK2)) | ~v1_tex_2(k1_tex_2(sK2,X1),sK2)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK2),X1),u1_struct_0(sK2)) | v1_tex_2(k1_tex_2(sK2,X1),sK2)) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.85/1.01    introduced(choice_axiom,[])).
% 1.85/1.01  
% 1.85/1.01  fof(f54,plain,(
% 1.85/1.01    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | ~v1_tex_2(k1_tex_2(sK2,sK3),sK2)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | v1_tex_2(k1_tex_2(sK2,sK3),sK2)) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 1.85/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f51,f53,f52])).
% 1.85/1.01  
% 1.85/1.01  fof(f81,plain,(
% 1.85/1.01    ~v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | ~v1_tex_2(k1_tex_2(sK2,sK3),sK2)),
% 1.85/1.01    inference(cnf_transformation,[],[f54])).
% 1.85/1.01  
% 1.85/1.01  fof(f78,plain,(
% 1.85/1.01    l1_pre_topc(sK2)),
% 1.85/1.01    inference(cnf_transformation,[],[f54])).
% 1.85/1.01  
% 1.85/1.01  fof(f79,plain,(
% 1.85/1.01    m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.85/1.01    inference(cnf_transformation,[],[f54])).
% 1.85/1.01  
% 1.85/1.01  fof(f4,axiom,(
% 1.85/1.01    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0)) => ~v1_zfmisc_1(u1_struct_0(X0)))),
% 1.85/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/1.01  
% 1.85/1.01  fof(f21,plain,(
% 1.85/1.01    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v7_struct_0(X0)))),
% 1.85/1.01    inference(ennf_transformation,[],[f4])).
% 1.85/1.01  
% 1.85/1.01  fof(f22,plain,(
% 1.85/1.01    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 1.85/1.01    inference(flattening,[],[f21])).
% 1.85/1.01  
% 1.85/1.01  fof(f58,plain,(
% 1.85/1.01    ( ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0)) )),
% 1.85/1.01    inference(cnf_transformation,[],[f22])).
% 1.85/1.01  
% 1.85/1.01  fof(f2,axiom,(
% 1.85/1.01    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.85/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/1.01  
% 1.85/1.01  fof(f19,plain,(
% 1.85/1.01    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.85/1.01    inference(ennf_transformation,[],[f2])).
% 1.85/1.01  
% 1.85/1.01  fof(f56,plain,(
% 1.85/1.01    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.85/1.01    inference(cnf_transformation,[],[f19])).
% 1.85/1.01  
% 1.85/1.01  fof(f80,plain,(
% 1.85/1.01    v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | v1_tex_2(k1_tex_2(sK2,sK3),sK2)),
% 1.85/1.01    inference(cnf_transformation,[],[f54])).
% 1.85/1.01  
% 1.85/1.01  fof(f13,axiom,(
% 1.85/1.01    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 1.85/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/1.01  
% 1.85/1.01  fof(f37,plain,(
% 1.85/1.01    ! [X0] : (! [X1] : ((~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.85/1.01    inference(ennf_transformation,[],[f13])).
% 1.85/1.01  
% 1.85/1.01  fof(f38,plain,(
% 1.85/1.01    ! [X0] : (! [X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.85/1.01    inference(flattening,[],[f37])).
% 1.85/1.01  
% 1.85/1.01  fof(f76,plain,(
% 1.85/1.01    ( ! [X0,X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.85/1.01    inference(cnf_transformation,[],[f38])).
% 1.85/1.01  
% 1.85/1.01  fof(f77,plain,(
% 1.85/1.01    ~v2_struct_0(sK2)),
% 1.85/1.01    inference(cnf_transformation,[],[f54])).
% 1.85/1.01  
% 1.85/1.01  fof(f7,axiom,(
% 1.85/1.01    ! [X0] : ((l1_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (~v2_struct_0(X1) => (~v1_tex_2(X1,X0) & ~v2_struct_0(X1)))))),
% 1.85/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/1.01  
% 1.85/1.01  fof(f27,plain,(
% 1.85/1.01    ! [X0] : (! [X1] : (((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)))),
% 1.85/1.01    inference(ennf_transformation,[],[f7])).
% 1.85/1.01  
% 1.85/1.01  fof(f28,plain,(
% 1.85/1.01    ! [X0] : (! [X1] : ((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))),
% 1.85/1.01    inference(flattening,[],[f27])).
% 1.85/1.01  
% 1.85/1.01  fof(f62,plain,(
% 1.85/1.01    ( ! [X0,X1] : (~v1_tex_2(X1,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)) )),
% 1.85/1.01    inference(cnf_transformation,[],[f28])).
% 1.85/1.01  
% 1.85/1.01  fof(f12,axiom,(
% 1.85/1.01    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.85/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/1.01  
% 1.85/1.01  fof(f16,plain,(
% 1.85/1.01    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.85/1.01    inference(pure_predicate_removal,[],[f12])).
% 1.85/1.01  
% 1.85/1.01  fof(f35,plain,(
% 1.85/1.01    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.85/1.01    inference(ennf_transformation,[],[f16])).
% 1.85/1.01  
% 1.85/1.01  fof(f36,plain,(
% 1.85/1.01    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.85/1.01    inference(flattening,[],[f35])).
% 1.85/1.01  
% 1.85/1.01  fof(f74,plain,(
% 1.85/1.01    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.85/1.01    inference(cnf_transformation,[],[f36])).
% 1.85/1.01  
% 1.85/1.01  fof(f67,plain,(
% 1.85/1.01    ( ! [X0,X1] : (v1_tex_2(X1,X0) | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.85/1.01    inference(cnf_transformation,[],[f48])).
% 1.85/1.01  
% 1.85/1.01  fof(f69,plain,(
% 1.85/1.01    ( ! [X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(sK1(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.85/1.01    inference(cnf_transformation,[],[f48])).
% 1.85/1.01  
% 1.85/1.01  fof(f5,axiom,(
% 1.85/1.01    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 1.85/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/1.01  
% 1.85/1.01  fof(f23,plain,(
% 1.85/1.01    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 1.85/1.01    inference(ennf_transformation,[],[f5])).
% 1.85/1.01  
% 1.85/1.01  fof(f24,plain,(
% 1.85/1.01    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 1.85/1.01    inference(flattening,[],[f23])).
% 1.85/1.01  
% 1.85/1.01  fof(f59,plain,(
% 1.85/1.01    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 1.85/1.01    inference(cnf_transformation,[],[f24])).
% 1.85/1.01  
% 1.85/1.01  fof(f3,axiom,(
% 1.85/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.85/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.85/1.01  
% 1.85/1.01  fof(f20,plain,(
% 1.85/1.01    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.85/1.01    inference(ennf_transformation,[],[f3])).
% 1.85/1.01  
% 1.85/1.01  fof(f57,plain,(
% 1.85/1.01    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.85/1.01    inference(cnf_transformation,[],[f20])).
% 1.85/1.01  
% 1.85/1.01  fof(f75,plain,(
% 1.85/1.01    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.85/1.01    inference(cnf_transformation,[],[f36])).
% 1.85/1.01  
% 1.85/1.01  cnf(c_17,plain,
% 1.85/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.85/1.01      | m1_pre_topc(k1_tex_2(X1,X0),X1)
% 1.85/1.01      | v2_struct_0(X1)
% 1.85/1.01      | ~ l1_pre_topc(X1) ),
% 1.85/1.01      inference(cnf_transformation,[],[f73]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_2473,plain,
% 1.85/1.01      ( ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
% 1.85/1.01      | m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47)
% 1.85/1.01      | v2_struct_0(X0_47)
% 1.85/1.01      | ~ l1_pre_topc(X0_47) ),
% 1.85/1.01      inference(subtyping,[status(esa)],[c_17]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_3088,plain,
% 1.85/1.01      ( m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
% 1.85/1.01      | m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47) = iProver_top
% 1.85/1.01      | v2_struct_0(X0_47) = iProver_top
% 1.85/1.01      | l1_pre_topc(X0_47) != iProver_top ),
% 1.85/1.01      inference(predicate_to_equality,[status(thm)],[c_2473]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_12,plain,
% 1.85/1.01      ( v1_tex_2(X0,X1)
% 1.85/1.01      | ~ m1_pre_topc(X0,X1)
% 1.85/1.01      | ~ l1_pre_topc(X1)
% 1.85/1.01      | sK1(X1,X0) = u1_struct_0(X0) ),
% 1.85/1.01      inference(cnf_transformation,[],[f68]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_2478,plain,
% 1.85/1.01      ( v1_tex_2(X0_47,X1_47)
% 1.85/1.01      | ~ m1_pre_topc(X0_47,X1_47)
% 1.85/1.01      | ~ l1_pre_topc(X1_47)
% 1.85/1.01      | sK1(X1_47,X0_47) = u1_struct_0(X0_47) ),
% 1.85/1.01      inference(subtyping,[status(esa)],[c_12]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_3083,plain,
% 1.85/1.01      ( sK1(X0_47,X1_47) = u1_struct_0(X1_47)
% 1.85/1.01      | v1_tex_2(X1_47,X0_47) = iProver_top
% 1.85/1.01      | m1_pre_topc(X1_47,X0_47) != iProver_top
% 1.85/1.01      | l1_pre_topc(X0_47) != iProver_top ),
% 1.85/1.01      inference(predicate_to_equality,[status(thm)],[c_2478]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_3503,plain,
% 1.85/1.01      ( sK1(X0_47,k1_tex_2(X0_47,X0_46)) = u1_struct_0(k1_tex_2(X0_47,X0_46))
% 1.85/1.01      | v1_tex_2(k1_tex_2(X0_47,X0_46),X0_47) = iProver_top
% 1.85/1.01      | m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
% 1.85/1.01      | v2_struct_0(X0_47) = iProver_top
% 1.85/1.01      | l1_pre_topc(X0_47) != iProver_top ),
% 1.85/1.01      inference(superposition,[status(thm)],[c_3088,c_3083]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_0,plain,
% 1.85/1.01      ( ~ v1_xboole_0(X0) | v1_zfmisc_1(X0) ),
% 1.85/1.01      inference(cnf_transformation,[],[f55]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_5,plain,
% 1.85/1.01      ( ~ m1_subset_1(X0,X1)
% 1.85/1.01      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 1.85/1.01      | v1_xboole_0(X1) ),
% 1.85/1.01      inference(cnf_transformation,[],[f60]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_428,plain,
% 1.85/1.01      ( ~ m1_subset_1(X0,X1)
% 1.85/1.01      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 1.85/1.01      | v1_zfmisc_1(X2)
% 1.85/1.01      | X1 != X2 ),
% 1.85/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_5]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_429,plain,
% 1.85/1.01      ( ~ m1_subset_1(X0,X1)
% 1.85/1.01      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 1.85/1.01      | v1_zfmisc_1(X1) ),
% 1.85/1.01      inference(unflattening,[status(thm)],[c_428]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_2461,plain,
% 1.85/1.01      ( ~ m1_subset_1(X0_46,X1_46)
% 1.85/1.01      | m1_subset_1(k6_domain_1(X1_46,X0_46),k1_zfmisc_1(X1_46))
% 1.85/1.01      | v1_zfmisc_1(X1_46) ),
% 1.85/1.01      inference(subtyping,[status(esa)],[c_429]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_3100,plain,
% 1.85/1.01      ( m1_subset_1(X0_46,X1_46) != iProver_top
% 1.85/1.01      | m1_subset_1(k6_domain_1(X1_46,X0_46),k1_zfmisc_1(X1_46)) = iProver_top
% 1.85/1.01      | v1_zfmisc_1(X1_46) = iProver_top ),
% 1.85/1.01      inference(predicate_to_equality,[status(thm)],[c_2461]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_15,plain,
% 1.85/1.01      ( v1_subset_1(X0,X1)
% 1.85/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.85/1.01      | X0 = X1 ),
% 1.85/1.01      inference(cnf_transformation,[],[f71]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_2475,plain,
% 1.85/1.01      ( v1_subset_1(X0_46,X1_46)
% 1.85/1.01      | ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
% 1.85/1.01      | X0_46 = X1_46 ),
% 1.85/1.01      inference(subtyping,[status(esa)],[c_15]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_3086,plain,
% 1.85/1.01      ( X0_46 = X1_46
% 1.85/1.01      | v1_subset_1(X0_46,X1_46) = iProver_top
% 1.85/1.01      | m1_subset_1(X0_46,k1_zfmisc_1(X1_46)) != iProver_top ),
% 1.85/1.01      inference(predicate_to_equality,[status(thm)],[c_2475]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_4194,plain,
% 1.85/1.01      ( k6_domain_1(X0_46,X1_46) = X0_46
% 1.85/1.01      | v1_subset_1(k6_domain_1(X0_46,X1_46),X0_46) = iProver_top
% 1.85/1.01      | m1_subset_1(X1_46,X0_46) != iProver_top
% 1.85/1.01      | v1_zfmisc_1(X0_46) = iProver_top ),
% 1.85/1.01      inference(superposition,[status(thm)],[c_3100,c_3086]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_8,plain,
% 1.85/1.01      ( ~ m1_subset_1(X0,X1)
% 1.85/1.01      | v1_xboole_0(X1)
% 1.85/1.01      | v1_zfmisc_1(X1)
% 1.85/1.01      | k6_domain_1(X1,X0) != X1 ),
% 1.85/1.01      inference(cnf_transformation,[],[f65]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_413,plain,
% 1.85/1.01      ( ~ m1_subset_1(X0,X1)
% 1.85/1.01      | v1_zfmisc_1(X2)
% 1.85/1.01      | v1_zfmisc_1(X1)
% 1.85/1.01      | X1 != X2
% 1.85/1.01      | k6_domain_1(X1,X0) != X1 ),
% 1.85/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_8]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_414,plain,
% 1.85/1.01      ( ~ m1_subset_1(X0,X1)
% 1.85/1.01      | v1_zfmisc_1(X1)
% 1.85/1.01      | k6_domain_1(X1,X0) != X1 ),
% 1.85/1.01      inference(unflattening,[status(thm)],[c_413]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_2462,plain,
% 1.85/1.01      ( ~ m1_subset_1(X0_46,X1_46)
% 1.85/1.01      | v1_zfmisc_1(X1_46)
% 1.85/1.01      | k6_domain_1(X1_46,X0_46) != X1_46 ),
% 1.85/1.01      inference(subtyping,[status(esa)],[c_414]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_2544,plain,
% 1.85/1.01      ( k6_domain_1(X0_46,X1_46) != X0_46
% 1.85/1.01      | m1_subset_1(X1_46,X0_46) != iProver_top
% 1.85/1.01      | v1_zfmisc_1(X0_46) = iProver_top ),
% 1.85/1.01      inference(predicate_to_equality,[status(thm)],[c_2462]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_4199,plain,
% 1.85/1.01      ( v1_subset_1(k6_domain_1(X0_46,X1_46),X0_46) = iProver_top
% 1.85/1.01      | m1_subset_1(X1_46,X0_46) != iProver_top
% 1.85/1.01      | v1_zfmisc_1(X0_46) = iProver_top ),
% 1.85/1.01      inference(global_propositional_subsumption,
% 1.85/1.01                [status(thm)],
% 1.85/1.01                [c_4194,c_2544]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_22,negated_conjecture,
% 1.85/1.01      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 1.85/1.01      | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
% 1.85/1.01      inference(cnf_transformation,[],[f81]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_2470,negated_conjecture,
% 1.85/1.01      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 1.85/1.01      | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
% 1.85/1.01      inference(subtyping,[status(esa)],[c_22]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_3091,plain,
% 1.85/1.01      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
% 1.85/1.01      | v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top ),
% 1.85/1.01      inference(predicate_to_equality,[status(thm)],[c_2470]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_4208,plain,
% 1.85/1.01      ( v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 1.85/1.01      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 1.85/1.01      | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top ),
% 1.85/1.01      inference(superposition,[status(thm)],[c_4199,c_3091]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_25,negated_conjecture,
% 1.85/1.01      ( l1_pre_topc(sK2) ),
% 1.85/1.01      inference(cnf_transformation,[],[f78]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_28,plain,
% 1.85/1.01      ( l1_pre_topc(sK2) = iProver_top ),
% 1.85/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_24,negated_conjecture,
% 1.85/1.01      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 1.85/1.01      inference(cnf_transformation,[],[f79]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_29,plain,
% 1.85/1.01      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 1.85/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_31,plain,
% 1.85/1.01      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
% 1.85/1.01      | v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top ),
% 1.85/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_3,plain,
% 1.85/1.01      ( v7_struct_0(X0)
% 1.85/1.01      | ~ l1_struct_0(X0)
% 1.85/1.01      | ~ v1_zfmisc_1(u1_struct_0(X0)) ),
% 1.85/1.01      inference(cnf_transformation,[],[f58]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_82,plain,
% 1.85/1.01      ( v7_struct_0(X0) = iProver_top
% 1.85/1.01      | l1_struct_0(X0) != iProver_top
% 1.85/1.01      | v1_zfmisc_1(u1_struct_0(X0)) != iProver_top ),
% 1.85/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_84,plain,
% 1.85/1.01      ( v7_struct_0(sK2) = iProver_top
% 1.85/1.01      | l1_struct_0(sK2) != iProver_top
% 1.85/1.01      | v1_zfmisc_1(u1_struct_0(sK2)) != iProver_top ),
% 1.85/1.01      inference(instantiation,[status(thm)],[c_82]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_1,plain,
% 1.85/1.01      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.85/1.01      inference(cnf_transformation,[],[f56]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_86,plain,
% 1.85/1.01      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 1.85/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_88,plain,
% 1.85/1.01      ( l1_pre_topc(sK2) != iProver_top
% 1.85/1.01      | l1_struct_0(sK2) = iProver_top ),
% 1.85/1.01      inference(instantiation,[status(thm)],[c_86]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_3289,plain,
% 1.85/1.01      ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.85/1.01      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 1.85/1.01      | v1_zfmisc_1(u1_struct_0(sK2)) ),
% 1.85/1.01      inference(instantiation,[status(thm)],[c_2461]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_3290,plain,
% 1.85/1.01      ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 1.85/1.01      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 1.85/1.01      | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top ),
% 1.85/1.01      inference(predicate_to_equality,[status(thm)],[c_3289]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_3292,plain,
% 1.85/1.01      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 1.85/1.01      | v1_zfmisc_1(u1_struct_0(sK2))
% 1.85/1.01      | k6_domain_1(u1_struct_0(sK2),sK3) != u1_struct_0(sK2) ),
% 1.85/1.01      inference(instantiation,[status(thm)],[c_2462]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_3293,plain,
% 1.85/1.01      ( k6_domain_1(u1_struct_0(sK2),sK3) != u1_struct_0(sK2)
% 1.85/1.01      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 1.85/1.01      | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top ),
% 1.85/1.01      inference(predicate_to_equality,[status(thm)],[c_3292]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_3372,plain,
% 1.85/1.01      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 1.85/1.01      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.85/1.01      | k6_domain_1(u1_struct_0(sK2),sK3) = u1_struct_0(sK2) ),
% 1.85/1.01      inference(instantiation,[status(thm)],[c_2475]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_3373,plain,
% 1.85/1.01      ( k6_domain_1(u1_struct_0(sK2),sK3) = u1_struct_0(sK2)
% 1.85/1.01      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) = iProver_top
% 1.85/1.01      | m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.85/1.01      inference(predicate_to_equality,[status(thm)],[c_3372]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_23,negated_conjecture,
% 1.85/1.01      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 1.85/1.01      | v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
% 1.85/1.01      inference(cnf_transformation,[],[f80]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_2469,negated_conjecture,
% 1.85/1.01      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 1.85/1.01      | v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
% 1.85/1.01      inference(subtyping,[status(esa)],[c_23]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_3092,plain,
% 1.85/1.01      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) = iProver_top
% 1.85/1.01      | v1_tex_2(k1_tex_2(sK2,sK3),sK2) = iProver_top ),
% 1.85/1.01      inference(predicate_to_equality,[status(thm)],[c_2469]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_21,plain,
% 1.85/1.01      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
% 1.85/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.85/1.01      | v2_struct_0(X0)
% 1.85/1.01      | ~ v7_struct_0(X0)
% 1.85/1.01      | ~ l1_struct_0(X0) ),
% 1.85/1.01      inference(cnf_transformation,[],[f76]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_349,plain,
% 1.85/1.01      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
% 1.85/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.85/1.01      | v2_struct_0(X0)
% 1.85/1.01      | ~ v7_struct_0(X0)
% 1.85/1.01      | ~ l1_pre_topc(X0) ),
% 1.85/1.01      inference(resolution,[status(thm)],[c_1,c_21]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_2465,plain,
% 1.85/1.01      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0_47),X0_46),u1_struct_0(X0_47))
% 1.85/1.01      | ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
% 1.85/1.01      | v2_struct_0(X0_47)
% 1.85/1.01      | ~ v7_struct_0(X0_47)
% 1.85/1.01      | ~ l1_pre_topc(X0_47) ),
% 1.85/1.01      inference(subtyping,[status(esa)],[c_349]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_3096,plain,
% 1.85/1.01      ( v1_subset_1(k6_domain_1(u1_struct_0(X0_47),X0_46),u1_struct_0(X0_47)) != iProver_top
% 1.85/1.01      | m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
% 1.85/1.01      | v2_struct_0(X0_47) = iProver_top
% 1.85/1.01      | v7_struct_0(X0_47) != iProver_top
% 1.85/1.01      | l1_pre_topc(X0_47) != iProver_top ),
% 1.85/1.01      inference(predicate_to_equality,[status(thm)],[c_2465]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_4089,plain,
% 1.85/1.01      ( v1_tex_2(k1_tex_2(sK2,sK3),sK2) = iProver_top
% 1.85/1.01      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 1.85/1.01      | v2_struct_0(sK2) = iProver_top
% 1.85/1.01      | v7_struct_0(sK2) != iProver_top
% 1.85/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 1.85/1.01      inference(superposition,[status(thm)],[c_3092,c_3096]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_26,negated_conjecture,
% 1.85/1.01      ( ~ v2_struct_0(sK2) ),
% 1.85/1.01      inference(cnf_transformation,[],[f77]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_27,plain,
% 1.85/1.01      ( v2_struct_0(sK2) != iProver_top ),
% 1.85/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_6,plain,
% 1.85/1.01      ( ~ v1_tex_2(X0,X1)
% 1.85/1.01      | ~ m1_pre_topc(X0,X1)
% 1.85/1.01      | v2_struct_0(X1)
% 1.85/1.01      | v2_struct_0(X0)
% 1.85/1.01      | ~ v7_struct_0(X1)
% 1.85/1.01      | ~ l1_pre_topc(X1) ),
% 1.85/1.01      inference(cnf_transformation,[],[f62]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_204,plain,
% 1.85/1.01      ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 1.85/1.01      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
% 1.85/1.01      inference(prop_impl,[status(thm)],[c_23]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_205,plain,
% 1.85/1.01      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 1.85/1.01      | v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
% 1.85/1.01      inference(renaming,[status(thm)],[c_204]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_1317,plain,
% 1.85/1.01      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 1.85/1.01      | ~ m1_pre_topc(X0,X1)
% 1.85/1.01      | v2_struct_0(X0)
% 1.85/1.01      | v2_struct_0(X1)
% 1.85/1.01      | ~ v7_struct_0(X1)
% 1.85/1.01      | ~ l1_pre_topc(X1)
% 1.85/1.01      | k1_tex_2(sK2,sK3) != X0
% 1.85/1.01      | sK2 != X1 ),
% 1.85/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_205]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_1318,plain,
% 1.85/1.01      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 1.85/1.01      | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 1.85/1.01      | v2_struct_0(k1_tex_2(sK2,sK3))
% 1.85/1.01      | v2_struct_0(sK2)
% 1.85/1.01      | ~ v7_struct_0(sK2)
% 1.85/1.01      | ~ l1_pre_topc(sK2) ),
% 1.85/1.01      inference(unflattening,[status(thm)],[c_1317]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_1320,plain,
% 1.85/1.01      ( ~ v7_struct_0(sK2)
% 1.85/1.01      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 1.85/1.01      | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 1.85/1.01      | v2_struct_0(k1_tex_2(sK2,sK3)) ),
% 1.85/1.01      inference(global_propositional_subsumption,
% 1.85/1.01                [status(thm)],
% 1.85/1.01                [c_1318,c_26,c_25]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_1321,plain,
% 1.85/1.01      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 1.85/1.01      | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 1.85/1.01      | v2_struct_0(k1_tex_2(sK2,sK3))
% 1.85/1.01      | ~ v7_struct_0(sK2) ),
% 1.85/1.01      inference(renaming,[status(thm)],[c_1320]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_1322,plain,
% 1.85/1.01      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) = iProver_top
% 1.85/1.01      | m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 1.85/1.01      | v2_struct_0(k1_tex_2(sK2,sK3)) = iProver_top
% 1.85/1.01      | v7_struct_0(sK2) != iProver_top ),
% 1.85/1.01      inference(predicate_to_equality,[status(thm)],[c_1321]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_2525,plain,
% 1.85/1.01      ( m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
% 1.85/1.01      | m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47) = iProver_top
% 1.85/1.01      | v2_struct_0(X0_47) = iProver_top
% 1.85/1.01      | l1_pre_topc(X0_47) != iProver_top ),
% 1.85/1.01      inference(predicate_to_equality,[status(thm)],[c_2473]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_2527,plain,
% 1.85/1.01      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 1.85/1.01      | m1_pre_topc(k1_tex_2(sK2,sK3),sK2) = iProver_top
% 1.85/1.01      | v2_struct_0(sK2) = iProver_top
% 1.85/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 1.85/1.01      inference(instantiation,[status(thm)],[c_2525]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_20,plain,
% 1.85/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.85/1.01      | v2_struct_0(X1)
% 1.85/1.01      | ~ v2_struct_0(k1_tex_2(X1,X0))
% 1.85/1.01      | ~ l1_pre_topc(X1) ),
% 1.85/1.01      inference(cnf_transformation,[],[f74]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_2472,plain,
% 1.85/1.01      ( ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
% 1.85/1.01      | v2_struct_0(X0_47)
% 1.85/1.01      | ~ v2_struct_0(k1_tex_2(X0_47,X0_46))
% 1.85/1.01      | ~ l1_pre_topc(X0_47) ),
% 1.85/1.01      inference(subtyping,[status(esa)],[c_20]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_2528,plain,
% 1.85/1.01      ( m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
% 1.85/1.01      | v2_struct_0(X0_47) = iProver_top
% 1.85/1.01      | v2_struct_0(k1_tex_2(X0_47,X0_46)) != iProver_top
% 1.85/1.01      | l1_pre_topc(X0_47) != iProver_top ),
% 1.85/1.01      inference(predicate_to_equality,[status(thm)],[c_2472]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_2530,plain,
% 1.85/1.01      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 1.85/1.01      | v2_struct_0(k1_tex_2(sK2,sK3)) != iProver_top
% 1.85/1.01      | v2_struct_0(sK2) = iProver_top
% 1.85/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 1.85/1.01      inference(instantiation,[status(thm)],[c_2528]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_2539,plain,
% 1.85/1.01      ( v1_subset_1(k6_domain_1(u1_struct_0(X0_47),X0_46),u1_struct_0(X0_47)) != iProver_top
% 1.85/1.01      | m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
% 1.85/1.01      | v2_struct_0(X0_47) = iProver_top
% 1.85/1.01      | v7_struct_0(X0_47) != iProver_top
% 1.85/1.01      | l1_pre_topc(X0_47) != iProver_top ),
% 1.85/1.01      inference(predicate_to_equality,[status(thm)],[c_2465]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_2541,plain,
% 1.85/1.01      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
% 1.85/1.01      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 1.85/1.01      | v2_struct_0(sK2) = iProver_top
% 1.85/1.01      | v7_struct_0(sK2) != iProver_top
% 1.85/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 1.85/1.01      inference(instantiation,[status(thm)],[c_2539]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_4092,plain,
% 1.85/1.01      ( v7_struct_0(sK2) != iProver_top ),
% 1.85/1.01      inference(global_propositional_subsumption,
% 1.85/1.01                [status(thm)],
% 1.85/1.01                [c_4089,c_27,c_28,c_29,c_1322,c_2527,c_2530,c_2541]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_4285,plain,
% 1.85/1.01      ( v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top ),
% 1.85/1.01      inference(global_propositional_subsumption,
% 1.85/1.01                [status(thm)],
% 1.85/1.01                [c_4208,c_27,c_28,c_29,c_31,c_84,c_88,c_1322,c_2527,
% 1.85/1.01                 c_2530,c_2541,c_3290,c_3293,c_3373]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_4512,plain,
% 1.85/1.01      ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
% 1.85/1.01      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 1.85/1.01      | v2_struct_0(sK2) = iProver_top
% 1.85/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 1.85/1.01      inference(superposition,[status(thm)],[c_3503,c_4285]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_13,plain,
% 1.85/1.01      ( v1_tex_2(X0,X1)
% 1.85/1.01      | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.85/1.01      | ~ m1_pre_topc(X0,X1)
% 1.85/1.01      | ~ l1_pre_topc(X1) ),
% 1.85/1.01      inference(cnf_transformation,[],[f67]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_2477,plain,
% 1.85/1.01      ( v1_tex_2(X0_47,X1_47)
% 1.85/1.01      | m1_subset_1(sK1(X1_47,X0_47),k1_zfmisc_1(u1_struct_0(X1_47)))
% 1.85/1.01      | ~ m1_pre_topc(X0_47,X1_47)
% 1.85/1.01      | ~ l1_pre_topc(X1_47) ),
% 1.85/1.01      inference(subtyping,[status(esa)],[c_13]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_3084,plain,
% 1.85/1.01      ( v1_tex_2(X0_47,X1_47) = iProver_top
% 1.85/1.01      | m1_subset_1(sK1(X1_47,X0_47),k1_zfmisc_1(u1_struct_0(X1_47))) = iProver_top
% 1.85/1.01      | m1_pre_topc(X0_47,X1_47) != iProver_top
% 1.85/1.01      | l1_pre_topc(X1_47) != iProver_top ),
% 1.85/1.01      inference(predicate_to_equality,[status(thm)],[c_2477]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_3806,plain,
% 1.85/1.01      ( sK1(X0_47,X1_47) = u1_struct_0(X0_47)
% 1.85/1.01      | v1_subset_1(sK1(X0_47,X1_47),u1_struct_0(X0_47)) = iProver_top
% 1.85/1.01      | v1_tex_2(X1_47,X0_47) = iProver_top
% 1.85/1.01      | m1_pre_topc(X1_47,X0_47) != iProver_top
% 1.85/1.01      | l1_pre_topc(X0_47) != iProver_top ),
% 1.85/1.01      inference(superposition,[status(thm)],[c_3084,c_3086]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_11,plain,
% 1.85/1.01      ( ~ v1_subset_1(sK1(X0,X1),u1_struct_0(X0))
% 1.85/1.01      | v1_tex_2(X1,X0)
% 1.85/1.01      | ~ m1_pre_topc(X1,X0)
% 1.85/1.01      | ~ l1_pre_topc(X0) ),
% 1.85/1.01      inference(cnf_transformation,[],[f69]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_2479,plain,
% 1.85/1.01      ( ~ v1_subset_1(sK1(X0_47,X1_47),u1_struct_0(X0_47))
% 1.85/1.01      | v1_tex_2(X1_47,X0_47)
% 1.85/1.01      | ~ m1_pre_topc(X1_47,X0_47)
% 1.85/1.01      | ~ l1_pre_topc(X0_47) ),
% 1.85/1.01      inference(subtyping,[status(esa)],[c_11]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_2515,plain,
% 1.85/1.01      ( v1_subset_1(sK1(X0_47,X1_47),u1_struct_0(X0_47)) != iProver_top
% 1.85/1.01      | v1_tex_2(X1_47,X0_47) = iProver_top
% 1.85/1.01      | m1_pre_topc(X1_47,X0_47) != iProver_top
% 1.85/1.01      | l1_pre_topc(X0_47) != iProver_top ),
% 1.85/1.01      inference(predicate_to_equality,[status(thm)],[c_2479]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_4006,plain,
% 1.85/1.01      ( sK1(X0_47,X1_47) = u1_struct_0(X0_47)
% 1.85/1.01      | v1_tex_2(X1_47,X0_47) = iProver_top
% 1.85/1.01      | m1_pre_topc(X1_47,X0_47) != iProver_top
% 1.85/1.01      | l1_pre_topc(X0_47) != iProver_top ),
% 1.85/1.01      inference(global_propositional_subsumption,
% 1.85/1.01                [status(thm)],
% 1.85/1.01                [c_3806,c_2515]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_4014,plain,
% 1.85/1.01      ( sK1(X0_47,k1_tex_2(X0_47,X0_46)) = u1_struct_0(X0_47)
% 1.85/1.01      | v1_tex_2(k1_tex_2(X0_47,X0_46),X0_47) = iProver_top
% 1.85/1.01      | m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
% 1.85/1.01      | v2_struct_0(X0_47) = iProver_top
% 1.85/1.01      | l1_pre_topc(X0_47) != iProver_top ),
% 1.85/1.01      inference(superposition,[status(thm)],[c_3088,c_4006]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_4296,plain,
% 1.85/1.01      ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(sK2)
% 1.85/1.01      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 1.85/1.01      | v2_struct_0(sK2) = iProver_top
% 1.85/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 1.85/1.01      inference(superposition,[status(thm)],[c_4014,c_4285]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_202,plain,
% 1.85/1.01      ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 1.85/1.01      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
% 1.85/1.01      inference(prop_impl,[status(thm)],[c_22]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_203,plain,
% 1.85/1.01      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 1.85/1.01      | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
% 1.85/1.01      inference(renaming,[status(thm)],[c_202]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_1246,plain,
% 1.85/1.01      ( ~ v1_subset_1(sK1(X0,X1),u1_struct_0(X0))
% 1.85/1.01      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 1.85/1.01      | ~ m1_pre_topc(X1,X0)
% 1.85/1.01      | ~ l1_pre_topc(X0)
% 1.85/1.01      | k1_tex_2(sK2,sK3) != X1
% 1.85/1.01      | sK2 != X0 ),
% 1.85/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_203]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_1247,plain,
% 1.85/1.01      ( ~ v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
% 1.85/1.01      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 1.85/1.01      | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 1.85/1.01      | ~ l1_pre_topc(sK2) ),
% 1.85/1.01      inference(unflattening,[status(thm)],[c_1246]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_1248,plain,
% 1.85/1.01      ( v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) != iProver_top
% 1.85/1.01      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
% 1.85/1.01      | m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 1.85/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 1.85/1.01      inference(predicate_to_equality,[status(thm)],[c_1247]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_1263,plain,
% 1.85/1.01      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 1.85/1.01      | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 1.85/1.01      | ~ m1_pre_topc(X1,X0)
% 1.85/1.01      | ~ l1_pre_topc(X0)
% 1.85/1.01      | k1_tex_2(sK2,sK3) != X1
% 1.85/1.01      | sK2 != X0 ),
% 1.85/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_203]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_1264,plain,
% 1.85/1.01      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 1.85/1.01      | m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.85/1.01      | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 1.85/1.01      | ~ l1_pre_topc(sK2) ),
% 1.85/1.01      inference(unflattening,[status(thm)],[c_1263]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_1265,plain,
% 1.85/1.01      ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
% 1.85/1.01      | m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 1.85/1.01      | m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 1.85/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 1.85/1.01      inference(predicate_to_equality,[status(thm)],[c_1264]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_3388,plain,
% 1.85/1.01      ( v1_subset_1(X0_46,u1_struct_0(sK2))
% 1.85/1.01      | ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.85/1.01      | X0_46 = u1_struct_0(sK2) ),
% 1.85/1.01      inference(instantiation,[status(thm)],[c_2475]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_3667,plain,
% 1.85/1.01      ( v1_subset_1(sK1(sK2,k1_tex_2(sK2,X0_46)),u1_struct_0(sK2))
% 1.85/1.01      | ~ m1_subset_1(sK1(sK2,k1_tex_2(sK2,X0_46)),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.85/1.01      | sK1(sK2,k1_tex_2(sK2,X0_46)) = u1_struct_0(sK2) ),
% 1.85/1.01      inference(instantiation,[status(thm)],[c_3388]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_3670,plain,
% 1.85/1.01      ( sK1(sK2,k1_tex_2(sK2,X0_46)) = u1_struct_0(sK2)
% 1.85/1.01      | v1_subset_1(sK1(sK2,k1_tex_2(sK2,X0_46)),u1_struct_0(sK2)) = iProver_top
% 1.85/1.01      | m1_subset_1(sK1(sK2,k1_tex_2(sK2,X0_46)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.85/1.01      inference(predicate_to_equality,[status(thm)],[c_3667]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_3672,plain,
% 1.85/1.01      ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(sK2)
% 1.85/1.01      | v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) = iProver_top
% 1.85/1.01      | m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.85/1.01      inference(instantiation,[status(thm)],[c_3670]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_4412,plain,
% 1.85/1.01      ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(sK2) ),
% 1.85/1.01      inference(global_propositional_subsumption,
% 1.85/1.01                [status(thm)],
% 1.85/1.01                [c_4296,c_27,c_28,c_29,c_84,c_88,c_1248,c_1265,c_1322,
% 1.85/1.01                 c_2527,c_2530,c_2541,c_3290,c_3293,c_3373,c_3672]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_4532,plain,
% 1.85/1.01      ( u1_struct_0(k1_tex_2(sK2,sK3)) = u1_struct_0(sK2)
% 1.85/1.01      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 1.85/1.01      | v2_struct_0(sK2) = iProver_top
% 1.85/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 1.85/1.01      inference(light_normalisation,[status(thm)],[c_4512,c_4412]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_4753,plain,
% 1.85/1.01      ( u1_struct_0(k1_tex_2(sK2,sK3)) = u1_struct_0(sK2) ),
% 1.85/1.01      inference(global_propositional_subsumption,
% 1.85/1.01                [status(thm)],
% 1.85/1.01                [c_4532,c_27,c_28,c_29]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_4,plain,
% 1.85/1.01      ( ~ v7_struct_0(X0)
% 1.85/1.01      | ~ l1_struct_0(X0)
% 1.85/1.01      | v1_zfmisc_1(u1_struct_0(X0)) ),
% 1.85/1.01      inference(cnf_transformation,[],[f59]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_369,plain,
% 1.85/1.01      ( ~ v7_struct_0(X0)
% 1.85/1.01      | ~ l1_pre_topc(X0)
% 1.85/1.01      | v1_zfmisc_1(u1_struct_0(X0)) ),
% 1.85/1.01      inference(resolution,[status(thm)],[c_1,c_4]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_2464,plain,
% 1.85/1.01      ( ~ v7_struct_0(X0_47)
% 1.85/1.01      | ~ l1_pre_topc(X0_47)
% 1.85/1.01      | v1_zfmisc_1(u1_struct_0(X0_47)) ),
% 1.85/1.01      inference(subtyping,[status(esa)],[c_369]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_3097,plain,
% 1.85/1.01      ( v7_struct_0(X0_47) != iProver_top
% 1.85/1.01      | l1_pre_topc(X0_47) != iProver_top
% 1.85/1.01      | v1_zfmisc_1(u1_struct_0(X0_47)) = iProver_top ),
% 1.85/1.01      inference(predicate_to_equality,[status(thm)],[c_2464]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_4765,plain,
% 1.85/1.01      ( v7_struct_0(k1_tex_2(sK2,sK3)) != iProver_top
% 1.85/1.01      | l1_pre_topc(k1_tex_2(sK2,sK3)) != iProver_top
% 1.85/1.01      | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top ),
% 1.85/1.01      inference(superposition,[status(thm)],[c_4753,c_3097]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_2,plain,
% 1.85/1.01      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 1.85/1.01      inference(cnf_transformation,[],[f57]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_2481,plain,
% 1.85/1.01      ( ~ m1_pre_topc(X0_47,X1_47)
% 1.85/1.01      | ~ l1_pre_topc(X1_47)
% 1.85/1.01      | l1_pre_topc(X0_47) ),
% 1.85/1.01      inference(subtyping,[status(esa)],[c_2]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_3411,plain,
% 1.85/1.01      ( ~ m1_pre_topc(k1_tex_2(X0_47,X0_46),X1_47)
% 1.85/1.01      | ~ l1_pre_topc(X1_47)
% 1.85/1.01      | l1_pre_topc(k1_tex_2(X0_47,X0_46)) ),
% 1.85/1.01      inference(instantiation,[status(thm)],[c_2481]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_3412,plain,
% 1.85/1.01      ( m1_pre_topc(k1_tex_2(X0_47,X0_46),X1_47) != iProver_top
% 1.85/1.01      | l1_pre_topc(X1_47) != iProver_top
% 1.85/1.01      | l1_pre_topc(k1_tex_2(X0_47,X0_46)) = iProver_top ),
% 1.85/1.01      inference(predicate_to_equality,[status(thm)],[c_3411]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_3414,plain,
% 1.85/1.01      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 1.85/1.01      | l1_pre_topc(k1_tex_2(sK2,sK3)) = iProver_top
% 1.85/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 1.85/1.01      inference(instantiation,[status(thm)],[c_3412]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_19,plain,
% 1.85/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.85/1.01      | v2_struct_0(X1)
% 1.85/1.01      | v7_struct_0(k1_tex_2(X1,X0))
% 1.85/1.01      | ~ l1_pre_topc(X1) ),
% 1.85/1.01      inference(cnf_transformation,[],[f75]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_2471,plain,
% 1.85/1.01      ( ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
% 1.85/1.01      | v2_struct_0(X0_47)
% 1.85/1.01      | v7_struct_0(k1_tex_2(X0_47,X0_46))
% 1.85/1.01      | ~ l1_pre_topc(X0_47) ),
% 1.85/1.01      inference(subtyping,[status(esa)],[c_19]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_2531,plain,
% 1.85/1.01      ( m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
% 1.85/1.01      | v2_struct_0(X0_47) = iProver_top
% 1.85/1.01      | v7_struct_0(k1_tex_2(X0_47,X0_46)) = iProver_top
% 1.85/1.01      | l1_pre_topc(X0_47) != iProver_top ),
% 1.85/1.01      inference(predicate_to_equality,[status(thm)],[c_2471]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(c_2533,plain,
% 1.85/1.01      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 1.85/1.01      | v2_struct_0(sK2) = iProver_top
% 1.85/1.01      | v7_struct_0(k1_tex_2(sK2,sK3)) = iProver_top
% 1.85/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 1.85/1.01      inference(instantiation,[status(thm)],[c_2531]) ).
% 1.85/1.01  
% 1.85/1.01  cnf(contradiction,plain,
% 1.85/1.01      ( $false ),
% 1.85/1.01      inference(minisat,
% 1.85/1.01                [status(thm)],
% 1.85/1.01                [c_4765,c_4092,c_3414,c_2533,c_2527,c_88,c_84,c_29,c_28,
% 1.85/1.02                 c_27]) ).
% 1.85/1.02  
% 1.85/1.02  
% 1.85/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 1.85/1.02  
% 1.85/1.02  ------                               Statistics
% 1.85/1.02  
% 1.85/1.02  ------ General
% 1.85/1.02  
% 1.85/1.02  abstr_ref_over_cycles:                  0
% 1.85/1.02  abstr_ref_under_cycles:                 0
% 1.85/1.02  gc_basic_clause_elim:                   0
% 1.85/1.02  forced_gc_time:                         0
% 1.85/1.02  parsing_time:                           0.009
% 1.85/1.02  unif_index_cands_time:                  0.
% 1.85/1.02  unif_index_add_time:                    0.
% 1.85/1.02  orderings_time:                         0.
% 1.85/1.02  out_proof_time:                         0.008
% 1.85/1.02  total_time:                             0.142
% 1.85/1.02  num_of_symbols:                         51
% 1.85/1.02  num_of_terms:                           2733
% 1.85/1.02  
% 1.85/1.02  ------ Preprocessing
% 1.85/1.02  
% 1.85/1.02  num_of_splits:                          0
% 1.85/1.02  num_of_split_atoms:                     0
% 1.85/1.02  num_of_reused_defs:                     0
% 1.85/1.02  num_eq_ax_congr_red:                    12
% 1.85/1.02  num_of_sem_filtered_clauses:            1
% 1.85/1.02  num_of_subtypes:                        2
% 1.85/1.02  monotx_restored_types:                  1
% 1.85/1.02  sat_num_of_epr_types:                   0
% 1.85/1.02  sat_num_of_non_cyclic_types:            0
% 1.85/1.02  sat_guarded_non_collapsed_types:        0
% 1.85/1.02  num_pure_diseq_elim:                    0
% 1.85/1.02  simp_replaced_by:                       0
% 1.85/1.02  res_preprocessed:                       119
% 1.85/1.02  prep_upred:                             0
% 1.85/1.02  prep_unflattend:                        86
% 1.85/1.02  smt_new_axioms:                         0
% 1.85/1.02  pred_elim_cands:                        8
% 1.85/1.02  pred_elim:                              2
% 1.85/1.02  pred_elim_cl:                           4
% 1.85/1.02  pred_elim_cycles:                       12
% 1.85/1.02  merged_defs:                            8
% 1.85/1.02  merged_defs_ncl:                        0
% 1.85/1.02  bin_hyper_res:                          8
% 1.85/1.02  prep_cycles:                            4
% 1.85/1.02  pred_elim_time:                         0.033
% 1.85/1.02  splitting_time:                         0.
% 1.85/1.02  sem_filter_time:                        0.
% 1.85/1.02  monotx_time:                            0.001
% 1.85/1.02  subtype_inf_time:                       0.001
% 1.85/1.02  
% 1.85/1.02  ------ Problem properties
% 1.85/1.02  
% 1.85/1.02  clauses:                                21
% 1.85/1.02  conjectures:                            5
% 1.85/1.02  epr:                                    4
% 1.85/1.02  horn:                                   13
% 1.85/1.02  ground:                                 5
% 1.85/1.02  unary:                                  3
% 1.85/1.02  binary:                                 3
% 1.85/1.02  lits:                                   67
% 1.85/1.02  lits_eq:                                3
% 1.85/1.02  fd_pure:                                0
% 1.85/1.02  fd_pseudo:                              0
% 1.85/1.02  fd_cond:                                0
% 1.85/1.02  fd_pseudo_cond:                         1
% 1.85/1.02  ac_symbols:                             0
% 1.85/1.02  
% 1.85/1.02  ------ Propositional Solver
% 1.85/1.02  
% 1.85/1.02  prop_solver_calls:                      28
% 1.85/1.02  prop_fast_solver_calls:                 1358
% 1.85/1.02  smt_solver_calls:                       0
% 1.85/1.02  smt_fast_solver_calls:                  0
% 1.85/1.02  prop_num_of_clauses:                    954
% 1.85/1.02  prop_preprocess_simplified:             4753
% 1.85/1.02  prop_fo_subsumed:                       50
% 1.85/1.02  prop_solver_time:                       0.
% 1.85/1.02  smt_solver_time:                        0.
% 1.85/1.02  smt_fast_solver_time:                   0.
% 1.85/1.02  prop_fast_solver_time:                  0.
% 1.85/1.02  prop_unsat_core_time:                   0.
% 1.85/1.02  
% 1.85/1.02  ------ QBF
% 1.85/1.02  
% 1.85/1.02  qbf_q_res:                              0
% 1.85/1.02  qbf_num_tautologies:                    0
% 1.85/1.02  qbf_prep_cycles:                        0
% 1.85/1.02  
% 1.85/1.02  ------ BMC1
% 1.85/1.02  
% 1.85/1.02  bmc1_current_bound:                     -1
% 1.85/1.02  bmc1_last_solved_bound:                 -1
% 1.85/1.02  bmc1_unsat_core_size:                   -1
% 1.85/1.02  bmc1_unsat_core_parents_size:           -1
% 1.85/1.02  bmc1_merge_next_fun:                    0
% 1.85/1.02  bmc1_unsat_core_clauses_time:           0.
% 1.85/1.02  
% 1.85/1.02  ------ Instantiation
% 1.85/1.02  
% 1.85/1.02  inst_num_of_clauses:                    273
% 1.85/1.02  inst_num_in_passive:                    63
% 1.85/1.02  inst_num_in_active:                     168
% 1.85/1.02  inst_num_in_unprocessed:                42
% 1.85/1.02  inst_num_of_loops:                      190
% 1.85/1.02  inst_num_of_learning_restarts:          0
% 1.85/1.02  inst_num_moves_active_passive:          18
% 1.85/1.02  inst_lit_activity:                      0
% 1.85/1.02  inst_lit_activity_moves:                0
% 1.85/1.02  inst_num_tautologies:                   0
% 1.85/1.02  inst_num_prop_implied:                  0
% 1.85/1.02  inst_num_existing_simplified:           0
% 1.85/1.02  inst_num_eq_res_simplified:             0
% 1.85/1.02  inst_num_child_elim:                    0
% 1.85/1.02  inst_num_of_dismatching_blockings:      62
% 1.85/1.02  inst_num_of_non_proper_insts:           309
% 1.85/1.02  inst_num_of_duplicates:                 0
% 1.85/1.02  inst_inst_num_from_inst_to_res:         0
% 1.85/1.02  inst_dismatching_checking_time:         0.
% 1.85/1.02  
% 1.85/1.02  ------ Resolution
% 1.85/1.02  
% 1.85/1.02  res_num_of_clauses:                     0
% 1.85/1.02  res_num_in_passive:                     0
% 1.85/1.02  res_num_in_active:                      0
% 1.85/1.02  res_num_of_loops:                       123
% 1.85/1.02  res_forward_subset_subsumed:            44
% 1.85/1.02  res_backward_subset_subsumed:           0
% 1.85/1.02  res_forward_subsumed:                   0
% 1.85/1.02  res_backward_subsumed:                  0
% 1.85/1.02  res_forward_subsumption_resolution:     3
% 1.85/1.02  res_backward_subsumption_resolution:    0
% 1.85/1.02  res_clause_to_clause_subsumption:       139
% 1.85/1.02  res_orphan_elimination:                 0
% 1.85/1.02  res_tautology_del:                      81
% 1.85/1.02  res_num_eq_res_simplified:              0
% 1.85/1.02  res_num_sel_changes:                    0
% 1.85/1.02  res_moves_from_active_to_pass:          0
% 1.85/1.02  
% 1.85/1.02  ------ Superposition
% 1.85/1.02  
% 1.85/1.02  sup_time_total:                         0.
% 1.85/1.02  sup_time_generating:                    0.
% 1.85/1.02  sup_time_sim_full:                      0.
% 1.85/1.02  sup_time_sim_immed:                     0.
% 1.85/1.02  
% 1.85/1.02  sup_num_of_clauses:                     44
% 1.85/1.02  sup_num_in_active:                      38
% 1.85/1.02  sup_num_in_passive:                     6
% 1.85/1.02  sup_num_of_loops:                       37
% 1.85/1.02  sup_fw_superposition:                   8
% 1.85/1.02  sup_bw_superposition:                   29
% 1.85/1.02  sup_immediate_simplified:               8
% 1.85/1.02  sup_given_eliminated:                   0
% 1.85/1.02  comparisons_done:                       0
% 1.85/1.02  comparisons_avoided:                    0
% 1.85/1.02  
% 1.85/1.02  ------ Simplifications
% 1.85/1.02  
% 1.85/1.02  
% 1.85/1.02  sim_fw_subset_subsumed:                 4
% 1.85/1.02  sim_bw_subset_subsumed:                 1
% 1.85/1.02  sim_fw_subsumed:                        0
% 1.85/1.02  sim_bw_subsumed:                        0
% 1.85/1.02  sim_fw_subsumption_res:                 0
% 1.85/1.02  sim_bw_subsumption_res:                 0
% 1.85/1.02  sim_tautology_del:                      2
% 1.85/1.02  sim_eq_tautology_del:                   1
% 1.85/1.02  sim_eq_res_simp:                        0
% 1.85/1.02  sim_fw_demodulated:                     0
% 1.85/1.02  sim_bw_demodulated:                     0
% 1.85/1.02  sim_light_normalised:                   5
% 1.85/1.02  sim_joinable_taut:                      0
% 1.85/1.02  sim_joinable_simp:                      0
% 1.85/1.02  sim_ac_normalised:                      0
% 1.85/1.02  sim_smt_subsumption:                    0
% 1.85/1.02  
%------------------------------------------------------------------------------
