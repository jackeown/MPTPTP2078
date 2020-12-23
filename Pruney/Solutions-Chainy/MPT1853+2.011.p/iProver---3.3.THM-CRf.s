%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:36 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 817 expanded)
%              Number of clauses        :  103 ( 280 expanded)
%              Number of leaves         :   19 ( 150 expanded)
%              Depth                    :   21
%              Number of atoms          :  684 (3843 expanded)
%              Number of equality atoms :  148 ( 369 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v1_subset_1(X2,u1_struct_0(X0))
                <=> v1_tex_2(X1,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v1_subset_1(X2,u1_struct_0(X0))
              <=> v1_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v1_subset_1(X2,u1_struct_0(X0))
              <=> v1_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v1_subset_1(X2,u1_struct_0(X0))
                  | ~ v1_tex_2(X1,X0) )
                & ( v1_tex_2(X1,X0)
                  | ~ v1_subset_1(X2,u1_struct_0(X0)) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(X2,u1_struct_0(X0))
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),sK2),u1_struct_0(X0))
          | ~ v1_tex_2(k1_tex_2(X0,sK2),X0) )
        & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),sK2),u1_struct_0(X0))
          | v1_tex_2(k1_tex_2(X0,sK2),X0) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
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
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),X1),u1_struct_0(sK1))
            | ~ v1_tex_2(k1_tex_2(sK1,X1),sK1) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),X1),u1_struct_0(sK1))
            | v1_tex_2(k1_tex_2(sK1,X1),sK1) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
      | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) )
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f53,f55,f54])).

fof(f83,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f80,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f79,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f81,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f56])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f58,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ~ v2_struct_0(X1)
           => ( ~ v1_tex_2(X1,X0)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f32])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f82,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f57,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK0(X0)) = X0
        & m1_subset_1(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK0(X0)) = X0
            & m1_subset_1(sK0(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X0)
      | k6_domain_1(X0,X1) != X0
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f62,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X0)
      | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f59,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v7_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_subset_1(X2,u1_struct_0(X0))
      | ~ v1_tex_2(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f77])).

cnf(c_7,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2205,plain,
    ( m1_subset_1(u1_struct_0(X0_46),k1_zfmisc_1(u1_struct_0(X1_46)))
    | ~ m1_pre_topc(X0_46,X1_46)
    | ~ l1_pre_topc(X1_46) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2861,plain,
    ( m1_subset_1(u1_struct_0(X0_46),k1_zfmisc_1(u1_struct_0(X1_46))) = iProver_top
    | m1_pre_topc(X0_46,X1_46) != iProver_top
    | l1_pre_topc(X1_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2205])).

cnf(c_13,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2202,plain,
    ( v1_subset_1(X0_45,X1_45)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(X1_45))
    | X0_45 = X1_45 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2864,plain,
    ( X0_45 = X1_45
    | v1_subset_1(X0_45,X1_45) = iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(X1_45)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2202])).

cnf(c_3417,plain,
    ( u1_struct_0(X0_46) = u1_struct_0(X1_46)
    | v1_subset_1(u1_struct_0(X1_46),u1_struct_0(X0_46)) = iProver_top
    | m1_pre_topc(X1_46,X0_46) != iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_2861,c_2864])).

cnf(c_20,plain,
    ( ~ v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | v1_tex_2(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_153,plain,
    ( v1_tex_2(X0,X1)
    | ~ v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_7])).

cnf(c_154,plain,
    ( ~ v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_153])).

cnf(c_22,negated_conjecture,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_214,plain,
    ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
    inference(prop_impl,[status(thm)],[c_22])).

cnf(c_215,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(renaming,[status(thm)],[c_214])).

cnf(c_661,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | k1_tex_2(sK1,sK2) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_154,c_215])).

cnf(c_662,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
    | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_661])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_664,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_662,c_25])).

cnf(c_665,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
    | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1) ),
    inference(renaming,[status(thm)],[c_664])).

cnf(c_2189,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
    | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1) ),
    inference(subtyping,[status(esa)],[c_665])).

cnf(c_2877,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
    | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2189])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_27,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_28,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_29,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_82,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_84,plain,
    ( v2_struct_0(sK1) = iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_82])).

cnf(c_1,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_86,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_88,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_struct_0(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_86])).

cnf(c_663,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
    | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_662])).

cnf(c_4,plain,
    ( v7_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_zfmisc_1(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_373,plain,
    ( v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_zfmisc_1(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_1,c_4])).

cnf(c_8,plain,
    ( ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v7_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_23,negated_conjecture,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_216,plain,
    ( v1_tex_2(k1_tex_2(sK1,sK2),sK1)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
    inference(prop_impl,[status(thm)],[c_23])).

cnf(c_217,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(renaming,[status(thm)],[c_216])).

cnf(c_695,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0,X1)
    | ~ v7_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k1_tex_2(sK1,sK2) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_217])).

cnf(c_696,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | ~ v7_struct_0(sK1)
    | v2_struct_0(k1_tex_2(sK1,sK2))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_695])).

cnf(c_698,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | ~ v7_struct_0(sK1)
    | v2_struct_0(k1_tex_2(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_696,c_26,c_25])).

cnf(c_942,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | v2_struct_0(k1_tex_2(sK1,sK2))
    | ~ l1_pre_topc(X0)
    | ~ v1_zfmisc_1(u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_373,c_698])).

cnf(c_943,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | v2_struct_0(k1_tex_2(sK1,sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_942])).

cnf(c_944,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | v2_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_943])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_pre_topc(k1_tex_2(X1,X0),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2200,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(X0_46))
    | m1_pre_topc(k1_tex_2(X0_46,X0_45),X0_46)
    | v2_struct_0(X0_46)
    | ~ l1_pre_topc(X0_46) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2258,plain,
    ( m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
    | m1_pre_topc(k1_tex_2(X0_46,X0_45),X0_46) = iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2200])).

cnf(c_2260,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2258])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2199,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(X0_46))
    | v2_struct_0(X0_46)
    | ~ v2_struct_0(k1_tex_2(X0_46,X0_45))
    | ~ l1_pre_topc(X0_46) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_2261,plain,
    ( m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | v2_struct_0(k1_tex_2(X0_46,X0_45)) != iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2199])).

cnf(c_2263,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2261])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | v1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | v1_zfmisc_1(X1)
    | k6_domain_1(X1,X0) != X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1108,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_zfmisc_1(X2)
    | v1_zfmisc_1(X1)
    | X1 != X2
    | k6_domain_1(X1,X0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_10])).

cnf(c_1109,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_zfmisc_1(X1)
    | k6_domain_1(X1,X0) != X1 ),
    inference(unflattening,[status(thm)],[c_1108])).

cnf(c_2186,plain,
    ( ~ m1_subset_1(X0_45,X1_45)
    | v1_zfmisc_1(X1_45)
    | k6_domain_1(X1_45,X0_45) != X1_45 ),
    inference(subtyping,[status(esa)],[c_1109])).

cnf(c_3077,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v1_zfmisc_1(u1_struct_0(sK1))
    | k6_domain_1(u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2186])).

cnf(c_3078,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3077])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2206,plain,
    ( ~ m1_subset_1(X0_45,X1_45)
    | m1_subset_1(k6_domain_1(X1_45,X0_45),k1_zfmisc_1(X1_45))
    | v1_xboole_0(X1_45) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_3090,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2206])).

cnf(c_3091,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3090])).

cnf(c_3130,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | k6_domain_1(u1_struct_0(sK1),sK2) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2202])).

cnf(c_3131,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3130])).

cnf(c_3734,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2877,c_27,c_28,c_29,c_84,c_88,c_663,c_944,c_2260,c_2263,c_3078,c_3091,c_3131])).

cnf(c_4303,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3417,c_3734])).

cnf(c_3093,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(X0_46,X0_45)),k1_zfmisc_1(u1_struct_0(X0_46)))
    | ~ m1_pre_topc(k1_tex_2(X0_46,X0_45),X0_46)
    | ~ l1_pre_topc(X0_46) ),
    inference(instantiation,[status(thm)],[c_2205])).

cnf(c_3094,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(X0_46,X0_45)),k1_zfmisc_1(u1_struct_0(X0_46))) = iProver_top
    | m1_pre_topc(k1_tex_2(X0_46,X0_45),X0_46) != iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3093])).

cnf(c_3096,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3094])).

cnf(c_3156,plain,
    ( v1_subset_1(X0_45,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
    | X0_45 = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2202])).

cnf(c_3294,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK1,X0_45)),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK1,X0_45)),k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_struct_0(k1_tex_2(sK1,X0_45)) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_3156])).

cnf(c_3296,plain,
    ( u1_struct_0(k1_tex_2(sK1,X0_45)) = u1_struct_0(sK1)
    | v1_subset_1(u1_struct_0(k1_tex_2(sK1,X0_45)),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(u1_struct_0(k1_tex_2(sK1,X0_45)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3294])).

cnf(c_3298,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
    | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3296])).

cnf(c_4313,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4303,c_27,c_28,c_29,c_84,c_88,c_663,c_944,c_2260,c_2263,c_3078,c_3091,c_3096,c_3131,c_3298])).

cnf(c_5,plain,
    ( ~ v7_struct_0(X0)
    | ~ l1_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_359,plain,
    ( ~ v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_zfmisc_1(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_1,c_5])).

cnf(c_2193,plain,
    ( ~ v7_struct_0(X0_46)
    | ~ l1_pre_topc(X0_46)
    | v1_zfmisc_1(u1_struct_0(X0_46)) ),
    inference(subtyping,[status(esa)],[c_359])).

cnf(c_2873,plain,
    ( v7_struct_0(X0_46) != iProver_top
    | l1_pre_topc(X0_46) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X0_46)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2193])).

cnf(c_4327,plain,
    ( v7_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
    | l1_pre_topc(k1_tex_2(sK1,sK2)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4313,c_2873])).

cnf(c_21,plain,
    ( ~ v1_subset_1(k6_domain_1(X0,X1),X0)
    | ~ m1_subset_1(X1,X0)
    | v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2197,plain,
    ( ~ v1_subset_1(k6_domain_1(X0_45,X1_45),X0_45)
    | ~ m1_subset_1(X1_45,X0_45)
    | v1_xboole_0(X0_45)
    | ~ v1_zfmisc_1(X0_45) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_3709,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0_46),X0_45),u1_struct_0(X0_46))
    | ~ m1_subset_1(X0_45,u1_struct_0(X0_46))
    | v1_xboole_0(u1_struct_0(X0_46))
    | ~ v1_zfmisc_1(u1_struct_0(X0_46)) ),
    inference(instantiation,[status(thm)],[c_2197])).

cnf(c_3720,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(X0_46),X0_45),u1_struct_0(X0_46)) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_46)) = iProver_top
    | v1_zfmisc_1(u1_struct_0(X0_46)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3709])).

cnf(c_3722,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top
    | v1_zfmisc_1(u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3720])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2207,plain,
    ( ~ m1_pre_topc(X0_46,X1_46)
    | ~ l1_pre_topc(X1_46)
    | l1_pre_topc(X0_46) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_3182,plain,
    ( ~ m1_pre_topc(k1_tex_2(X0_46,X0_45),X1_46)
    | ~ l1_pre_topc(X1_46)
    | l1_pre_topc(k1_tex_2(X0_46,X0_45)) ),
    inference(instantiation,[status(thm)],[c_2207])).

cnf(c_3183,plain,
    ( m1_pre_topc(k1_tex_2(X0_46,X0_45),X1_46) != iProver_top
    | l1_pre_topc(X1_46) != iProver_top
    | l1_pre_topc(k1_tex_2(X0_46,X0_45)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3182])).

cnf(c_3185,plain,
    ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | l1_pre_topc(k1_tex_2(sK1,sK2)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3183])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v7_struct_0(k1_tex_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2198,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(X0_46))
    | v7_struct_0(k1_tex_2(X0_46,X0_45))
    | v2_struct_0(X0_46)
    | ~ l1_pre_topc(X0_46) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2264,plain,
    ( m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
    | v7_struct_0(k1_tex_2(X0_46,X0_45)) = iProver_top
    | v2_struct_0(X0_46) = iProver_top
    | l1_pre_topc(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2198])).

cnf(c_2266,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v7_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2264])).

cnf(c_19,plain,
    ( v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tex_2(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_160,plain,
    ( ~ v1_tex_2(X0,X1)
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_7])).

cnf(c_161,plain,
    ( v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_160])).

cnf(c_678,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | k1_tex_2(sK1,sK2) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_161,c_217])).

cnf(c_679,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
    | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_678])).

cnf(c_681,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_679,c_25])).

cnf(c_682,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
    | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1) ),
    inference(renaming,[status(thm)],[c_681])).

cnf(c_683,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
    | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) = iProver_top
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_682])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4327,c_3734,c_3722,c_3185,c_2266,c_2260,c_683,c_88,c_84,c_29,c_28,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n022.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 18:19:10 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 1.73/1.06  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.06  
% 1.73/1.06  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.73/1.06  
% 1.73/1.06  ------  iProver source info
% 1.73/1.06  
% 1.73/1.06  git: date: 2020-06-30 10:37:57 +0100
% 1.73/1.06  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.73/1.06  git: non_committed_changes: false
% 1.73/1.06  git: last_make_outside_of_git: false
% 1.73/1.06  
% 1.73/1.06  ------ 
% 1.73/1.06  
% 1.73/1.06  ------ Input Options
% 1.73/1.06  
% 1.73/1.06  --out_options                           all
% 1.73/1.06  --tptp_safe_out                         true
% 1.73/1.06  --problem_path                          ""
% 1.73/1.06  --include_path                          ""
% 1.73/1.06  --clausifier                            res/vclausify_rel
% 1.73/1.06  --clausifier_options                    --mode clausify
% 1.73/1.06  --stdin                                 false
% 1.73/1.06  --stats_out                             all
% 1.73/1.06  
% 1.73/1.06  ------ General Options
% 1.73/1.06  
% 1.73/1.06  --fof                                   false
% 1.73/1.06  --time_out_real                         305.
% 1.73/1.06  --time_out_virtual                      -1.
% 1.73/1.06  --symbol_type_check                     false
% 1.73/1.06  --clausify_out                          false
% 1.73/1.06  --sig_cnt_out                           false
% 1.73/1.06  --trig_cnt_out                          false
% 1.73/1.06  --trig_cnt_out_tolerance                1.
% 1.73/1.06  --trig_cnt_out_sk_spl                   false
% 1.73/1.06  --abstr_cl_out                          false
% 1.73/1.06  
% 1.73/1.06  ------ Global Options
% 1.73/1.06  
% 1.73/1.06  --schedule                              default
% 1.73/1.06  --add_important_lit                     false
% 1.73/1.06  --prop_solver_per_cl                    1000
% 1.73/1.06  --min_unsat_core                        false
% 1.73/1.06  --soft_assumptions                      false
% 1.73/1.06  --soft_lemma_size                       3
% 1.73/1.06  --prop_impl_unit_size                   0
% 1.73/1.06  --prop_impl_unit                        []
% 1.73/1.06  --share_sel_clauses                     true
% 1.73/1.06  --reset_solvers                         false
% 1.73/1.06  --bc_imp_inh                            [conj_cone]
% 1.73/1.06  --conj_cone_tolerance                   3.
% 1.73/1.06  --extra_neg_conj                        none
% 1.73/1.06  --large_theory_mode                     true
% 1.73/1.06  --prolific_symb_bound                   200
% 1.73/1.06  --lt_threshold                          2000
% 1.73/1.06  --clause_weak_htbl                      true
% 1.73/1.06  --gc_record_bc_elim                     false
% 1.73/1.06  
% 1.73/1.06  ------ Preprocessing Options
% 1.73/1.06  
% 1.73/1.06  --preprocessing_flag                    true
% 1.73/1.06  --time_out_prep_mult                    0.1
% 1.73/1.06  --splitting_mode                        input
% 1.73/1.06  --splitting_grd                         true
% 1.73/1.06  --splitting_cvd                         false
% 1.73/1.06  --splitting_cvd_svl                     false
% 1.73/1.06  --splitting_nvd                         32
% 1.73/1.06  --sub_typing                            true
% 1.73/1.06  --prep_gs_sim                           true
% 1.73/1.06  --prep_unflatten                        true
% 1.73/1.06  --prep_res_sim                          true
% 1.73/1.06  --prep_upred                            true
% 1.73/1.06  --prep_sem_filter                       exhaustive
% 1.73/1.06  --prep_sem_filter_out                   false
% 1.73/1.06  --pred_elim                             true
% 1.73/1.06  --res_sim_input                         true
% 1.73/1.06  --eq_ax_congr_red                       true
% 1.73/1.06  --pure_diseq_elim                       true
% 1.73/1.06  --brand_transform                       false
% 1.73/1.06  --non_eq_to_eq                          false
% 1.73/1.06  --prep_def_merge                        true
% 1.73/1.06  --prep_def_merge_prop_impl              false
% 1.73/1.06  --prep_def_merge_mbd                    true
% 1.73/1.06  --prep_def_merge_tr_red                 false
% 1.73/1.06  --prep_def_merge_tr_cl                  false
% 1.73/1.06  --smt_preprocessing                     true
% 1.73/1.06  --smt_ac_axioms                         fast
% 1.73/1.06  --preprocessed_out                      false
% 1.73/1.06  --preprocessed_stats                    false
% 1.73/1.06  
% 1.73/1.06  ------ Abstraction refinement Options
% 1.73/1.06  
% 1.73/1.06  --abstr_ref                             []
% 1.73/1.06  --abstr_ref_prep                        false
% 1.73/1.06  --abstr_ref_until_sat                   false
% 1.73/1.06  --abstr_ref_sig_restrict                funpre
% 1.73/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 1.73/1.06  --abstr_ref_under                       []
% 1.73/1.06  
% 1.73/1.06  ------ SAT Options
% 1.73/1.06  
% 1.73/1.06  --sat_mode                              false
% 1.73/1.06  --sat_fm_restart_options                ""
% 1.73/1.06  --sat_gr_def                            false
% 1.73/1.06  --sat_epr_types                         true
% 1.73/1.06  --sat_non_cyclic_types                  false
% 1.73/1.06  --sat_finite_models                     false
% 1.73/1.06  --sat_fm_lemmas                         false
% 1.73/1.06  --sat_fm_prep                           false
% 1.73/1.06  --sat_fm_uc_incr                        true
% 1.73/1.06  --sat_out_model                         small
% 1.73/1.06  --sat_out_clauses                       false
% 1.73/1.06  
% 1.73/1.06  ------ QBF Options
% 1.73/1.06  
% 1.73/1.06  --qbf_mode                              false
% 1.73/1.06  --qbf_elim_univ                         false
% 1.73/1.06  --qbf_dom_inst                          none
% 1.73/1.06  --qbf_dom_pre_inst                      false
% 1.73/1.06  --qbf_sk_in                             false
% 1.73/1.06  --qbf_pred_elim                         true
% 1.73/1.06  --qbf_split                             512
% 1.73/1.06  
% 1.73/1.06  ------ BMC1 Options
% 1.73/1.06  
% 1.73/1.06  --bmc1_incremental                      false
% 1.73/1.06  --bmc1_axioms                           reachable_all
% 1.73/1.06  --bmc1_min_bound                        0
% 1.73/1.06  --bmc1_max_bound                        -1
% 1.73/1.06  --bmc1_max_bound_default                -1
% 1.73/1.06  --bmc1_symbol_reachability              true
% 1.73/1.06  --bmc1_property_lemmas                  false
% 1.73/1.06  --bmc1_k_induction                      false
% 1.73/1.06  --bmc1_non_equiv_states                 false
% 1.73/1.06  --bmc1_deadlock                         false
% 1.73/1.06  --bmc1_ucm                              false
% 1.73/1.06  --bmc1_add_unsat_core                   none
% 1.73/1.06  --bmc1_unsat_core_children              false
% 1.73/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 1.73/1.06  --bmc1_out_stat                         full
% 1.73/1.06  --bmc1_ground_init                      false
% 1.73/1.06  --bmc1_pre_inst_next_state              false
% 1.73/1.06  --bmc1_pre_inst_state                   false
% 1.73/1.06  --bmc1_pre_inst_reach_state             false
% 1.73/1.06  --bmc1_out_unsat_core                   false
% 1.73/1.06  --bmc1_aig_witness_out                  false
% 1.73/1.06  --bmc1_verbose                          false
% 1.73/1.06  --bmc1_dump_clauses_tptp                false
% 1.73/1.06  --bmc1_dump_unsat_core_tptp             false
% 1.73/1.06  --bmc1_dump_file                        -
% 1.73/1.06  --bmc1_ucm_expand_uc_limit              128
% 1.73/1.06  --bmc1_ucm_n_expand_iterations          6
% 1.73/1.06  --bmc1_ucm_extend_mode                  1
% 1.73/1.06  --bmc1_ucm_init_mode                    2
% 1.73/1.06  --bmc1_ucm_cone_mode                    none
% 1.73/1.06  --bmc1_ucm_reduced_relation_type        0
% 1.73/1.06  --bmc1_ucm_relax_model                  4
% 1.73/1.06  --bmc1_ucm_full_tr_after_sat            true
% 1.73/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 1.73/1.06  --bmc1_ucm_layered_model                none
% 1.73/1.06  --bmc1_ucm_max_lemma_size               10
% 1.73/1.06  
% 1.73/1.06  ------ AIG Options
% 1.73/1.06  
% 1.73/1.06  --aig_mode                              false
% 1.73/1.06  
% 1.73/1.06  ------ Instantiation Options
% 1.73/1.06  
% 1.73/1.06  --instantiation_flag                    true
% 1.73/1.06  --inst_sos_flag                         false
% 1.73/1.06  --inst_sos_phase                        true
% 1.73/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.73/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.73/1.06  --inst_lit_sel_side                     num_symb
% 1.73/1.06  --inst_solver_per_active                1400
% 1.73/1.06  --inst_solver_calls_frac                1.
% 1.73/1.06  --inst_passive_queue_type               priority_queues
% 1.73/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.73/1.06  --inst_passive_queues_freq              [25;2]
% 1.73/1.06  --inst_dismatching                      true
% 1.73/1.06  --inst_eager_unprocessed_to_passive     true
% 1.73/1.06  --inst_prop_sim_given                   true
% 1.73/1.06  --inst_prop_sim_new                     false
% 1.73/1.06  --inst_subs_new                         false
% 1.73/1.06  --inst_eq_res_simp                      false
% 1.73/1.06  --inst_subs_given                       false
% 1.73/1.06  --inst_orphan_elimination               true
% 1.73/1.06  --inst_learning_loop_flag               true
% 1.73/1.06  --inst_learning_start                   3000
% 1.73/1.06  --inst_learning_factor                  2
% 1.73/1.06  --inst_start_prop_sim_after_learn       3
% 1.73/1.06  --inst_sel_renew                        solver
% 1.73/1.06  --inst_lit_activity_flag                true
% 1.73/1.06  --inst_restr_to_given                   false
% 1.73/1.06  --inst_activity_threshold               500
% 1.73/1.06  --inst_out_proof                        true
% 1.73/1.06  
% 1.73/1.06  ------ Resolution Options
% 1.73/1.06  
% 1.73/1.06  --resolution_flag                       true
% 1.73/1.06  --res_lit_sel                           adaptive
% 1.73/1.06  --res_lit_sel_side                      none
% 1.73/1.06  --res_ordering                          kbo
% 1.73/1.06  --res_to_prop_solver                    active
% 1.73/1.06  --res_prop_simpl_new                    false
% 1.73/1.06  --res_prop_simpl_given                  true
% 1.73/1.06  --res_passive_queue_type                priority_queues
% 1.73/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.73/1.06  --res_passive_queues_freq               [15;5]
% 1.73/1.06  --res_forward_subs                      full
% 1.73/1.06  --res_backward_subs                     full
% 1.73/1.06  --res_forward_subs_resolution           true
% 1.73/1.06  --res_backward_subs_resolution          true
% 1.73/1.06  --res_orphan_elimination                true
% 1.73/1.06  --res_time_limit                        2.
% 1.73/1.06  --res_out_proof                         true
% 1.73/1.06  
% 1.73/1.06  ------ Superposition Options
% 1.73/1.06  
% 1.73/1.06  --superposition_flag                    true
% 1.73/1.06  --sup_passive_queue_type                priority_queues
% 1.73/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.73/1.06  --sup_passive_queues_freq               [8;1;4]
% 1.73/1.06  --demod_completeness_check              fast
% 1.73/1.06  --demod_use_ground                      true
% 1.73/1.06  --sup_to_prop_solver                    passive
% 1.73/1.06  --sup_prop_simpl_new                    true
% 1.73/1.06  --sup_prop_simpl_given                  true
% 1.73/1.06  --sup_fun_splitting                     false
% 1.73/1.06  --sup_smt_interval                      50000
% 1.73/1.06  
% 1.73/1.06  ------ Superposition Simplification Setup
% 1.73/1.06  
% 1.73/1.06  --sup_indices_passive                   []
% 1.73/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 1.73/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/1.06  --sup_full_bw                           [BwDemod]
% 1.73/1.06  --sup_immed_triv                        [TrivRules]
% 1.73/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.73/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/1.06  --sup_immed_bw_main                     []
% 1.73/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.73/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 1.73/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.73/1.06  
% 1.73/1.06  ------ Combination Options
% 1.73/1.06  
% 1.73/1.06  --comb_res_mult                         3
% 1.73/1.06  --comb_sup_mult                         2
% 1.73/1.06  --comb_inst_mult                        10
% 1.73/1.06  
% 1.73/1.06  ------ Debug Options
% 1.73/1.06  
% 1.73/1.06  --dbg_backtrace                         false
% 1.73/1.06  --dbg_dump_prop_clauses                 false
% 1.73/1.06  --dbg_dump_prop_clauses_file            -
% 1.73/1.06  --dbg_out_stat                          false
% 1.73/1.06  ------ Parsing...
% 1.73/1.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.73/1.06  
% 1.73/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.73/1.06  
% 1.73/1.06  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.73/1.06  
% 1.73/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.73/1.06  ------ Proving...
% 1.73/1.06  ------ Problem Properties 
% 1.73/1.06  
% 1.73/1.06  
% 1.73/1.06  clauses                                 23
% 1.73/1.06  conjectures                             3
% 1.73/1.06  EPR                                     4
% 1.73/1.06  Horn                                    14
% 1.73/1.06  unary                                   3
% 1.73/1.06  binary                                  2
% 1.73/1.06  lits                                    69
% 1.73/1.06  lits eq                                 3
% 1.73/1.06  fd_pure                                 0
% 1.73/1.06  fd_pseudo                               0
% 1.73/1.06  fd_cond                                 0
% 1.73/1.06  fd_pseudo_cond                          1
% 1.73/1.06  AC symbols                              0
% 1.73/1.06  
% 1.73/1.06  ------ Schedule dynamic 5 is on 
% 1.73/1.06  
% 1.73/1.06  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.73/1.06  
% 1.73/1.06  
% 1.73/1.06  ------ 
% 1.73/1.06  Current options:
% 1.73/1.06  ------ 
% 1.73/1.06  
% 1.73/1.06  ------ Input Options
% 1.73/1.06  
% 1.73/1.06  --out_options                           all
% 1.73/1.06  --tptp_safe_out                         true
% 1.73/1.06  --problem_path                          ""
% 1.73/1.06  --include_path                          ""
% 1.73/1.06  --clausifier                            res/vclausify_rel
% 1.73/1.06  --clausifier_options                    --mode clausify
% 1.73/1.06  --stdin                                 false
% 1.73/1.06  --stats_out                             all
% 1.73/1.06  
% 1.73/1.06  ------ General Options
% 1.73/1.06  
% 1.73/1.06  --fof                                   false
% 1.73/1.06  --time_out_real                         305.
% 1.73/1.06  --time_out_virtual                      -1.
% 1.73/1.06  --symbol_type_check                     false
% 1.73/1.06  --clausify_out                          false
% 1.73/1.06  --sig_cnt_out                           false
% 1.73/1.06  --trig_cnt_out                          false
% 1.73/1.06  --trig_cnt_out_tolerance                1.
% 1.73/1.06  --trig_cnt_out_sk_spl                   false
% 1.73/1.06  --abstr_cl_out                          false
% 1.73/1.06  
% 1.73/1.06  ------ Global Options
% 1.73/1.06  
% 1.73/1.06  --schedule                              default
% 1.73/1.06  --add_important_lit                     false
% 1.73/1.06  --prop_solver_per_cl                    1000
% 1.73/1.06  --min_unsat_core                        false
% 1.73/1.06  --soft_assumptions                      false
% 1.73/1.06  --soft_lemma_size                       3
% 1.73/1.06  --prop_impl_unit_size                   0
% 1.73/1.06  --prop_impl_unit                        []
% 1.73/1.06  --share_sel_clauses                     true
% 1.73/1.06  --reset_solvers                         false
% 1.73/1.06  --bc_imp_inh                            [conj_cone]
% 1.73/1.06  --conj_cone_tolerance                   3.
% 1.73/1.06  --extra_neg_conj                        none
% 1.73/1.06  --large_theory_mode                     true
% 1.73/1.06  --prolific_symb_bound                   200
% 1.73/1.06  --lt_threshold                          2000
% 1.73/1.06  --clause_weak_htbl                      true
% 1.73/1.06  --gc_record_bc_elim                     false
% 1.73/1.06  
% 1.73/1.06  ------ Preprocessing Options
% 1.73/1.06  
% 1.73/1.06  --preprocessing_flag                    true
% 1.73/1.06  --time_out_prep_mult                    0.1
% 1.73/1.06  --splitting_mode                        input
% 1.73/1.06  --splitting_grd                         true
% 1.73/1.06  --splitting_cvd                         false
% 1.73/1.06  --splitting_cvd_svl                     false
% 1.73/1.06  --splitting_nvd                         32
% 1.73/1.06  --sub_typing                            true
% 1.73/1.06  --prep_gs_sim                           true
% 1.73/1.06  --prep_unflatten                        true
% 1.73/1.06  --prep_res_sim                          true
% 1.73/1.06  --prep_upred                            true
% 1.73/1.06  --prep_sem_filter                       exhaustive
% 1.73/1.06  --prep_sem_filter_out                   false
% 1.73/1.06  --pred_elim                             true
% 1.73/1.06  --res_sim_input                         true
% 1.73/1.06  --eq_ax_congr_red                       true
% 1.73/1.06  --pure_diseq_elim                       true
% 1.73/1.06  --brand_transform                       false
% 1.73/1.06  --non_eq_to_eq                          false
% 1.73/1.06  --prep_def_merge                        true
% 1.73/1.06  --prep_def_merge_prop_impl              false
% 1.73/1.06  --prep_def_merge_mbd                    true
% 1.73/1.06  --prep_def_merge_tr_red                 false
% 1.73/1.06  --prep_def_merge_tr_cl                  false
% 1.73/1.06  --smt_preprocessing                     true
% 1.73/1.06  --smt_ac_axioms                         fast
% 1.73/1.06  --preprocessed_out                      false
% 1.73/1.06  --preprocessed_stats                    false
% 1.73/1.06  
% 1.73/1.06  ------ Abstraction refinement Options
% 1.73/1.06  
% 1.73/1.06  --abstr_ref                             []
% 1.73/1.06  --abstr_ref_prep                        false
% 1.73/1.06  --abstr_ref_until_sat                   false
% 1.73/1.06  --abstr_ref_sig_restrict                funpre
% 1.73/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 1.73/1.06  --abstr_ref_under                       []
% 1.73/1.06  
% 1.73/1.06  ------ SAT Options
% 1.73/1.06  
% 1.73/1.06  --sat_mode                              false
% 1.73/1.06  --sat_fm_restart_options                ""
% 1.73/1.06  --sat_gr_def                            false
% 1.73/1.06  --sat_epr_types                         true
% 1.73/1.06  --sat_non_cyclic_types                  false
% 1.73/1.06  --sat_finite_models                     false
% 1.73/1.06  --sat_fm_lemmas                         false
% 1.73/1.06  --sat_fm_prep                           false
% 1.73/1.06  --sat_fm_uc_incr                        true
% 1.73/1.06  --sat_out_model                         small
% 1.73/1.06  --sat_out_clauses                       false
% 1.73/1.06  
% 1.73/1.06  ------ QBF Options
% 1.73/1.06  
% 1.73/1.06  --qbf_mode                              false
% 1.73/1.06  --qbf_elim_univ                         false
% 1.73/1.06  --qbf_dom_inst                          none
% 1.73/1.06  --qbf_dom_pre_inst                      false
% 1.73/1.06  --qbf_sk_in                             false
% 1.73/1.06  --qbf_pred_elim                         true
% 1.73/1.06  --qbf_split                             512
% 1.73/1.06  
% 1.73/1.06  ------ BMC1 Options
% 1.73/1.06  
% 1.73/1.06  --bmc1_incremental                      false
% 1.73/1.06  --bmc1_axioms                           reachable_all
% 1.73/1.06  --bmc1_min_bound                        0
% 1.73/1.06  --bmc1_max_bound                        -1
% 1.73/1.06  --bmc1_max_bound_default                -1
% 1.73/1.06  --bmc1_symbol_reachability              true
% 1.73/1.06  --bmc1_property_lemmas                  false
% 1.73/1.06  --bmc1_k_induction                      false
% 1.73/1.06  --bmc1_non_equiv_states                 false
% 1.73/1.06  --bmc1_deadlock                         false
% 1.73/1.06  --bmc1_ucm                              false
% 1.73/1.06  --bmc1_add_unsat_core                   none
% 1.73/1.06  --bmc1_unsat_core_children              false
% 1.73/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 1.73/1.06  --bmc1_out_stat                         full
% 1.73/1.06  --bmc1_ground_init                      false
% 1.73/1.06  --bmc1_pre_inst_next_state              false
% 1.73/1.06  --bmc1_pre_inst_state                   false
% 1.73/1.06  --bmc1_pre_inst_reach_state             false
% 1.73/1.06  --bmc1_out_unsat_core                   false
% 1.73/1.06  --bmc1_aig_witness_out                  false
% 1.73/1.06  --bmc1_verbose                          false
% 1.73/1.06  --bmc1_dump_clauses_tptp                false
% 1.73/1.06  --bmc1_dump_unsat_core_tptp             false
% 1.73/1.06  --bmc1_dump_file                        -
% 1.73/1.06  --bmc1_ucm_expand_uc_limit              128
% 1.73/1.06  --bmc1_ucm_n_expand_iterations          6
% 1.73/1.06  --bmc1_ucm_extend_mode                  1
% 1.73/1.06  --bmc1_ucm_init_mode                    2
% 1.73/1.06  --bmc1_ucm_cone_mode                    none
% 1.73/1.06  --bmc1_ucm_reduced_relation_type        0
% 1.73/1.06  --bmc1_ucm_relax_model                  4
% 1.73/1.06  --bmc1_ucm_full_tr_after_sat            true
% 1.73/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 1.73/1.06  --bmc1_ucm_layered_model                none
% 1.73/1.06  --bmc1_ucm_max_lemma_size               10
% 1.73/1.06  
% 1.73/1.06  ------ AIG Options
% 1.73/1.06  
% 1.73/1.06  --aig_mode                              false
% 1.73/1.06  
% 1.73/1.06  ------ Instantiation Options
% 1.73/1.06  
% 1.73/1.06  --instantiation_flag                    true
% 1.73/1.06  --inst_sos_flag                         false
% 1.73/1.06  --inst_sos_phase                        true
% 1.73/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.73/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.73/1.06  --inst_lit_sel_side                     none
% 1.73/1.06  --inst_solver_per_active                1400
% 1.73/1.06  --inst_solver_calls_frac                1.
% 1.73/1.06  --inst_passive_queue_type               priority_queues
% 1.73/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.73/1.06  --inst_passive_queues_freq              [25;2]
% 1.73/1.06  --inst_dismatching                      true
% 1.73/1.06  --inst_eager_unprocessed_to_passive     true
% 1.73/1.06  --inst_prop_sim_given                   true
% 1.73/1.06  --inst_prop_sim_new                     false
% 1.73/1.06  --inst_subs_new                         false
% 1.73/1.06  --inst_eq_res_simp                      false
% 1.73/1.06  --inst_subs_given                       false
% 1.73/1.06  --inst_orphan_elimination               true
% 1.73/1.06  --inst_learning_loop_flag               true
% 1.73/1.06  --inst_learning_start                   3000
% 1.73/1.06  --inst_learning_factor                  2
% 1.73/1.06  --inst_start_prop_sim_after_learn       3
% 1.73/1.06  --inst_sel_renew                        solver
% 1.73/1.06  --inst_lit_activity_flag                true
% 1.73/1.06  --inst_restr_to_given                   false
% 1.73/1.06  --inst_activity_threshold               500
% 1.73/1.06  --inst_out_proof                        true
% 1.73/1.06  
% 1.73/1.06  ------ Resolution Options
% 1.73/1.06  
% 1.73/1.06  --resolution_flag                       false
% 1.73/1.06  --res_lit_sel                           adaptive
% 1.73/1.06  --res_lit_sel_side                      none
% 1.73/1.06  --res_ordering                          kbo
% 1.73/1.06  --res_to_prop_solver                    active
% 1.73/1.06  --res_prop_simpl_new                    false
% 1.73/1.06  --res_prop_simpl_given                  true
% 1.73/1.06  --res_passive_queue_type                priority_queues
% 1.73/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.73/1.06  --res_passive_queues_freq               [15;5]
% 1.73/1.06  --res_forward_subs                      full
% 1.73/1.06  --res_backward_subs                     full
% 1.73/1.06  --res_forward_subs_resolution           true
% 1.73/1.06  --res_backward_subs_resolution          true
% 1.73/1.06  --res_orphan_elimination                true
% 1.73/1.06  --res_time_limit                        2.
% 1.73/1.06  --res_out_proof                         true
% 1.73/1.06  
% 1.73/1.06  ------ Superposition Options
% 1.73/1.06  
% 1.73/1.06  --superposition_flag                    true
% 1.73/1.06  --sup_passive_queue_type                priority_queues
% 1.73/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.73/1.06  --sup_passive_queues_freq               [8;1;4]
% 1.73/1.06  --demod_completeness_check              fast
% 1.73/1.06  --demod_use_ground                      true
% 1.73/1.06  --sup_to_prop_solver                    passive
% 1.73/1.06  --sup_prop_simpl_new                    true
% 1.73/1.06  --sup_prop_simpl_given                  true
% 1.73/1.06  --sup_fun_splitting                     false
% 1.73/1.06  --sup_smt_interval                      50000
% 1.73/1.06  
% 1.73/1.06  ------ Superposition Simplification Setup
% 1.73/1.06  
% 1.73/1.06  --sup_indices_passive                   []
% 1.73/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 1.73/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/1.06  --sup_full_bw                           [BwDemod]
% 1.73/1.06  --sup_immed_triv                        [TrivRules]
% 1.73/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.73/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/1.06  --sup_immed_bw_main                     []
% 1.73/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.73/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 1.73/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.73/1.06  
% 1.73/1.06  ------ Combination Options
% 1.73/1.06  
% 1.73/1.06  --comb_res_mult                         3
% 1.73/1.06  --comb_sup_mult                         2
% 1.73/1.06  --comb_inst_mult                        10
% 1.73/1.06  
% 1.73/1.06  ------ Debug Options
% 1.73/1.06  
% 1.73/1.06  --dbg_backtrace                         false
% 1.73/1.06  --dbg_dump_prop_clauses                 false
% 1.73/1.06  --dbg_dump_prop_clauses_file            -
% 1.73/1.06  --dbg_out_stat                          false
% 1.73/1.06  
% 1.73/1.06  
% 1.73/1.06  
% 1.73/1.06  
% 1.73/1.06  ------ Proving...
% 1.73/1.06  
% 1.73/1.06  
% 1.73/1.06  % SZS status Theorem for theBenchmark.p
% 1.73/1.06  
% 1.73/1.06  % SZS output start CNFRefutation for theBenchmark.p
% 1.73/1.06  
% 1.73/1.06  fof(f8,axiom,(
% 1.73/1.06    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.73/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.73/1.06  
% 1.73/1.06  fof(f31,plain,(
% 1.73/1.06    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.73/1.06    inference(ennf_transformation,[],[f8])).
% 1.73/1.06  
% 1.73/1.06  fof(f64,plain,(
% 1.73/1.06    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.73/1.06    inference(cnf_transformation,[],[f31])).
% 1.73/1.06  
% 1.73/1.06  fof(f11,axiom,(
% 1.73/1.06    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.73/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.73/1.06  
% 1.73/1.06  fof(f35,plain,(
% 1.73/1.06    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.73/1.06    inference(ennf_transformation,[],[f11])).
% 1.73/1.06  
% 1.73/1.06  fof(f50,plain,(
% 1.73/1.06    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.73/1.06    inference(nnf_transformation,[],[f35])).
% 1.73/1.06  
% 1.73/1.06  fof(f71,plain,(
% 1.73/1.06    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.73/1.06    inference(cnf_transformation,[],[f50])).
% 1.73/1.06  
% 1.73/1.06  fof(f14,axiom,(
% 1.73/1.06    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v1_subset_1(X2,u1_struct_0(X0)) <=> v1_tex_2(X1,X0))))))),
% 1.73/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.73/1.06  
% 1.73/1.06  fof(f40,plain,(
% 1.73/1.06    ! [X0] : (! [X1] : (! [X2] : (((v1_subset_1(X2,u1_struct_0(X0)) <=> v1_tex_2(X1,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.73/1.06    inference(ennf_transformation,[],[f14])).
% 1.73/1.06  
% 1.73/1.06  fof(f41,plain,(
% 1.73/1.06    ! [X0] : (! [X1] : (! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) <=> v1_tex_2(X1,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.73/1.06    inference(flattening,[],[f40])).
% 1.73/1.06  
% 1.73/1.06  fof(f51,plain,(
% 1.73/1.06    ! [X0] : (! [X1] : (! [X2] : (((v1_subset_1(X2,u1_struct_0(X0)) | ~v1_tex_2(X1,X0)) & (v1_tex_2(X1,X0) | ~v1_subset_1(X2,u1_struct_0(X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.73/1.06    inference(nnf_transformation,[],[f41])).
% 1.73/1.06  
% 1.73/1.06  fof(f76,plain,(
% 1.73/1.06    ( ! [X2,X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.73/1.06    inference(cnf_transformation,[],[f51])).
% 1.73/1.06  
% 1.73/1.06  fof(f86,plain,(
% 1.73/1.06    ( ! [X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.73/1.06    inference(equality_resolution,[],[f76])).
% 1.73/1.06  
% 1.73/1.06  fof(f16,conjecture,(
% 1.73/1.06    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 1.73/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.73/1.06  
% 1.73/1.06  fof(f17,negated_conjecture,(
% 1.73/1.06    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 1.73/1.06    inference(negated_conjecture,[],[f16])).
% 1.73/1.06  
% 1.73/1.06  fof(f44,plain,(
% 1.73/1.06    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.73/1.06    inference(ennf_transformation,[],[f17])).
% 1.73/1.06  
% 1.73/1.06  fof(f45,plain,(
% 1.73/1.06    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.73/1.06    inference(flattening,[],[f44])).
% 1.73/1.06  
% 1.73/1.06  fof(f52,plain,(
% 1.73/1.06    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.73/1.06    inference(nnf_transformation,[],[f45])).
% 1.73/1.06  
% 1.73/1.06  fof(f53,plain,(
% 1.73/1.06    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.73/1.06    inference(flattening,[],[f52])).
% 1.73/1.06  
% 1.73/1.06  fof(f55,plain,(
% 1.73/1.06    ( ! [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),sK2),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,sK2),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),sK2),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,sK2),X0)) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 1.73/1.06    introduced(choice_axiom,[])).
% 1.73/1.06  
% 1.73/1.06  fof(f54,plain,(
% 1.73/1.06    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK1),X1),u1_struct_0(sK1)) | ~v1_tex_2(k1_tex_2(sK1,X1),sK1)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK1),X1),u1_struct_0(sK1)) | v1_tex_2(k1_tex_2(sK1,X1),sK1)) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.73/1.06    introduced(choice_axiom,[])).
% 1.73/1.06  
% 1.73/1.06  fof(f56,plain,(
% 1.73/1.06    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | ~v1_tex_2(k1_tex_2(sK1,sK2),sK1)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | v1_tex_2(k1_tex_2(sK1,sK2),sK1)) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 1.73/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f53,f55,f54])).
% 1.73/1.06  
% 1.73/1.06  fof(f83,plain,(
% 1.73/1.06    ~v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | ~v1_tex_2(k1_tex_2(sK1,sK2),sK1)),
% 1.73/1.06    inference(cnf_transformation,[],[f56])).
% 1.73/1.06  
% 1.73/1.06  fof(f80,plain,(
% 1.73/1.06    l1_pre_topc(sK1)),
% 1.73/1.06    inference(cnf_transformation,[],[f56])).
% 1.73/1.06  
% 1.73/1.06  fof(f79,plain,(
% 1.73/1.06    ~v2_struct_0(sK1)),
% 1.73/1.06    inference(cnf_transformation,[],[f56])).
% 1.73/1.06  
% 1.73/1.06  fof(f81,plain,(
% 1.73/1.06    m1_subset_1(sK2,u1_struct_0(sK1))),
% 1.73/1.06    inference(cnf_transformation,[],[f56])).
% 1.73/1.06  
% 1.73/1.06  fof(f4,axiom,(
% 1.73/1.06    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.73/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.73/1.06  
% 1.73/1.06  fof(f23,plain,(
% 1.73/1.06    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.73/1.06    inference(ennf_transformation,[],[f4])).
% 1.73/1.06  
% 1.73/1.06  fof(f24,plain,(
% 1.73/1.06    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.73/1.06    inference(flattening,[],[f23])).
% 1.73/1.06  
% 1.73/1.06  fof(f60,plain,(
% 1.73/1.06    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.73/1.06    inference(cnf_transformation,[],[f24])).
% 1.73/1.06  
% 1.73/1.06  fof(f2,axiom,(
% 1.73/1.06    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.73/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.73/1.06  
% 1.73/1.06  fof(f21,plain,(
% 1.73/1.06    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.73/1.06    inference(ennf_transformation,[],[f2])).
% 1.73/1.06  
% 1.73/1.06  fof(f58,plain,(
% 1.73/1.06    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.73/1.06    inference(cnf_transformation,[],[f21])).
% 1.73/1.06  
% 1.73/1.06  fof(f5,axiom,(
% 1.73/1.06    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0)) => ~v1_zfmisc_1(u1_struct_0(X0)))),
% 1.73/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.73/1.06  
% 1.73/1.06  fof(f25,plain,(
% 1.73/1.06    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v7_struct_0(X0)))),
% 1.73/1.06    inference(ennf_transformation,[],[f5])).
% 1.73/1.06  
% 1.73/1.06  fof(f26,plain,(
% 1.73/1.06    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 1.73/1.06    inference(flattening,[],[f25])).
% 1.73/1.06  
% 1.73/1.06  fof(f61,plain,(
% 1.73/1.06    ( ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0)) )),
% 1.73/1.06    inference(cnf_transformation,[],[f26])).
% 1.73/1.06  
% 1.73/1.06  fof(f9,axiom,(
% 1.73/1.06    ! [X0] : ((l1_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (~v2_struct_0(X1) => (~v1_tex_2(X1,X0) & ~v2_struct_0(X1)))))),
% 1.73/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.73/1.06  
% 1.73/1.06  fof(f32,plain,(
% 1.73/1.06    ! [X0] : (! [X1] : (((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)))),
% 1.73/1.06    inference(ennf_transformation,[],[f9])).
% 1.73/1.06  
% 1.73/1.06  fof(f33,plain,(
% 1.73/1.06    ! [X0] : (! [X1] : ((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))),
% 1.73/1.06    inference(flattening,[],[f32])).
% 1.73/1.06  
% 1.73/1.06  fof(f66,plain,(
% 1.73/1.06    ( ! [X0,X1] : (~v1_tex_2(X1,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)) )),
% 1.73/1.06    inference(cnf_transformation,[],[f33])).
% 1.73/1.06  
% 1.73/1.06  fof(f82,plain,(
% 1.73/1.06    v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | v1_tex_2(k1_tex_2(sK1,sK2),sK1)),
% 1.73/1.06    inference(cnf_transformation,[],[f56])).
% 1.73/1.06  
% 1.73/1.06  fof(f12,axiom,(
% 1.73/1.06    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.73/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.73/1.06  
% 1.73/1.06  fof(f18,plain,(
% 1.73/1.06    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.73/1.06    inference(pure_predicate_removal,[],[f12])).
% 1.73/1.06  
% 1.73/1.06  fof(f36,plain,(
% 1.73/1.06    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.73/1.06    inference(ennf_transformation,[],[f18])).
% 1.73/1.06  
% 1.73/1.06  fof(f37,plain,(
% 1.73/1.06    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.73/1.06    inference(flattening,[],[f36])).
% 1.73/1.06  
% 1.73/1.06  fof(f73,plain,(
% 1.73/1.06    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.73/1.06    inference(cnf_transformation,[],[f37])).
% 1.73/1.06  
% 1.73/1.06  fof(f13,axiom,(
% 1.73/1.06    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.73/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.73/1.06  
% 1.73/1.06  fof(f19,plain,(
% 1.73/1.06    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.73/1.06    inference(pure_predicate_removal,[],[f13])).
% 1.73/1.06  
% 1.73/1.06  fof(f38,plain,(
% 1.73/1.06    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.73/1.06    inference(ennf_transformation,[],[f19])).
% 1.73/1.06  
% 1.73/1.06  fof(f39,plain,(
% 1.73/1.06    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.73/1.06    inference(flattening,[],[f38])).
% 1.73/1.06  
% 1.73/1.06  fof(f74,plain,(
% 1.73/1.06    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.73/1.06    inference(cnf_transformation,[],[f39])).
% 1.73/1.06  
% 1.73/1.06  fof(f1,axiom,(
% 1.73/1.06    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 1.73/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.73/1.06  
% 1.73/1.06  fof(f20,plain,(
% 1.73/1.06    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 1.73/1.06    inference(ennf_transformation,[],[f1])).
% 1.73/1.06  
% 1.73/1.06  fof(f57,plain,(
% 1.73/1.06    ( ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0)) )),
% 1.73/1.06    inference(cnf_transformation,[],[f20])).
% 1.73/1.06  
% 1.73/1.06  fof(f10,axiom,(
% 1.73/1.06    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 1.73/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.73/1.06  
% 1.73/1.06  fof(f34,plain,(
% 1.73/1.06    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 1.73/1.06    inference(ennf_transformation,[],[f10])).
% 1.73/1.06  
% 1.73/1.06  fof(f46,plain,(
% 1.73/1.06    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 1.73/1.06    inference(nnf_transformation,[],[f34])).
% 1.73/1.06  
% 1.73/1.06  fof(f47,plain,(
% 1.73/1.06    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 1.73/1.06    inference(rectify,[],[f46])).
% 1.73/1.06  
% 1.73/1.06  fof(f48,plain,(
% 1.73/1.06    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK0(X0)) = X0 & m1_subset_1(sK0(X0),X0)))),
% 1.73/1.06    introduced(choice_axiom,[])).
% 1.73/1.06  
% 1.73/1.06  fof(f49,plain,(
% 1.73/1.06    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK0(X0)) = X0 & m1_subset_1(sK0(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 1.73/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).
% 1.73/1.06  
% 1.73/1.06  fof(f69,plain,(
% 1.73/1.06    ( ! [X0,X1] : (v1_zfmisc_1(X0) | k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.73/1.06    inference(cnf_transformation,[],[f49])).
% 1.73/1.06  
% 1.73/1.06  fof(f7,axiom,(
% 1.73/1.06    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.73/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.73/1.06  
% 1.73/1.06  fof(f29,plain,(
% 1.73/1.06    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.73/1.06    inference(ennf_transformation,[],[f7])).
% 1.73/1.06  
% 1.73/1.06  fof(f30,plain,(
% 1.73/1.06    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.73/1.06    inference(flattening,[],[f29])).
% 1.73/1.06  
% 1.73/1.06  fof(f63,plain,(
% 1.73/1.06    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.73/1.06    inference(cnf_transformation,[],[f30])).
% 1.73/1.06  
% 1.73/1.06  fof(f6,axiom,(
% 1.73/1.06    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 1.73/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.73/1.06  
% 1.73/1.06  fof(f27,plain,(
% 1.73/1.06    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 1.73/1.06    inference(ennf_transformation,[],[f6])).
% 1.73/1.06  
% 1.73/1.06  fof(f28,plain,(
% 1.73/1.06    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 1.73/1.06    inference(flattening,[],[f27])).
% 1.73/1.06  
% 1.73/1.06  fof(f62,plain,(
% 1.73/1.06    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 1.73/1.06    inference(cnf_transformation,[],[f28])).
% 1.73/1.06  
% 1.73/1.06  fof(f15,axiom,(
% 1.73/1.06    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 1.73/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.73/1.06  
% 1.73/1.06  fof(f42,plain,(
% 1.73/1.06    ! [X0] : (! [X1] : ((~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0)) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 1.73/1.06    inference(ennf_transformation,[],[f15])).
% 1.73/1.06  
% 1.73/1.06  fof(f43,plain,(
% 1.73/1.06    ! [X0] : (! [X1] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 1.73/1.06    inference(flattening,[],[f42])).
% 1.73/1.06  
% 1.73/1.06  fof(f78,plain,(
% 1.73/1.06    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.73/1.06    inference(cnf_transformation,[],[f43])).
% 1.73/1.06  
% 1.73/1.06  fof(f3,axiom,(
% 1.73/1.06    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.73/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.73/1.06  
% 1.73/1.06  fof(f22,plain,(
% 1.73/1.06    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.73/1.06    inference(ennf_transformation,[],[f3])).
% 1.73/1.06  
% 1.73/1.06  fof(f59,plain,(
% 1.73/1.06    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.73/1.06    inference(cnf_transformation,[],[f22])).
% 1.73/1.06  
% 1.73/1.06  fof(f75,plain,(
% 1.73/1.06    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.73/1.06    inference(cnf_transformation,[],[f39])).
% 1.73/1.06  
% 1.73/1.06  fof(f77,plain,(
% 1.73/1.06    ( ! [X2,X0,X1] : (v1_subset_1(X2,u1_struct_0(X0)) | ~v1_tex_2(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.73/1.06    inference(cnf_transformation,[],[f51])).
% 1.73/1.06  
% 1.73/1.06  fof(f85,plain,(
% 1.73/1.06    ( ! [X0,X1] : (v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~v1_tex_2(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.73/1.06    inference(equality_resolution,[],[f77])).
% 1.73/1.06  
% 1.73/1.06  cnf(c_7,plain,
% 1.73/1.06      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.73/1.06      | ~ m1_pre_topc(X0,X1)
% 1.73/1.06      | ~ l1_pre_topc(X1) ),
% 1.73/1.06      inference(cnf_transformation,[],[f64]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2205,plain,
% 1.73/1.06      ( m1_subset_1(u1_struct_0(X0_46),k1_zfmisc_1(u1_struct_0(X1_46)))
% 1.73/1.06      | ~ m1_pre_topc(X0_46,X1_46)
% 1.73/1.06      | ~ l1_pre_topc(X1_46) ),
% 1.73/1.06      inference(subtyping,[status(esa)],[c_7]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2861,plain,
% 1.73/1.06      ( m1_subset_1(u1_struct_0(X0_46),k1_zfmisc_1(u1_struct_0(X1_46))) = iProver_top
% 1.73/1.06      | m1_pre_topc(X0_46,X1_46) != iProver_top
% 1.73/1.06      | l1_pre_topc(X1_46) != iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_2205]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_13,plain,
% 1.73/1.06      ( v1_subset_1(X0,X1)
% 1.73/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.73/1.06      | X0 = X1 ),
% 1.73/1.06      inference(cnf_transformation,[],[f71]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2202,plain,
% 1.73/1.06      ( v1_subset_1(X0_45,X1_45)
% 1.73/1.06      | ~ m1_subset_1(X0_45,k1_zfmisc_1(X1_45))
% 1.73/1.06      | X0_45 = X1_45 ),
% 1.73/1.06      inference(subtyping,[status(esa)],[c_13]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2864,plain,
% 1.73/1.06      ( X0_45 = X1_45
% 1.73/1.06      | v1_subset_1(X0_45,X1_45) = iProver_top
% 1.73/1.06      | m1_subset_1(X0_45,k1_zfmisc_1(X1_45)) != iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_2202]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3417,plain,
% 1.73/1.06      ( u1_struct_0(X0_46) = u1_struct_0(X1_46)
% 1.73/1.06      | v1_subset_1(u1_struct_0(X1_46),u1_struct_0(X0_46)) = iProver_top
% 1.73/1.06      | m1_pre_topc(X1_46,X0_46) != iProver_top
% 1.73/1.06      | l1_pre_topc(X0_46) != iProver_top ),
% 1.73/1.06      inference(superposition,[status(thm)],[c_2861,c_2864]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_20,plain,
% 1.73/1.06      ( ~ v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 1.73/1.06      | v1_tex_2(X0,X1)
% 1.73/1.06      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.73/1.06      | ~ m1_pre_topc(X0,X1)
% 1.73/1.06      | ~ l1_pre_topc(X1) ),
% 1.73/1.06      inference(cnf_transformation,[],[f86]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_153,plain,
% 1.73/1.06      ( v1_tex_2(X0,X1)
% 1.73/1.06      | ~ v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 1.73/1.06      | ~ m1_pre_topc(X0,X1)
% 1.73/1.06      | ~ l1_pre_topc(X1) ),
% 1.73/1.06      inference(global_propositional_subsumption,
% 1.73/1.06                [status(thm)],
% 1.73/1.06                [c_20,c_7]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_154,plain,
% 1.73/1.06      ( ~ v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 1.73/1.06      | v1_tex_2(X0,X1)
% 1.73/1.06      | ~ m1_pre_topc(X0,X1)
% 1.73/1.06      | ~ l1_pre_topc(X1) ),
% 1.73/1.06      inference(renaming,[status(thm)],[c_153]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_22,negated_conjecture,
% 1.73/1.06      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.73/1.06      | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
% 1.73/1.06      inference(cnf_transformation,[],[f83]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_214,plain,
% 1.73/1.06      ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
% 1.73/1.06      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
% 1.73/1.06      inference(prop_impl,[status(thm)],[c_22]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_215,plain,
% 1.73/1.06      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.73/1.06      | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
% 1.73/1.06      inference(renaming,[status(thm)],[c_214]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_661,plain,
% 1.73/1.06      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.73/1.06      | ~ v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 1.73/1.06      | ~ m1_pre_topc(X0,X1)
% 1.73/1.06      | ~ l1_pre_topc(X1)
% 1.73/1.06      | k1_tex_2(sK1,sK2) != X0
% 1.73/1.06      | sK1 != X1 ),
% 1.73/1.06      inference(resolution_lifted,[status(thm)],[c_154,c_215]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_662,plain,
% 1.73/1.06      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.73/1.06      | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
% 1.73/1.06      | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 1.73/1.06      | ~ l1_pre_topc(sK1) ),
% 1.73/1.06      inference(unflattening,[status(thm)],[c_661]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_25,negated_conjecture,
% 1.73/1.06      ( l1_pre_topc(sK1) ),
% 1.73/1.06      inference(cnf_transformation,[],[f80]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_664,plain,
% 1.73/1.06      ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 1.73/1.06      | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
% 1.73/1.06      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
% 1.73/1.06      inference(global_propositional_subsumption,
% 1.73/1.06                [status(thm)],
% 1.73/1.06                [c_662,c_25]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_665,plain,
% 1.73/1.06      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.73/1.06      | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
% 1.73/1.06      | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1) ),
% 1.73/1.06      inference(renaming,[status(thm)],[c_664]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2189,plain,
% 1.73/1.06      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.73/1.06      | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
% 1.73/1.06      | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1) ),
% 1.73/1.06      inference(subtyping,[status(esa)],[c_665]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2877,plain,
% 1.73/1.06      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
% 1.73/1.06      | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) != iProver_top
% 1.73/1.06      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_2189]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_26,negated_conjecture,
% 1.73/1.06      ( ~ v2_struct_0(sK1) ),
% 1.73/1.06      inference(cnf_transformation,[],[f79]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_27,plain,
% 1.73/1.06      ( v2_struct_0(sK1) != iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_28,plain,
% 1.73/1.06      ( l1_pre_topc(sK1) = iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_24,negated_conjecture,
% 1.73/1.06      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.73/1.06      inference(cnf_transformation,[],[f81]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_29,plain,
% 1.73/1.06      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3,plain,
% 1.73/1.06      ( v2_struct_0(X0)
% 1.73/1.06      | ~ l1_struct_0(X0)
% 1.73/1.06      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.73/1.06      inference(cnf_transformation,[],[f60]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_82,plain,
% 1.73/1.06      ( v2_struct_0(X0) = iProver_top
% 1.73/1.06      | l1_struct_0(X0) != iProver_top
% 1.73/1.06      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_84,plain,
% 1.73/1.06      ( v2_struct_0(sK1) = iProver_top
% 1.73/1.06      | l1_struct_0(sK1) != iProver_top
% 1.73/1.06      | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_82]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1,plain,
% 1.73/1.06      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.73/1.06      inference(cnf_transformation,[],[f58]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_86,plain,
% 1.73/1.06      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_88,plain,
% 1.73/1.06      ( l1_pre_topc(sK1) != iProver_top
% 1.73/1.06      | l1_struct_0(sK1) = iProver_top ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_86]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_663,plain,
% 1.73/1.06      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
% 1.73/1.06      | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) != iProver_top
% 1.73/1.06      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 1.73/1.06      | l1_pre_topc(sK1) != iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_662]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_4,plain,
% 1.73/1.06      ( v7_struct_0(X0)
% 1.73/1.06      | ~ l1_struct_0(X0)
% 1.73/1.06      | ~ v1_zfmisc_1(u1_struct_0(X0)) ),
% 1.73/1.06      inference(cnf_transformation,[],[f61]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_373,plain,
% 1.73/1.06      ( v7_struct_0(X0)
% 1.73/1.06      | ~ l1_pre_topc(X0)
% 1.73/1.06      | ~ v1_zfmisc_1(u1_struct_0(X0)) ),
% 1.73/1.06      inference(resolution,[status(thm)],[c_1,c_4]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_8,plain,
% 1.73/1.06      ( ~ v1_tex_2(X0,X1)
% 1.73/1.06      | ~ m1_pre_topc(X0,X1)
% 1.73/1.06      | ~ v7_struct_0(X1)
% 1.73/1.06      | v2_struct_0(X1)
% 1.73/1.06      | v2_struct_0(X0)
% 1.73/1.06      | ~ l1_pre_topc(X1) ),
% 1.73/1.06      inference(cnf_transformation,[],[f66]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_23,negated_conjecture,
% 1.73/1.06      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.73/1.06      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
% 1.73/1.06      inference(cnf_transformation,[],[f82]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_216,plain,
% 1.73/1.06      ( v1_tex_2(k1_tex_2(sK1,sK2),sK1)
% 1.73/1.06      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
% 1.73/1.06      inference(prop_impl,[status(thm)],[c_23]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_217,plain,
% 1.73/1.06      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.73/1.06      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
% 1.73/1.06      inference(renaming,[status(thm)],[c_216]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_695,plain,
% 1.73/1.06      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.73/1.06      | ~ m1_pre_topc(X0,X1)
% 1.73/1.06      | ~ v7_struct_0(X1)
% 1.73/1.06      | v2_struct_0(X0)
% 1.73/1.06      | v2_struct_0(X1)
% 1.73/1.06      | ~ l1_pre_topc(X1)
% 1.73/1.06      | k1_tex_2(sK1,sK2) != X0
% 1.73/1.06      | sK1 != X1 ),
% 1.73/1.06      inference(resolution_lifted,[status(thm)],[c_8,c_217]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_696,plain,
% 1.73/1.06      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.73/1.06      | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 1.73/1.06      | ~ v7_struct_0(sK1)
% 1.73/1.06      | v2_struct_0(k1_tex_2(sK1,sK2))
% 1.73/1.06      | v2_struct_0(sK1)
% 1.73/1.06      | ~ l1_pre_topc(sK1) ),
% 1.73/1.06      inference(unflattening,[status(thm)],[c_695]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_698,plain,
% 1.73/1.06      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.73/1.06      | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 1.73/1.06      | ~ v7_struct_0(sK1)
% 1.73/1.06      | v2_struct_0(k1_tex_2(sK1,sK2)) ),
% 1.73/1.06      inference(global_propositional_subsumption,
% 1.73/1.06                [status(thm)],
% 1.73/1.06                [c_696,c_26,c_25]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_942,plain,
% 1.73/1.06      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.73/1.06      | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 1.73/1.06      | v2_struct_0(k1_tex_2(sK1,sK2))
% 1.73/1.06      | ~ l1_pre_topc(X0)
% 1.73/1.06      | ~ v1_zfmisc_1(u1_struct_0(X0))
% 1.73/1.06      | sK1 != X0 ),
% 1.73/1.06      inference(resolution_lifted,[status(thm)],[c_373,c_698]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_943,plain,
% 1.73/1.06      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.73/1.06      | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 1.73/1.06      | v2_struct_0(k1_tex_2(sK1,sK2))
% 1.73/1.06      | ~ l1_pre_topc(sK1)
% 1.73/1.06      | ~ v1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.73/1.06      inference(unflattening,[status(thm)],[c_942]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_944,plain,
% 1.73/1.06      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
% 1.73/1.06      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 1.73/1.06      | v2_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
% 1.73/1.06      | l1_pre_topc(sK1) != iProver_top
% 1.73/1.06      | v1_zfmisc_1(u1_struct_0(sK1)) != iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_943]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_15,plain,
% 1.73/1.06      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.73/1.06      | m1_pre_topc(k1_tex_2(X1,X0),X1)
% 1.73/1.06      | v2_struct_0(X1)
% 1.73/1.06      | ~ l1_pre_topc(X1) ),
% 1.73/1.06      inference(cnf_transformation,[],[f73]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2200,plain,
% 1.73/1.06      ( ~ m1_subset_1(X0_45,u1_struct_0(X0_46))
% 1.73/1.06      | m1_pre_topc(k1_tex_2(X0_46,X0_45),X0_46)
% 1.73/1.06      | v2_struct_0(X0_46)
% 1.73/1.06      | ~ l1_pre_topc(X0_46) ),
% 1.73/1.06      inference(subtyping,[status(esa)],[c_15]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2258,plain,
% 1.73/1.06      ( m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
% 1.73/1.06      | m1_pre_topc(k1_tex_2(X0_46,X0_45),X0_46) = iProver_top
% 1.73/1.06      | v2_struct_0(X0_46) = iProver_top
% 1.73/1.06      | l1_pre_topc(X0_46) != iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_2200]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2260,plain,
% 1.73/1.06      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 1.73/1.06      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) = iProver_top
% 1.73/1.06      | v2_struct_0(sK1) = iProver_top
% 1.73/1.06      | l1_pre_topc(sK1) != iProver_top ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_2258]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_18,plain,
% 1.73/1.06      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.73/1.06      | v2_struct_0(X1)
% 1.73/1.06      | ~ v2_struct_0(k1_tex_2(X1,X0))
% 1.73/1.06      | ~ l1_pre_topc(X1) ),
% 1.73/1.06      inference(cnf_transformation,[],[f74]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2199,plain,
% 1.73/1.06      ( ~ m1_subset_1(X0_45,u1_struct_0(X0_46))
% 1.73/1.06      | v2_struct_0(X0_46)
% 1.73/1.06      | ~ v2_struct_0(k1_tex_2(X0_46,X0_45))
% 1.73/1.06      | ~ l1_pre_topc(X0_46) ),
% 1.73/1.06      inference(subtyping,[status(esa)],[c_18]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2261,plain,
% 1.73/1.06      ( m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
% 1.73/1.06      | v2_struct_0(X0_46) = iProver_top
% 1.73/1.06      | v2_struct_0(k1_tex_2(X0_46,X0_45)) != iProver_top
% 1.73/1.06      | l1_pre_topc(X0_46) != iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_2199]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2263,plain,
% 1.73/1.06      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 1.73/1.06      | v2_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
% 1.73/1.06      | v2_struct_0(sK1) = iProver_top
% 1.73/1.06      | l1_pre_topc(sK1) != iProver_top ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_2261]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_0,plain,
% 1.73/1.06      ( ~ v1_xboole_0(X0) | v1_zfmisc_1(X0) ),
% 1.73/1.06      inference(cnf_transformation,[],[f57]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_10,plain,
% 1.73/1.06      ( ~ m1_subset_1(X0,X1)
% 1.73/1.06      | v1_xboole_0(X1)
% 1.73/1.06      | v1_zfmisc_1(X1)
% 1.73/1.06      | k6_domain_1(X1,X0) != X1 ),
% 1.73/1.06      inference(cnf_transformation,[],[f69]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1108,plain,
% 1.73/1.06      ( ~ m1_subset_1(X0,X1)
% 1.73/1.06      | v1_zfmisc_1(X2)
% 1.73/1.06      | v1_zfmisc_1(X1)
% 1.73/1.06      | X1 != X2
% 1.73/1.06      | k6_domain_1(X1,X0) != X1 ),
% 1.73/1.06      inference(resolution_lifted,[status(thm)],[c_0,c_10]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1109,plain,
% 1.73/1.06      ( ~ m1_subset_1(X0,X1)
% 1.73/1.06      | v1_zfmisc_1(X1)
% 1.73/1.06      | k6_domain_1(X1,X0) != X1 ),
% 1.73/1.06      inference(unflattening,[status(thm)],[c_1108]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2186,plain,
% 1.73/1.06      ( ~ m1_subset_1(X0_45,X1_45)
% 1.73/1.06      | v1_zfmisc_1(X1_45)
% 1.73/1.06      | k6_domain_1(X1_45,X0_45) != X1_45 ),
% 1.73/1.06      inference(subtyping,[status(esa)],[c_1109]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3077,plain,
% 1.73/1.06      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.73/1.06      | v1_zfmisc_1(u1_struct_0(sK1))
% 1.73/1.06      | k6_domain_1(u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_2186]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3078,plain,
% 1.73/1.06      ( k6_domain_1(u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 1.73/1.06      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 1.73/1.06      | v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_3077]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_6,plain,
% 1.73/1.06      ( ~ m1_subset_1(X0,X1)
% 1.73/1.06      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 1.73/1.06      | v1_xboole_0(X1) ),
% 1.73/1.06      inference(cnf_transformation,[],[f63]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2206,plain,
% 1.73/1.06      ( ~ m1_subset_1(X0_45,X1_45)
% 1.73/1.06      | m1_subset_1(k6_domain_1(X1_45,X0_45),k1_zfmisc_1(X1_45))
% 1.73/1.06      | v1_xboole_0(X1_45) ),
% 1.73/1.06      inference(subtyping,[status(esa)],[c_6]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3090,plain,
% 1.73/1.06      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.06      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.73/1.06      | v1_xboole_0(u1_struct_0(sK1)) ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_2206]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3091,plain,
% 1.73/1.06      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 1.73/1.06      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 1.73/1.06      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_3090]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3130,plain,
% 1.73/1.06      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.73/1.06      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.06      | k6_domain_1(u1_struct_0(sK1),sK2) = u1_struct_0(sK1) ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_2202]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3131,plain,
% 1.73/1.06      ( k6_domain_1(u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 1.73/1.06      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
% 1.73/1.06      | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_3130]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3734,plain,
% 1.73/1.06      ( v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) != iProver_top ),
% 1.73/1.06      inference(global_propositional_subsumption,
% 1.73/1.06                [status(thm)],
% 1.73/1.06                [c_2877,c_27,c_28,c_29,c_84,c_88,c_663,c_944,c_2260,
% 1.73/1.06                 c_2263,c_3078,c_3091,c_3131]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_4303,plain,
% 1.73/1.06      ( u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
% 1.73/1.06      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 1.73/1.06      | l1_pre_topc(sK1) != iProver_top ),
% 1.73/1.06      inference(superposition,[status(thm)],[c_3417,c_3734]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3093,plain,
% 1.73/1.06      ( m1_subset_1(u1_struct_0(k1_tex_2(X0_46,X0_45)),k1_zfmisc_1(u1_struct_0(X0_46)))
% 1.73/1.06      | ~ m1_pre_topc(k1_tex_2(X0_46,X0_45),X0_46)
% 1.73/1.06      | ~ l1_pre_topc(X0_46) ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_2205]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3094,plain,
% 1.73/1.06      ( m1_subset_1(u1_struct_0(k1_tex_2(X0_46,X0_45)),k1_zfmisc_1(u1_struct_0(X0_46))) = iProver_top
% 1.73/1.06      | m1_pre_topc(k1_tex_2(X0_46,X0_45),X0_46) != iProver_top
% 1.73/1.06      | l1_pre_topc(X0_46) != iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_3093]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3096,plain,
% 1.73/1.06      ( m1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 1.73/1.06      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 1.73/1.06      | l1_pre_topc(sK1) != iProver_top ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_3094]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3156,plain,
% 1.73/1.06      ( v1_subset_1(X0_45,u1_struct_0(sK1))
% 1.73/1.06      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.06      | X0_45 = u1_struct_0(sK1) ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_2202]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3294,plain,
% 1.73/1.06      ( v1_subset_1(u1_struct_0(k1_tex_2(sK1,X0_45)),u1_struct_0(sK1))
% 1.73/1.06      | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK1,X0_45)),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.06      | u1_struct_0(k1_tex_2(sK1,X0_45)) = u1_struct_0(sK1) ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_3156]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3296,plain,
% 1.73/1.06      ( u1_struct_0(k1_tex_2(sK1,X0_45)) = u1_struct_0(sK1)
% 1.73/1.06      | v1_subset_1(u1_struct_0(k1_tex_2(sK1,X0_45)),u1_struct_0(sK1)) = iProver_top
% 1.73/1.06      | m1_subset_1(u1_struct_0(k1_tex_2(sK1,X0_45)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_3294]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3298,plain,
% 1.73/1.06      ( u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
% 1.73/1.06      | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) = iProver_top
% 1.73/1.06      | m1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_3296]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_4313,plain,
% 1.73/1.06      ( u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1) ),
% 1.73/1.06      inference(global_propositional_subsumption,
% 1.73/1.06                [status(thm)],
% 1.73/1.06                [c_4303,c_27,c_28,c_29,c_84,c_88,c_663,c_944,c_2260,
% 1.73/1.06                 c_2263,c_3078,c_3091,c_3096,c_3131,c_3298]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_5,plain,
% 1.73/1.06      ( ~ v7_struct_0(X0)
% 1.73/1.06      | ~ l1_struct_0(X0)
% 1.73/1.06      | v1_zfmisc_1(u1_struct_0(X0)) ),
% 1.73/1.06      inference(cnf_transformation,[],[f62]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_359,plain,
% 1.73/1.06      ( ~ v7_struct_0(X0)
% 1.73/1.06      | ~ l1_pre_topc(X0)
% 1.73/1.06      | v1_zfmisc_1(u1_struct_0(X0)) ),
% 1.73/1.06      inference(resolution,[status(thm)],[c_1,c_5]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2193,plain,
% 1.73/1.06      ( ~ v7_struct_0(X0_46)
% 1.73/1.06      | ~ l1_pre_topc(X0_46)
% 1.73/1.06      | v1_zfmisc_1(u1_struct_0(X0_46)) ),
% 1.73/1.06      inference(subtyping,[status(esa)],[c_359]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2873,plain,
% 1.73/1.06      ( v7_struct_0(X0_46) != iProver_top
% 1.73/1.06      | l1_pre_topc(X0_46) != iProver_top
% 1.73/1.06      | v1_zfmisc_1(u1_struct_0(X0_46)) = iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_2193]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_4327,plain,
% 1.73/1.06      ( v7_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
% 1.73/1.06      | l1_pre_topc(k1_tex_2(sK1,sK2)) != iProver_top
% 1.73/1.06      | v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top ),
% 1.73/1.06      inference(superposition,[status(thm)],[c_4313,c_2873]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_21,plain,
% 1.73/1.06      ( ~ v1_subset_1(k6_domain_1(X0,X1),X0)
% 1.73/1.06      | ~ m1_subset_1(X1,X0)
% 1.73/1.06      | v1_xboole_0(X0)
% 1.73/1.06      | ~ v1_zfmisc_1(X0) ),
% 1.73/1.06      inference(cnf_transformation,[],[f78]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2197,plain,
% 1.73/1.06      ( ~ v1_subset_1(k6_domain_1(X0_45,X1_45),X0_45)
% 1.73/1.06      | ~ m1_subset_1(X1_45,X0_45)
% 1.73/1.06      | v1_xboole_0(X0_45)
% 1.73/1.06      | ~ v1_zfmisc_1(X0_45) ),
% 1.73/1.06      inference(subtyping,[status(esa)],[c_21]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3709,plain,
% 1.73/1.06      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0_46),X0_45),u1_struct_0(X0_46))
% 1.73/1.06      | ~ m1_subset_1(X0_45,u1_struct_0(X0_46))
% 1.73/1.06      | v1_xboole_0(u1_struct_0(X0_46))
% 1.73/1.06      | ~ v1_zfmisc_1(u1_struct_0(X0_46)) ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_2197]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3720,plain,
% 1.73/1.06      ( v1_subset_1(k6_domain_1(u1_struct_0(X0_46),X0_45),u1_struct_0(X0_46)) != iProver_top
% 1.73/1.06      | m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
% 1.73/1.06      | v1_xboole_0(u1_struct_0(X0_46)) = iProver_top
% 1.73/1.06      | v1_zfmisc_1(u1_struct_0(X0_46)) != iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_3709]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3722,plain,
% 1.73/1.06      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
% 1.73/1.06      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 1.73/1.06      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top
% 1.73/1.06      | v1_zfmisc_1(u1_struct_0(sK1)) != iProver_top ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_3720]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2,plain,
% 1.73/1.06      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 1.73/1.06      inference(cnf_transformation,[],[f59]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2207,plain,
% 1.73/1.06      ( ~ m1_pre_topc(X0_46,X1_46)
% 1.73/1.06      | ~ l1_pre_topc(X1_46)
% 1.73/1.06      | l1_pre_topc(X0_46) ),
% 1.73/1.06      inference(subtyping,[status(esa)],[c_2]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3182,plain,
% 1.73/1.06      ( ~ m1_pre_topc(k1_tex_2(X0_46,X0_45),X1_46)
% 1.73/1.06      | ~ l1_pre_topc(X1_46)
% 1.73/1.06      | l1_pre_topc(k1_tex_2(X0_46,X0_45)) ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_2207]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3183,plain,
% 1.73/1.06      ( m1_pre_topc(k1_tex_2(X0_46,X0_45),X1_46) != iProver_top
% 1.73/1.06      | l1_pre_topc(X1_46) != iProver_top
% 1.73/1.06      | l1_pre_topc(k1_tex_2(X0_46,X0_45)) = iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_3182]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3185,plain,
% 1.73/1.06      ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 1.73/1.06      | l1_pre_topc(k1_tex_2(sK1,sK2)) = iProver_top
% 1.73/1.06      | l1_pre_topc(sK1) != iProver_top ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_3183]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_17,plain,
% 1.73/1.06      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.73/1.06      | v7_struct_0(k1_tex_2(X1,X0))
% 1.73/1.06      | v2_struct_0(X1)
% 1.73/1.06      | ~ l1_pre_topc(X1) ),
% 1.73/1.06      inference(cnf_transformation,[],[f75]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2198,plain,
% 1.73/1.06      ( ~ m1_subset_1(X0_45,u1_struct_0(X0_46))
% 1.73/1.06      | v7_struct_0(k1_tex_2(X0_46,X0_45))
% 1.73/1.06      | v2_struct_0(X0_46)
% 1.73/1.06      | ~ l1_pre_topc(X0_46) ),
% 1.73/1.06      inference(subtyping,[status(esa)],[c_17]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2264,plain,
% 1.73/1.06      ( m1_subset_1(X0_45,u1_struct_0(X0_46)) != iProver_top
% 1.73/1.06      | v7_struct_0(k1_tex_2(X0_46,X0_45)) = iProver_top
% 1.73/1.06      | v2_struct_0(X0_46) = iProver_top
% 1.73/1.06      | l1_pre_topc(X0_46) != iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_2198]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2266,plain,
% 1.73/1.06      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 1.73/1.06      | v7_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
% 1.73/1.06      | v2_struct_0(sK1) = iProver_top
% 1.73/1.06      | l1_pre_topc(sK1) != iProver_top ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_2264]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_19,plain,
% 1.73/1.06      ( v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 1.73/1.06      | ~ v1_tex_2(X0,X1)
% 1.73/1.06      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.73/1.06      | ~ m1_pre_topc(X0,X1)
% 1.73/1.06      | ~ l1_pre_topc(X1) ),
% 1.73/1.06      inference(cnf_transformation,[],[f85]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_160,plain,
% 1.73/1.06      ( ~ v1_tex_2(X0,X1)
% 1.73/1.06      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 1.73/1.06      | ~ m1_pre_topc(X0,X1)
% 1.73/1.06      | ~ l1_pre_topc(X1) ),
% 1.73/1.06      inference(global_propositional_subsumption,
% 1.73/1.06                [status(thm)],
% 1.73/1.06                [c_19,c_7]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_161,plain,
% 1.73/1.06      ( v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 1.73/1.06      | ~ v1_tex_2(X0,X1)
% 1.73/1.06      | ~ m1_pre_topc(X0,X1)
% 1.73/1.06      | ~ l1_pre_topc(X1) ),
% 1.73/1.06      inference(renaming,[status(thm)],[c_160]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_678,plain,
% 1.73/1.06      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.73/1.06      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 1.73/1.06      | ~ m1_pre_topc(X0,X1)
% 1.73/1.06      | ~ l1_pre_topc(X1)
% 1.73/1.06      | k1_tex_2(sK1,sK2) != X0
% 1.73/1.06      | sK1 != X1 ),
% 1.73/1.06      inference(resolution_lifted,[status(thm)],[c_161,c_217]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_679,plain,
% 1.73/1.06      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.73/1.06      | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
% 1.73/1.06      | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 1.73/1.06      | ~ l1_pre_topc(sK1) ),
% 1.73/1.06      inference(unflattening,[status(thm)],[c_678]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_681,plain,
% 1.73/1.06      ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 1.73/1.06      | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
% 1.73/1.06      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
% 1.73/1.06      inference(global_propositional_subsumption,
% 1.73/1.06                [status(thm)],
% 1.73/1.06                [c_679,c_25]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_682,plain,
% 1.73/1.06      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.73/1.06      | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
% 1.73/1.06      | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1) ),
% 1.73/1.06      inference(renaming,[status(thm)],[c_681]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_683,plain,
% 1.73/1.06      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
% 1.73/1.06      | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) = iProver_top
% 1.73/1.06      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_682]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(contradiction,plain,
% 1.73/1.06      ( $false ),
% 1.73/1.06      inference(minisat,
% 1.73/1.06                [status(thm)],
% 1.73/1.06                [c_4327,c_3734,c_3722,c_3185,c_2266,c_2260,c_683,c_88,
% 1.73/1.06                 c_84,c_29,c_28,c_27]) ).
% 1.73/1.06  
% 1.73/1.06  
% 1.73/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 1.73/1.06  
% 1.73/1.06  ------                               Statistics
% 1.73/1.06  
% 1.73/1.06  ------ General
% 1.73/1.06  
% 1.73/1.06  abstr_ref_over_cycles:                  0
% 1.73/1.06  abstr_ref_under_cycles:                 0
% 1.73/1.06  gc_basic_clause_elim:                   0
% 1.73/1.06  forced_gc_time:                         0
% 1.73/1.06  parsing_time:                           0.01
% 1.73/1.06  unif_index_cands_time:                  0.
% 1.73/1.06  unif_index_add_time:                    0.
% 1.73/1.06  orderings_time:                         0.
% 1.73/1.06  out_proof_time:                         0.016
% 1.73/1.06  total_time:                             0.136
% 1.73/1.06  num_of_symbols:                         50
% 1.73/1.06  num_of_terms:                           2183
% 1.73/1.06  
% 1.73/1.06  ------ Preprocessing
% 1.73/1.06  
% 1.73/1.06  num_of_splits:                          0
% 1.73/1.06  num_of_split_atoms:                     0
% 1.73/1.06  num_of_reused_defs:                     0
% 1.73/1.06  num_eq_ax_congr_red:                    5
% 1.73/1.06  num_of_sem_filtered_clauses:            1
% 1.73/1.06  num_of_subtypes:                        2
% 1.73/1.06  monotx_restored_types:                  1
% 1.73/1.06  sat_num_of_epr_types:                   0
% 1.73/1.06  sat_num_of_non_cyclic_types:            0
% 1.73/1.06  sat_guarded_non_collapsed_types:        0
% 1.73/1.06  num_pure_diseq_elim:                    0
% 1.73/1.06  simp_replaced_by:                       0
% 1.73/1.06  res_preprocessed:                       125
% 1.73/1.06  prep_upred:                             0
% 1.73/1.06  prep_unflattend:                        78
% 1.73/1.06  smt_new_axioms:                         0
% 1.73/1.06  pred_elim_cands:                        8
% 1.73/1.06  pred_elim:                              2
% 1.73/1.06  pred_elim_cl:                           2
% 1.73/1.06  pred_elim_cycles:                       13
% 1.73/1.06  merged_defs:                            6
% 1.73/1.06  merged_defs_ncl:                        0
% 1.73/1.06  bin_hyper_res:                          7
% 1.73/1.06  prep_cycles:                            4
% 1.73/1.06  pred_elim_time:                         0.027
% 1.73/1.06  splitting_time:                         0.
% 1.73/1.06  sem_filter_time:                        0.
% 1.73/1.06  monotx_time:                            0.
% 1.73/1.06  subtype_inf_time:                       0.001
% 1.73/1.06  
% 1.73/1.06  ------ Problem properties
% 1.73/1.06  
% 1.73/1.06  clauses:                                23
% 1.73/1.06  conjectures:                            3
% 1.73/1.06  epr:                                    4
% 1.73/1.06  horn:                                   14
% 1.73/1.06  ground:                                 6
% 1.73/1.06  unary:                                  3
% 1.73/1.06  binary:                                 2
% 1.73/1.06  lits:                                   69
% 1.73/1.06  lits_eq:                                3
% 1.73/1.06  fd_pure:                                0
% 1.73/1.06  fd_pseudo:                              0
% 1.73/1.06  fd_cond:                                0
% 1.73/1.06  fd_pseudo_cond:                         1
% 1.73/1.06  ac_symbols:                             0
% 1.73/1.06  
% 1.73/1.06  ------ Propositional Solver
% 1.73/1.06  
% 1.73/1.06  prop_solver_calls:                      27
% 1.73/1.06  prop_fast_solver_calls:                 1246
% 1.73/1.06  smt_solver_calls:                       0
% 1.73/1.06  smt_fast_solver_calls:                  0
% 1.73/1.06  prop_num_of_clauses:                    872
% 1.73/1.06  prop_preprocess_simplified:             4561
% 1.73/1.06  prop_fo_subsumed:                       42
% 1.73/1.06  prop_solver_time:                       0.
% 1.73/1.06  smt_solver_time:                        0.
% 1.73/1.06  smt_fast_solver_time:                   0.
% 1.73/1.06  prop_fast_solver_time:                  0.
% 1.73/1.06  prop_unsat_core_time:                   0.
% 1.73/1.06  
% 1.73/1.06  ------ QBF
% 1.73/1.06  
% 1.73/1.06  qbf_q_res:                              0
% 1.73/1.06  qbf_num_tautologies:                    0
% 1.73/1.06  qbf_prep_cycles:                        0
% 1.73/1.06  
% 1.73/1.06  ------ BMC1
% 1.73/1.06  
% 1.73/1.06  bmc1_current_bound:                     -1
% 1.73/1.06  bmc1_last_solved_bound:                 -1
% 1.73/1.06  bmc1_unsat_core_size:                   -1
% 1.73/1.06  bmc1_unsat_core_parents_size:           -1
% 1.73/1.06  bmc1_merge_next_fun:                    0
% 1.73/1.06  bmc1_unsat_core_clauses_time:           0.
% 1.73/1.06  
% 1.73/1.06  ------ Instantiation
% 1.73/1.06  
% 1.73/1.06  inst_num_of_clauses:                    207
% 1.73/1.06  inst_num_in_passive:                    9
% 1.73/1.06  inst_num_in_active:                     151
% 1.73/1.06  inst_num_in_unprocessed:                47
% 1.73/1.06  inst_num_of_loops:                      160
% 1.73/1.06  inst_num_of_learning_restarts:          0
% 1.73/1.06  inst_num_moves_active_passive:          6
% 1.73/1.06  inst_lit_activity:                      0
% 1.73/1.06  inst_lit_activity_moves:                0
% 1.73/1.06  inst_num_tautologies:                   0
% 1.73/1.06  inst_num_prop_implied:                  0
% 1.73/1.06  inst_num_existing_simplified:           0
% 1.73/1.06  inst_num_eq_res_simplified:             0
% 1.73/1.06  inst_num_child_elim:                    0
% 1.73/1.06  inst_num_of_dismatching_blockings:      43
% 1.73/1.06  inst_num_of_non_proper_insts:           222
% 1.73/1.06  inst_num_of_duplicates:                 0
% 1.73/1.06  inst_inst_num_from_inst_to_res:         0
% 1.73/1.06  inst_dismatching_checking_time:         0.
% 1.73/1.06  
% 1.73/1.06  ------ Resolution
% 1.73/1.06  
% 1.73/1.06  res_num_of_clauses:                     0
% 1.73/1.06  res_num_in_passive:                     0
% 1.73/1.06  res_num_in_active:                      0
% 1.73/1.06  res_num_of_loops:                       129
% 1.73/1.06  res_forward_subset_subsumed:            27
% 1.73/1.06  res_backward_subset_subsumed:           0
% 1.73/1.06  res_forward_subsumed:                   1
% 1.73/1.06  res_backward_subsumed:                  1
% 1.73/1.06  res_forward_subsumption_resolution:     3
% 1.73/1.06  res_backward_subsumption_resolution:    0
% 1.73/1.06  res_clause_to_clause_subsumption:       107
% 1.73/1.06  res_orphan_elimination:                 0
% 1.73/1.06  res_tautology_del:                      88
% 1.73/1.06  res_num_eq_res_simplified:              0
% 1.73/1.06  res_num_sel_changes:                    0
% 1.73/1.06  res_moves_from_active_to_pass:          0
% 1.73/1.06  
% 1.73/1.06  ------ Superposition
% 1.73/1.06  
% 1.73/1.06  sup_time_total:                         0.
% 1.73/1.06  sup_time_generating:                    0.
% 1.73/1.06  sup_time_sim_full:                      0.
% 1.73/1.06  sup_time_sim_immed:                     0.
% 1.73/1.06  
% 1.73/1.06  sup_num_of_clauses:                     48
% 1.73/1.06  sup_num_in_active:                      31
% 1.73/1.06  sup_num_in_passive:                     17
% 1.73/1.06  sup_num_of_loops:                       31
% 1.73/1.06  sup_fw_superposition:                   15
% 1.73/1.06  sup_bw_superposition:                   18
% 1.73/1.06  sup_immediate_simplified:               3
% 1.73/1.06  sup_given_eliminated:                   0
% 1.73/1.06  comparisons_done:                       0
% 1.73/1.06  comparisons_avoided:                    0
% 1.73/1.06  
% 1.73/1.06  ------ Simplifications
% 1.73/1.06  
% 1.73/1.06  
% 1.73/1.06  sim_fw_subset_subsumed:                 2
% 1.73/1.06  sim_bw_subset_subsumed:                 0
% 1.73/1.06  sim_fw_subsumed:                        0
% 1.73/1.06  sim_bw_subsumed:                        0
% 1.73/1.06  sim_fw_subsumption_res:                 0
% 1.73/1.06  sim_bw_subsumption_res:                 0
% 1.73/1.06  sim_tautology_del:                      1
% 1.73/1.06  sim_eq_tautology_del:                   1
% 1.73/1.06  sim_eq_res_simp:                        0
% 1.73/1.06  sim_fw_demodulated:                     2
% 1.73/1.06  sim_bw_demodulated:                     1
% 1.73/1.06  sim_light_normalised:                   0
% 1.73/1.06  sim_joinable_taut:                      0
% 1.73/1.06  sim_joinable_simp:                      0
% 1.73/1.06  sim_ac_normalised:                      0
% 1.73/1.06  sim_smt_subsumption:                    0
% 1.73/1.06  
%------------------------------------------------------------------------------
