%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:40 EST 2020

% Result     : Theorem 1.33s
% Output     : CNFRefutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 602 expanded)
%              Number of clauses        :   77 ( 167 expanded)
%              Number of leaves         :   18 ( 129 expanded)
%              Depth                    :   22
%              Number of atoms          :  596 (3217 expanded)
%              Number of equality atoms :   54 ( 113 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   14 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ~ v1_xboole_0(X1)
           => ( ~ v1_subset_1(X1,u1_struct_0(X0))
              & ~ v1_xboole_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_subset_1(X1,u1_struct_0(X0))
            & ~ v1_xboole_0(X1) )
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_subset_1(X1,u1_struct_0(X0))
            & ~ v1_xboole_0(X1) )
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,u1_struct_0(X0))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( ~ v1_tex_2(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( ~ v7_struct_0(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v7_struct_0(X1)
            & ~ v2_struct_0(X1) )
          | v1_tex_2(X1,X0)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v7_struct_0(X1)
            & ~ v2_struct_0(X1) )
          | v1_tex_2(X1,X0)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v7_struct_0(X1)
      | v1_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),sK1),u1_struct_0(X0))
          | ~ v1_tex_2(k1_tex_2(X0,sK1),X0) )
        & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),sK1),u1_struct_0(X0))
          | v1_tex_2(k1_tex_2(X0,sK1),X0) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
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
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
            | ~ v1_tex_2(k1_tex_2(sK0,X1),sK0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
            | v1_tex_2(k1_tex_2(sK0,X1),sK0) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).

fof(f66,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f62,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f63,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f64,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v7_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ~ ( v1_tex_2(X1,X0)
              & u1_struct_0(X0) = u1_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_tex_2(X1,X0)
          | u1_struct_0(X0) != u1_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_tex_2(X1,X0)
          | u1_struct_0(X0) != u1_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_tex_2(X1,X0)
      | u1_struct_0(X0) != u1_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f65,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v7_struct_0(X0)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_347,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_0,c_2])).

cnf(c_1502,plain,
    ( v2_struct_0(X0_44)
    | ~ v1_xboole_0(u1_struct_0(X0_44))
    | ~ l1_pre_topc(X0_44) ),
    inference(subtyping,[status(esa)],[c_347])).

cnf(c_2179,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ l1_pre_topc(k1_tex_2(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1502])).

cnf(c_6,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v7_struct_0(X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_361,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v7_struct_0(X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_pre_topc(X2)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_6])).

cnf(c_362,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v7_struct_0(X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_361])).

cnf(c_1501,plain,
    ( ~ v1_subset_1(X0_43,u1_struct_0(X0_44))
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
    | ~ v7_struct_0(X0_44)
    | v2_struct_0(X0_44)
    | v1_xboole_0(X0_43)
    | ~ l1_pre_topc(X0_44) ),
    inference(subtyping,[status(esa)],[c_362])).

cnf(c_2104,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v7_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1501])).

cnf(c_8,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1511,plain,
    ( v1_subset_1(X0_43,X1_43)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
    | X0_43 = X1_43 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2058,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(k1_tex_2(sK0,sK1)) = u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1511])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_pre_topc(k1_tex_2(X1,X0),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_4,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v7_struct_0(X0)
    | v7_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_17,negated_conjecture,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_155,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_156,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(renaming,[status(thm)],[c_155])).

cnf(c_467,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_pre_topc(X0,X1)
    | ~ v7_struct_0(X0)
    | v7_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k1_tex_2(sK0,sK1) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_156])).

cnf(c_468,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ v7_struct_0(k1_tex_2(sK0,sK1))
    | v7_struct_0(sK0)
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_467])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_470,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ v7_struct_0(k1_tex_2(sK0,sK1))
    | v7_struct_0(sK0)
    | v2_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_468,c_21,c_20])).

cnf(c_612,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v7_struct_0(k1_tex_2(sK0,sK1))
    | v7_struct_0(sK0)
    | v2_struct_0(X1)
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(X1)
    | k1_tex_2(X1,X0) != k1_tex_2(sK0,sK1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_470])).

cnf(c_613,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ v7_struct_0(k1_tex_2(sK0,sK1))
    | v7_struct_0(sK0)
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | k1_tex_2(sK0,X0) != k1_tex_2(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_612])).

cnf(c_617,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ v7_struct_0(k1_tex_2(sK0,sK1))
    | v7_struct_0(sK0)
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | k1_tex_2(sK0,X0) != k1_tex_2(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_613,c_21,c_20])).

cnf(c_1496,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(X0_43,u1_struct_0(sK0))
    | ~ v7_struct_0(k1_tex_2(sK0,sK1))
    | v7_struct_0(sK0)
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | k1_tex_2(sK0,X0_43) != k1_tex_2(sK0,sK1) ),
    inference(subtyping,[status(esa)],[c_617])).

cnf(c_1514,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ v7_struct_0(k1_tex_2(sK0,sK1))
    | v7_struct_0(sK0)
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1496])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1528,plain,
    ( X0_44 != X1_44
    | k1_tex_2(X0_44,X0_43) = k1_tex_2(X1_44,X1_43)
    | X0_43 != X1_43 ),
    theory(equality)).

cnf(c_1538,plain,
    ( k1_tex_2(sK0,sK1) = k1_tex_2(sK0,sK1)
    | sK0 != sK0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1528])).

cnf(c_1516,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_1541,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1516])).

cnf(c_1517,plain,
    ( X0_44 = X0_44 ),
    theory(equality)).

cnf(c_1542,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1517])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1509,plain,
    ( ~ m1_subset_1(X0_43,u1_struct_0(X0_44))
    | v2_struct_0(X0_44)
    | ~ v2_struct_0(k1_tex_2(X0_44,X0_43))
    | ~ l1_pre_topc(X0_44) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1548,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1509])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v7_struct_0(k1_tex_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1508,plain,
    ( ~ m1_subset_1(X0_43,u1_struct_0(X0_44))
    | v7_struct_0(k1_tex_2(X0_44,X0_43))
    | v2_struct_0(X0_44)
    | ~ l1_pre_topc(X0_44) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1551,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v7_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1508])).

cnf(c_16,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v7_struct_0(X0)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_307,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v7_struct_0(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_0,c_16])).

cnf(c_1504,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(X0_44),X0_43),u1_struct_0(X0_44))
    | ~ m1_subset_1(X0_43,u1_struct_0(X0_44))
    | v7_struct_0(X0_44)
    | v2_struct_0(X0_44)
    | ~ l1_pre_topc(X0_44) ),
    inference(subtyping,[status(esa)],[c_307])).

cnf(c_1557,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v7_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1504])).

cnf(c_14,plain,
    ( ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_18,negated_conjecture,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_157,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_158,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(renaming,[status(thm)],[c_157])).

cnf(c_490,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | k1_tex_2(sK0,sK1) != X0
    | u1_struct_0(X1) != u1_struct_0(X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_158])).

cnf(c_491,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(sK0) != u1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_493,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | u1_struct_0(sK0) != u1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_491,c_20])).

cnf(c_494,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | u1_struct_0(sK0) != u1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(renaming,[status(thm)],[c_493])).

cnf(c_588,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k1_tex_2(X1,X0) != k1_tex_2(sK0,sK1)
    | u1_struct_0(k1_tex_2(sK0,sK1)) != u1_struct_0(sK0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_494])).

cnf(c_589,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | k1_tex_2(sK0,X0) != k1_tex_2(sK0,sK1)
    | u1_struct_0(k1_tex_2(sK0,sK1)) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_588])).

cnf(c_593,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k1_tex_2(sK0,X0) != k1_tex_2(sK0,sK1)
    | u1_struct_0(k1_tex_2(sK0,sK1)) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_589,c_21,c_20])).

cnf(c_1497,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(X0_43,u1_struct_0(sK0))
    | k1_tex_2(sK0,X0_43) != k1_tex_2(sK0,sK1)
    | u1_struct_0(k1_tex_2(sK0,sK1)) != u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_593])).

cnf(c_1512,plain,
    ( ~ m1_subset_1(X0_43,u1_struct_0(sK0))
    | k1_tex_2(sK0,X0_43) != k1_tex_2(sK0,sK1)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1497])).

cnf(c_1577,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ sP0_iProver_split
    | k1_tex_2(sK0,sK1) != k1_tex_2(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1512])).

cnf(c_1634,plain,
    ( v7_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1514,c_21,c_20,c_19,c_1538,c_1541,c_1542,c_1548,c_1551,c_1557,c_1577])).

cnf(c_1513,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | sP0_iProver_split
    | u1_struct_0(k1_tex_2(sK0,sK1)) != u1_struct_0(sK0) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1497])).

cnf(c_15,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v7_struct_0(X0)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_327,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v7_struct_0(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_0,c_15])).

cnf(c_1503,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0_44),X0_43),u1_struct_0(X0_44))
    | ~ m1_subset_1(X0_43,u1_struct_0(X0_44))
    | ~ v7_struct_0(X0_44)
    | v2_struct_0(X0_44)
    | ~ l1_pre_topc(X0_44) ),
    inference(subtyping,[status(esa)],[c_327])).

cnf(c_1560,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v7_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1503])).

cnf(c_1626,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1513,c_21,c_20,c_19,c_1538,c_1541,c_1542,c_1548,c_1551,c_1557,c_1560,c_1577,c_1514])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_570,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X3)
    | X1 != X2
    | k1_tex_2(X1,X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_10])).

cnf(c_571,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k1_tex_2(X1,X0)) ),
    inference(unflattening,[status(thm)],[c_570])).

cnf(c_1498,plain,
    ( ~ m1_subset_1(X0_43,u1_struct_0(X0_44))
    | v2_struct_0(X0_44)
    | ~ l1_pre_topc(X0_44)
    | l1_pre_topc(k1_tex_2(X0_44,X0_43)) ),
    inference(subtyping,[status(esa)],[c_571])).

cnf(c_1573,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | l1_pre_topc(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1498])).

cnf(c_3,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_552,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X3)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | X1 != X3
    | k1_tex_2(X1,X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_10])).

cnf(c_553,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(u1_struct_0(k1_tex_2(X1,X0)),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_552])).

cnf(c_1499,plain,
    ( ~ m1_subset_1(X0_43,u1_struct_0(X0_44))
    | m1_subset_1(u1_struct_0(k1_tex_2(X0_44,X0_43)),k1_zfmisc_1(u1_struct_0(X0_44)))
    | v2_struct_0(X0_44)
    | ~ l1_pre_topc(X0_44) ),
    inference(subtyping,[status(esa)],[c_553])).

cnf(c_1570,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1499])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2179,c_2104,c_2058,c_1634,c_1626,c_1573,c_1570,c_1548,c_19,c_20,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:37:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.33/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.33/0.99  
% 1.33/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.33/0.99  
% 1.33/0.99  ------  iProver source info
% 1.33/0.99  
% 1.33/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.33/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.33/0.99  git: non_committed_changes: false
% 1.33/0.99  git: last_make_outside_of_git: false
% 1.33/0.99  
% 1.33/0.99  ------ 
% 1.33/0.99  
% 1.33/0.99  ------ Input Options
% 1.33/0.99  
% 1.33/0.99  --out_options                           all
% 1.33/0.99  --tptp_safe_out                         true
% 1.33/0.99  --problem_path                          ""
% 1.33/0.99  --include_path                          ""
% 1.33/0.99  --clausifier                            res/vclausify_rel
% 1.33/0.99  --clausifier_options                    --mode clausify
% 1.33/0.99  --stdin                                 false
% 1.33/0.99  --stats_out                             all
% 1.33/0.99  
% 1.33/0.99  ------ General Options
% 1.33/0.99  
% 1.33/0.99  --fof                                   false
% 1.33/0.99  --time_out_real                         305.
% 1.33/0.99  --time_out_virtual                      -1.
% 1.33/0.99  --symbol_type_check                     false
% 1.33/0.99  --clausify_out                          false
% 1.33/0.99  --sig_cnt_out                           false
% 1.33/0.99  --trig_cnt_out                          false
% 1.33/0.99  --trig_cnt_out_tolerance                1.
% 1.33/0.99  --trig_cnt_out_sk_spl                   false
% 1.33/0.99  --abstr_cl_out                          false
% 1.33/0.99  
% 1.33/0.99  ------ Global Options
% 1.33/0.99  
% 1.33/0.99  --schedule                              default
% 1.33/0.99  --add_important_lit                     false
% 1.33/0.99  --prop_solver_per_cl                    1000
% 1.33/0.99  --min_unsat_core                        false
% 1.33/0.99  --soft_assumptions                      false
% 1.33/0.99  --soft_lemma_size                       3
% 1.33/0.99  --prop_impl_unit_size                   0
% 1.33/0.99  --prop_impl_unit                        []
% 1.33/0.99  --share_sel_clauses                     true
% 1.33/0.99  --reset_solvers                         false
% 1.33/0.99  --bc_imp_inh                            [conj_cone]
% 1.33/0.99  --conj_cone_tolerance                   3.
% 1.33/0.99  --extra_neg_conj                        none
% 1.33/0.99  --large_theory_mode                     true
% 1.33/0.99  --prolific_symb_bound                   200
% 1.33/0.99  --lt_threshold                          2000
% 1.33/0.99  --clause_weak_htbl                      true
% 1.33/0.99  --gc_record_bc_elim                     false
% 1.33/0.99  
% 1.33/0.99  ------ Preprocessing Options
% 1.33/0.99  
% 1.33/0.99  --preprocessing_flag                    true
% 1.33/0.99  --time_out_prep_mult                    0.1
% 1.33/0.99  --splitting_mode                        input
% 1.33/0.99  --splitting_grd                         true
% 1.33/0.99  --splitting_cvd                         false
% 1.33/0.99  --splitting_cvd_svl                     false
% 1.33/0.99  --splitting_nvd                         32
% 1.33/0.99  --sub_typing                            true
% 1.33/0.99  --prep_gs_sim                           true
% 1.33/0.99  --prep_unflatten                        true
% 1.33/0.99  --prep_res_sim                          true
% 1.33/0.99  --prep_upred                            true
% 1.33/0.99  --prep_sem_filter                       exhaustive
% 1.33/0.99  --prep_sem_filter_out                   false
% 1.33/0.99  --pred_elim                             true
% 1.33/0.99  --res_sim_input                         true
% 1.33/0.99  --eq_ax_congr_red                       true
% 1.33/0.99  --pure_diseq_elim                       true
% 1.33/0.99  --brand_transform                       false
% 1.33/0.99  --non_eq_to_eq                          false
% 1.33/0.99  --prep_def_merge                        true
% 1.33/0.99  --prep_def_merge_prop_impl              false
% 1.33/0.99  --prep_def_merge_mbd                    true
% 1.33/0.99  --prep_def_merge_tr_red                 false
% 1.33/0.99  --prep_def_merge_tr_cl                  false
% 1.33/0.99  --smt_preprocessing                     true
% 1.33/0.99  --smt_ac_axioms                         fast
% 1.33/0.99  --preprocessed_out                      false
% 1.33/0.99  --preprocessed_stats                    false
% 1.33/0.99  
% 1.33/0.99  ------ Abstraction refinement Options
% 1.33/0.99  
% 1.33/0.99  --abstr_ref                             []
% 1.33/0.99  --abstr_ref_prep                        false
% 1.33/0.99  --abstr_ref_until_sat                   false
% 1.33/0.99  --abstr_ref_sig_restrict                funpre
% 1.33/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.33/0.99  --abstr_ref_under                       []
% 1.33/0.99  
% 1.33/0.99  ------ SAT Options
% 1.33/0.99  
% 1.33/0.99  --sat_mode                              false
% 1.33/0.99  --sat_fm_restart_options                ""
% 1.33/0.99  --sat_gr_def                            false
% 1.33/0.99  --sat_epr_types                         true
% 1.33/0.99  --sat_non_cyclic_types                  false
% 1.33/0.99  --sat_finite_models                     false
% 1.33/0.99  --sat_fm_lemmas                         false
% 1.33/0.99  --sat_fm_prep                           false
% 1.33/0.99  --sat_fm_uc_incr                        true
% 1.33/0.99  --sat_out_model                         small
% 1.33/0.99  --sat_out_clauses                       false
% 1.33/0.99  
% 1.33/0.99  ------ QBF Options
% 1.33/0.99  
% 1.33/0.99  --qbf_mode                              false
% 1.33/0.99  --qbf_elim_univ                         false
% 1.33/0.99  --qbf_dom_inst                          none
% 1.33/0.99  --qbf_dom_pre_inst                      false
% 1.33/0.99  --qbf_sk_in                             false
% 1.33/0.99  --qbf_pred_elim                         true
% 1.33/0.99  --qbf_split                             512
% 1.33/0.99  
% 1.33/0.99  ------ BMC1 Options
% 1.33/0.99  
% 1.33/0.99  --bmc1_incremental                      false
% 1.33/0.99  --bmc1_axioms                           reachable_all
% 1.33/0.99  --bmc1_min_bound                        0
% 1.33/0.99  --bmc1_max_bound                        -1
% 1.33/0.99  --bmc1_max_bound_default                -1
% 1.33/0.99  --bmc1_symbol_reachability              true
% 1.33/0.99  --bmc1_property_lemmas                  false
% 1.33/0.99  --bmc1_k_induction                      false
% 1.33/0.99  --bmc1_non_equiv_states                 false
% 1.33/0.99  --bmc1_deadlock                         false
% 1.33/0.99  --bmc1_ucm                              false
% 1.33/0.99  --bmc1_add_unsat_core                   none
% 1.33/0.99  --bmc1_unsat_core_children              false
% 1.33/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.33/0.99  --bmc1_out_stat                         full
% 1.33/0.99  --bmc1_ground_init                      false
% 1.33/0.99  --bmc1_pre_inst_next_state              false
% 1.33/0.99  --bmc1_pre_inst_state                   false
% 1.33/0.99  --bmc1_pre_inst_reach_state             false
% 1.33/0.99  --bmc1_out_unsat_core                   false
% 1.33/0.99  --bmc1_aig_witness_out                  false
% 1.33/0.99  --bmc1_verbose                          false
% 1.33/0.99  --bmc1_dump_clauses_tptp                false
% 1.33/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.33/0.99  --bmc1_dump_file                        -
% 1.33/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.33/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.33/0.99  --bmc1_ucm_extend_mode                  1
% 1.33/0.99  --bmc1_ucm_init_mode                    2
% 1.33/0.99  --bmc1_ucm_cone_mode                    none
% 1.33/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.33/0.99  --bmc1_ucm_relax_model                  4
% 1.33/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.33/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.33/0.99  --bmc1_ucm_layered_model                none
% 1.33/0.99  --bmc1_ucm_max_lemma_size               10
% 1.33/0.99  
% 1.33/0.99  ------ AIG Options
% 1.33/0.99  
% 1.33/0.99  --aig_mode                              false
% 1.33/0.99  
% 1.33/0.99  ------ Instantiation Options
% 1.33/0.99  
% 1.33/0.99  --instantiation_flag                    true
% 1.33/0.99  --inst_sos_flag                         false
% 1.33/0.99  --inst_sos_phase                        true
% 1.33/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.33/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.33/0.99  --inst_lit_sel_side                     num_symb
% 1.33/0.99  --inst_solver_per_active                1400
% 1.33/0.99  --inst_solver_calls_frac                1.
% 1.33/0.99  --inst_passive_queue_type               priority_queues
% 1.33/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.33/0.99  --inst_passive_queues_freq              [25;2]
% 1.33/0.99  --inst_dismatching                      true
% 1.33/0.99  --inst_eager_unprocessed_to_passive     true
% 1.33/0.99  --inst_prop_sim_given                   true
% 1.33/0.99  --inst_prop_sim_new                     false
% 1.33/0.99  --inst_subs_new                         false
% 1.33/0.99  --inst_eq_res_simp                      false
% 1.33/0.99  --inst_subs_given                       false
% 1.33/0.99  --inst_orphan_elimination               true
% 1.33/0.99  --inst_learning_loop_flag               true
% 1.33/0.99  --inst_learning_start                   3000
% 1.33/0.99  --inst_learning_factor                  2
% 1.33/0.99  --inst_start_prop_sim_after_learn       3
% 1.33/0.99  --inst_sel_renew                        solver
% 1.33/0.99  --inst_lit_activity_flag                true
% 1.33/0.99  --inst_restr_to_given                   false
% 1.33/0.99  --inst_activity_threshold               500
% 1.33/0.99  --inst_out_proof                        true
% 1.33/0.99  
% 1.33/0.99  ------ Resolution Options
% 1.33/0.99  
% 1.33/0.99  --resolution_flag                       true
% 1.33/0.99  --res_lit_sel                           adaptive
% 1.33/0.99  --res_lit_sel_side                      none
% 1.33/0.99  --res_ordering                          kbo
% 1.33/0.99  --res_to_prop_solver                    active
% 1.33/0.99  --res_prop_simpl_new                    false
% 1.33/0.99  --res_prop_simpl_given                  true
% 1.33/0.99  --res_passive_queue_type                priority_queues
% 1.33/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.33/0.99  --res_passive_queues_freq               [15;5]
% 1.33/0.99  --res_forward_subs                      full
% 1.33/0.99  --res_backward_subs                     full
% 1.33/0.99  --res_forward_subs_resolution           true
% 1.33/0.99  --res_backward_subs_resolution          true
% 1.33/0.99  --res_orphan_elimination                true
% 1.33/0.99  --res_time_limit                        2.
% 1.33/0.99  --res_out_proof                         true
% 1.33/0.99  
% 1.33/0.99  ------ Superposition Options
% 1.33/0.99  
% 1.33/0.99  --superposition_flag                    true
% 1.33/0.99  --sup_passive_queue_type                priority_queues
% 1.33/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.33/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.33/0.99  --demod_completeness_check              fast
% 1.33/0.99  --demod_use_ground                      true
% 1.33/0.99  --sup_to_prop_solver                    passive
% 1.33/0.99  --sup_prop_simpl_new                    true
% 1.33/0.99  --sup_prop_simpl_given                  true
% 1.33/0.99  --sup_fun_splitting                     false
% 1.33/0.99  --sup_smt_interval                      50000
% 1.33/0.99  
% 1.33/0.99  ------ Superposition Simplification Setup
% 1.33/0.99  
% 1.33/0.99  --sup_indices_passive                   []
% 1.33/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.33/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.33/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.33/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.33/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.33/0.99  --sup_full_bw                           [BwDemod]
% 1.33/0.99  --sup_immed_triv                        [TrivRules]
% 1.33/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.33/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.33/0.99  --sup_immed_bw_main                     []
% 1.33/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.33/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.33/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.33/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.33/0.99  
% 1.33/0.99  ------ Combination Options
% 1.33/0.99  
% 1.33/0.99  --comb_res_mult                         3
% 1.33/0.99  --comb_sup_mult                         2
% 1.33/0.99  --comb_inst_mult                        10
% 1.33/0.99  
% 1.33/0.99  ------ Debug Options
% 1.33/0.99  
% 1.33/0.99  --dbg_backtrace                         false
% 1.33/0.99  --dbg_dump_prop_clauses                 false
% 1.33/0.99  --dbg_dump_prop_clauses_file            -
% 1.33/0.99  --dbg_out_stat                          false
% 1.33/0.99  ------ Parsing...
% 1.33/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.33/0.99  
% 1.33/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.33/0.99  
% 1.33/0.99  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.33/0.99  
% 1.33/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.33/0.99  ------ Proving...
% 1.33/0.99  ------ Problem Properties 
% 1.33/0.99  
% 1.33/0.99  
% 1.33/0.99  clauses                                 18
% 1.33/0.99  conjectures                             3
% 1.33/0.99  EPR                                     2
% 1.33/0.99  Horn                                    9
% 1.33/0.99  unary                                   3
% 1.33/0.99  binary                                  1
% 1.33/0.99  lits                                    62
% 1.33/0.99  lits eq                                 5
% 1.33/0.99  fd_pure                                 0
% 1.33/0.99  fd_pseudo                               0
% 1.33/0.99  fd_cond                                 0
% 1.33/0.99  fd_pseudo_cond                          1
% 1.33/0.99  AC symbols                              0
% 1.33/0.99  
% 1.33/0.99  ------ Schedule dynamic 5 is on 
% 1.33/0.99  
% 1.33/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.33/0.99  
% 1.33/0.99  
% 1.33/0.99  ------ 
% 1.33/0.99  Current options:
% 1.33/0.99  ------ 
% 1.33/0.99  
% 1.33/0.99  ------ Input Options
% 1.33/0.99  
% 1.33/0.99  --out_options                           all
% 1.33/0.99  --tptp_safe_out                         true
% 1.33/0.99  --problem_path                          ""
% 1.33/0.99  --include_path                          ""
% 1.33/0.99  --clausifier                            res/vclausify_rel
% 1.33/0.99  --clausifier_options                    --mode clausify
% 1.33/0.99  --stdin                                 false
% 1.33/0.99  --stats_out                             all
% 1.33/0.99  
% 1.33/0.99  ------ General Options
% 1.33/0.99  
% 1.33/0.99  --fof                                   false
% 1.33/0.99  --time_out_real                         305.
% 1.33/0.99  --time_out_virtual                      -1.
% 1.33/0.99  --symbol_type_check                     false
% 1.33/0.99  --clausify_out                          false
% 1.33/0.99  --sig_cnt_out                           false
% 1.33/0.99  --trig_cnt_out                          false
% 1.33/0.99  --trig_cnt_out_tolerance                1.
% 1.33/0.99  --trig_cnt_out_sk_spl                   false
% 1.33/0.99  --abstr_cl_out                          false
% 1.33/0.99  
% 1.33/0.99  ------ Global Options
% 1.33/0.99  
% 1.33/0.99  --schedule                              default
% 1.33/0.99  --add_important_lit                     false
% 1.33/0.99  --prop_solver_per_cl                    1000
% 1.33/0.99  --min_unsat_core                        false
% 1.33/0.99  --soft_assumptions                      false
% 1.33/0.99  --soft_lemma_size                       3
% 1.33/0.99  --prop_impl_unit_size                   0
% 1.33/0.99  --prop_impl_unit                        []
% 1.33/0.99  --share_sel_clauses                     true
% 1.33/0.99  --reset_solvers                         false
% 1.33/0.99  --bc_imp_inh                            [conj_cone]
% 1.33/0.99  --conj_cone_tolerance                   3.
% 1.33/0.99  --extra_neg_conj                        none
% 1.33/0.99  --large_theory_mode                     true
% 1.33/0.99  --prolific_symb_bound                   200
% 1.33/0.99  --lt_threshold                          2000
% 1.33/0.99  --clause_weak_htbl                      true
% 1.33/0.99  --gc_record_bc_elim                     false
% 1.33/0.99  
% 1.33/0.99  ------ Preprocessing Options
% 1.33/0.99  
% 1.33/0.99  --preprocessing_flag                    true
% 1.33/0.99  --time_out_prep_mult                    0.1
% 1.33/0.99  --splitting_mode                        input
% 1.33/0.99  --splitting_grd                         true
% 1.33/0.99  --splitting_cvd                         false
% 1.33/0.99  --splitting_cvd_svl                     false
% 1.33/0.99  --splitting_nvd                         32
% 1.33/0.99  --sub_typing                            true
% 1.33/0.99  --prep_gs_sim                           true
% 1.33/0.99  --prep_unflatten                        true
% 1.33/0.99  --prep_res_sim                          true
% 1.33/0.99  --prep_upred                            true
% 1.33/0.99  --prep_sem_filter                       exhaustive
% 1.33/0.99  --prep_sem_filter_out                   false
% 1.33/0.99  --pred_elim                             true
% 1.33/0.99  --res_sim_input                         true
% 1.33/0.99  --eq_ax_congr_red                       true
% 1.33/0.99  --pure_diseq_elim                       true
% 1.33/0.99  --brand_transform                       false
% 1.33/0.99  --non_eq_to_eq                          false
% 1.33/0.99  --prep_def_merge                        true
% 1.33/0.99  --prep_def_merge_prop_impl              false
% 1.33/0.99  --prep_def_merge_mbd                    true
% 1.33/0.99  --prep_def_merge_tr_red                 false
% 1.33/0.99  --prep_def_merge_tr_cl                  false
% 1.33/0.99  --smt_preprocessing                     true
% 1.33/0.99  --smt_ac_axioms                         fast
% 1.33/0.99  --preprocessed_out                      false
% 1.33/0.99  --preprocessed_stats                    false
% 1.33/0.99  
% 1.33/0.99  ------ Abstraction refinement Options
% 1.33/0.99  
% 1.33/0.99  --abstr_ref                             []
% 1.33/0.99  --abstr_ref_prep                        false
% 1.33/0.99  --abstr_ref_until_sat                   false
% 1.33/0.99  --abstr_ref_sig_restrict                funpre
% 1.33/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.33/0.99  --abstr_ref_under                       []
% 1.33/0.99  
% 1.33/0.99  ------ SAT Options
% 1.33/0.99  
% 1.33/0.99  --sat_mode                              false
% 1.33/0.99  --sat_fm_restart_options                ""
% 1.33/0.99  --sat_gr_def                            false
% 1.33/0.99  --sat_epr_types                         true
% 1.33/0.99  --sat_non_cyclic_types                  false
% 1.33/0.99  --sat_finite_models                     false
% 1.33/0.99  --sat_fm_lemmas                         false
% 1.33/0.99  --sat_fm_prep                           false
% 1.33/0.99  --sat_fm_uc_incr                        true
% 1.33/0.99  --sat_out_model                         small
% 1.33/0.99  --sat_out_clauses                       false
% 1.33/0.99  
% 1.33/0.99  ------ QBF Options
% 1.33/0.99  
% 1.33/0.99  --qbf_mode                              false
% 1.33/0.99  --qbf_elim_univ                         false
% 1.33/0.99  --qbf_dom_inst                          none
% 1.33/0.99  --qbf_dom_pre_inst                      false
% 1.33/0.99  --qbf_sk_in                             false
% 1.33/0.99  --qbf_pred_elim                         true
% 1.33/0.99  --qbf_split                             512
% 1.33/0.99  
% 1.33/0.99  ------ BMC1 Options
% 1.33/0.99  
% 1.33/0.99  --bmc1_incremental                      false
% 1.33/0.99  --bmc1_axioms                           reachable_all
% 1.33/0.99  --bmc1_min_bound                        0
% 1.33/0.99  --bmc1_max_bound                        -1
% 1.33/0.99  --bmc1_max_bound_default                -1
% 1.33/0.99  --bmc1_symbol_reachability              true
% 1.33/0.99  --bmc1_property_lemmas                  false
% 1.33/0.99  --bmc1_k_induction                      false
% 1.33/0.99  --bmc1_non_equiv_states                 false
% 1.33/0.99  --bmc1_deadlock                         false
% 1.33/0.99  --bmc1_ucm                              false
% 1.33/0.99  --bmc1_add_unsat_core                   none
% 1.33/0.99  --bmc1_unsat_core_children              false
% 1.33/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.33/0.99  --bmc1_out_stat                         full
% 1.33/0.99  --bmc1_ground_init                      false
% 1.33/0.99  --bmc1_pre_inst_next_state              false
% 1.33/0.99  --bmc1_pre_inst_state                   false
% 1.33/0.99  --bmc1_pre_inst_reach_state             false
% 1.33/0.99  --bmc1_out_unsat_core                   false
% 1.33/0.99  --bmc1_aig_witness_out                  false
% 1.33/0.99  --bmc1_verbose                          false
% 1.33/0.99  --bmc1_dump_clauses_tptp                false
% 1.33/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.33/0.99  --bmc1_dump_file                        -
% 1.33/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.33/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.33/0.99  --bmc1_ucm_extend_mode                  1
% 1.33/0.99  --bmc1_ucm_init_mode                    2
% 1.33/0.99  --bmc1_ucm_cone_mode                    none
% 1.33/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.33/0.99  --bmc1_ucm_relax_model                  4
% 1.33/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.33/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.33/0.99  --bmc1_ucm_layered_model                none
% 1.33/0.99  --bmc1_ucm_max_lemma_size               10
% 1.33/0.99  
% 1.33/0.99  ------ AIG Options
% 1.33/0.99  
% 1.33/0.99  --aig_mode                              false
% 1.33/0.99  
% 1.33/0.99  ------ Instantiation Options
% 1.33/0.99  
% 1.33/0.99  --instantiation_flag                    true
% 1.33/0.99  --inst_sos_flag                         false
% 1.33/0.99  --inst_sos_phase                        true
% 1.33/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.33/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.33/0.99  --inst_lit_sel_side                     none
% 1.33/0.99  --inst_solver_per_active                1400
% 1.33/0.99  --inst_solver_calls_frac                1.
% 1.33/0.99  --inst_passive_queue_type               priority_queues
% 1.33/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.33/0.99  --inst_passive_queues_freq              [25;2]
% 1.33/0.99  --inst_dismatching                      true
% 1.33/0.99  --inst_eager_unprocessed_to_passive     true
% 1.33/0.99  --inst_prop_sim_given                   true
% 1.33/0.99  --inst_prop_sim_new                     false
% 1.33/0.99  --inst_subs_new                         false
% 1.33/0.99  --inst_eq_res_simp                      false
% 1.33/0.99  --inst_subs_given                       false
% 1.33/0.99  --inst_orphan_elimination               true
% 1.33/0.99  --inst_learning_loop_flag               true
% 1.33/0.99  --inst_learning_start                   3000
% 1.33/0.99  --inst_learning_factor                  2
% 1.33/0.99  --inst_start_prop_sim_after_learn       3
% 1.33/0.99  --inst_sel_renew                        solver
% 1.33/0.99  --inst_lit_activity_flag                true
% 1.33/0.99  --inst_restr_to_given                   false
% 1.33/0.99  --inst_activity_threshold               500
% 1.33/0.99  --inst_out_proof                        true
% 1.33/0.99  
% 1.33/0.99  ------ Resolution Options
% 1.33/0.99  
% 1.33/0.99  --resolution_flag                       false
% 1.33/0.99  --res_lit_sel                           adaptive
% 1.33/0.99  --res_lit_sel_side                      none
% 1.33/0.99  --res_ordering                          kbo
% 1.33/0.99  --res_to_prop_solver                    active
% 1.33/0.99  --res_prop_simpl_new                    false
% 1.33/0.99  --res_prop_simpl_given                  true
% 1.33/0.99  --res_passive_queue_type                priority_queues
% 1.33/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.33/0.99  --res_passive_queues_freq               [15;5]
% 1.33/0.99  --res_forward_subs                      full
% 1.33/0.99  --res_backward_subs                     full
% 1.33/0.99  --res_forward_subs_resolution           true
% 1.33/0.99  --res_backward_subs_resolution          true
% 1.33/0.99  --res_orphan_elimination                true
% 1.33/0.99  --res_time_limit                        2.
% 1.33/0.99  --res_out_proof                         true
% 1.33/0.99  
% 1.33/0.99  ------ Superposition Options
% 1.33/0.99  
% 1.33/0.99  --superposition_flag                    true
% 1.33/0.99  --sup_passive_queue_type                priority_queues
% 1.33/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.33/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.33/0.99  --demod_completeness_check              fast
% 1.33/0.99  --demod_use_ground                      true
% 1.33/0.99  --sup_to_prop_solver                    passive
% 1.33/0.99  --sup_prop_simpl_new                    true
% 1.33/0.99  --sup_prop_simpl_given                  true
% 1.33/0.99  --sup_fun_splitting                     false
% 1.33/0.99  --sup_smt_interval                      50000
% 1.33/0.99  
% 1.33/0.99  ------ Superposition Simplification Setup
% 1.33/0.99  
% 1.33/0.99  --sup_indices_passive                   []
% 1.33/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.33/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.33/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.33/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.33/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.33/0.99  --sup_full_bw                           [BwDemod]
% 1.33/0.99  --sup_immed_triv                        [TrivRules]
% 1.33/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.33/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.33/0.99  --sup_immed_bw_main                     []
% 1.33/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.33/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.33/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.33/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.33/0.99  
% 1.33/0.99  ------ Combination Options
% 1.33/0.99  
% 1.33/0.99  --comb_res_mult                         3
% 1.33/0.99  --comb_sup_mult                         2
% 1.33/0.99  --comb_inst_mult                        10
% 1.33/0.99  
% 1.33/0.99  ------ Debug Options
% 1.33/0.99  
% 1.33/0.99  --dbg_backtrace                         false
% 1.33/0.99  --dbg_dump_prop_clauses                 false
% 1.33/0.99  --dbg_dump_prop_clauses_file            -
% 1.33/0.99  --dbg_out_stat                          false
% 1.33/0.99  
% 1.33/0.99  
% 1.33/0.99  
% 1.33/0.99  
% 1.33/0.99  ------ Proving...
% 1.33/0.99  
% 1.33/0.99  
% 1.33/0.99  % SZS status Theorem for theBenchmark.p
% 1.33/0.99  
% 1.33/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.33/0.99  
% 1.33/0.99  fof(f1,axiom,(
% 1.33/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.33/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/0.99  
% 1.33/0.99  fof(f17,plain,(
% 1.33/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.33/0.99    inference(ennf_transformation,[],[f1])).
% 1.33/0.99  
% 1.33/0.99  fof(f45,plain,(
% 1.33/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.33/0.99    inference(cnf_transformation,[],[f17])).
% 1.33/0.99  
% 1.33/0.99  fof(f3,axiom,(
% 1.33/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.33/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/0.99  
% 1.33/0.99  fof(f19,plain,(
% 1.33/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.33/0.99    inference(ennf_transformation,[],[f3])).
% 1.33/0.99  
% 1.33/0.99  fof(f20,plain,(
% 1.33/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.33/0.99    inference(flattening,[],[f19])).
% 1.33/0.99  
% 1.33/0.99  fof(f47,plain,(
% 1.33/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.33/0.99    inference(cnf_transformation,[],[f20])).
% 1.33/0.99  
% 1.33/0.99  fof(f6,axiom,(
% 1.33/0.99    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~v1_xboole_0(X1) => (~v1_subset_1(X1,u1_struct_0(X0)) & ~v1_xboole_0(X1)))))),
% 1.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/1.00  
% 1.33/1.00  fof(f24,plain,(
% 1.33/1.00    ! [X0] : (! [X1] : (((~v1_subset_1(X1,u1_struct_0(X0)) & ~v1_xboole_0(X1)) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_struct_0(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)))),
% 1.33/1.00    inference(ennf_transformation,[],[f6])).
% 1.33/1.00  
% 1.33/1.00  fof(f25,plain,(
% 1.33/1.00    ! [X0] : (! [X1] : ((~v1_subset_1(X1,u1_struct_0(X0)) & ~v1_xboole_0(X1)) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))),
% 1.33/1.00    inference(flattening,[],[f24])).
% 1.33/1.00  
% 1.33/1.00  fof(f52,plain,(
% 1.33/1.00    ( ! [X0,X1] : (~v1_subset_1(X1,u1_struct_0(X0)) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)) )),
% 1.33/1.00    inference(cnf_transformation,[],[f25])).
% 1.33/1.00  
% 1.33/1.00  fof(f7,axiom,(
% 1.33/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/1.00  
% 1.33/1.00  fof(f26,plain,(
% 1.33/1.00    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.33/1.00    inference(ennf_transformation,[],[f7])).
% 1.33/1.00  
% 1.33/1.00  fof(f39,plain,(
% 1.33/1.00    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.33/1.00    inference(nnf_transformation,[],[f26])).
% 1.33/1.00  
% 1.33/1.00  fof(f54,plain,(
% 1.33/1.00    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.33/1.00    inference(cnf_transformation,[],[f39])).
% 1.33/1.00  
% 1.33/1.00  fof(f8,axiom,(
% 1.33/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/1.00  
% 1.33/1.00  fof(f15,plain,(
% 1.33/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.33/1.00    inference(pure_predicate_removal,[],[f8])).
% 1.33/1.00  
% 1.33/1.00  fof(f27,plain,(
% 1.33/1.00    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.33/1.00    inference(ennf_transformation,[],[f15])).
% 1.33/1.00  
% 1.33/1.00  fof(f28,plain,(
% 1.33/1.00    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.33/1.00    inference(flattening,[],[f27])).
% 1.33/1.00  
% 1.33/1.00  fof(f56,plain,(
% 1.33/1.00    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.33/1.00    inference(cnf_transformation,[],[f28])).
% 1.33/1.00  
% 1.33/1.00  fof(f5,axiom,(
% 1.33/1.00    ! [X0] : ((l1_pre_topc(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) => (~v7_struct_0(X1) & ~v2_struct_0(X1)))))),
% 1.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/1.00  
% 1.33/1.00  fof(f22,plain,(
% 1.33/1.00    ! [X0] : (! [X1] : (((~v7_struct_0(X1) & ~v2_struct_0(X1)) | (v1_tex_2(X1,X0) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v7_struct_0(X0) | v2_struct_0(X0)))),
% 1.33/1.00    inference(ennf_transformation,[],[f5])).
% 1.33/1.00  
% 1.33/1.00  fof(f23,plain,(
% 1.33/1.00    ! [X0] : (! [X1] : ((~v7_struct_0(X1) & ~v2_struct_0(X1)) | v1_tex_2(X1,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v7_struct_0(X0) | v2_struct_0(X0))),
% 1.33/1.00    inference(flattening,[],[f22])).
% 1.33/1.00  
% 1.33/1.00  fof(f50,plain,(
% 1.33/1.00    ( ! [X0,X1] : (~v7_struct_0(X1) | v1_tex_2(X1,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v7_struct_0(X0) | v2_struct_0(X0)) )),
% 1.33/1.00    inference(cnf_transformation,[],[f23])).
% 1.33/1.00  
% 1.33/1.00  fof(f13,conjecture,(
% 1.33/1.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 1.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/1.00  
% 1.33/1.00  fof(f14,negated_conjecture,(
% 1.33/1.00    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 1.33/1.00    inference(negated_conjecture,[],[f13])).
% 1.33/1.00  
% 1.33/1.00  fof(f37,plain,(
% 1.33/1.00    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.33/1.00    inference(ennf_transformation,[],[f14])).
% 1.33/1.00  
% 1.33/1.00  fof(f38,plain,(
% 1.33/1.00    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.33/1.00    inference(flattening,[],[f37])).
% 1.33/1.00  
% 1.33/1.00  fof(f40,plain,(
% 1.33/1.00    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.33/1.00    inference(nnf_transformation,[],[f38])).
% 1.33/1.00  
% 1.33/1.00  fof(f41,plain,(
% 1.33/1.00    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.33/1.00    inference(flattening,[],[f40])).
% 1.33/1.00  
% 1.33/1.00  fof(f43,plain,(
% 1.33/1.00    ( ! [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),sK1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,sK1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),sK1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,sK1),X0)) & m1_subset_1(sK1,u1_struct_0(X0)))) )),
% 1.33/1.00    introduced(choice_axiom,[])).
% 1.33/1.00  
% 1.33/1.00  fof(f42,plain,(
% 1.33/1.00    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,X1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,X1),sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.33/1.00    introduced(choice_axiom,[])).
% 1.33/1.00  
% 1.33/1.00  fof(f44,plain,(
% 1.33/1.00    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.33/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).
% 1.33/1.00  
% 1.33/1.00  fof(f66,plain,(
% 1.33/1.00    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 1.33/1.00    inference(cnf_transformation,[],[f44])).
% 1.33/1.00  
% 1.33/1.00  fof(f62,plain,(
% 1.33/1.00    ~v2_struct_0(sK0)),
% 1.33/1.00    inference(cnf_transformation,[],[f44])).
% 1.33/1.00  
% 1.33/1.00  fof(f63,plain,(
% 1.33/1.00    l1_pre_topc(sK0)),
% 1.33/1.00    inference(cnf_transformation,[],[f44])).
% 1.33/1.00  
% 1.33/1.00  fof(f64,plain,(
% 1.33/1.00    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.33/1.00    inference(cnf_transformation,[],[f44])).
% 1.33/1.00  
% 1.33/1.00  fof(f9,axiom,(
% 1.33/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/1.00  
% 1.33/1.00  fof(f16,plain,(
% 1.33/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.33/1.00    inference(pure_predicate_removal,[],[f9])).
% 1.33/1.00  
% 1.33/1.00  fof(f29,plain,(
% 1.33/1.00    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.33/1.00    inference(ennf_transformation,[],[f16])).
% 1.33/1.00  
% 1.33/1.00  fof(f30,plain,(
% 1.33/1.00    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.33/1.00    inference(flattening,[],[f29])).
% 1.33/1.00  
% 1.33/1.00  fof(f57,plain,(
% 1.33/1.00    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.33/1.00    inference(cnf_transformation,[],[f30])).
% 1.33/1.00  
% 1.33/1.00  fof(f58,plain,(
% 1.33/1.00    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.33/1.00    inference(cnf_transformation,[],[f30])).
% 1.33/1.00  
% 1.33/1.00  fof(f12,axiom,(
% 1.33/1.00    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))))),
% 1.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/1.00  
% 1.33/1.00  fof(f35,plain,(
% 1.33/1.00    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v7_struct_0(X0) | v2_struct_0(X0)))),
% 1.33/1.00    inference(ennf_transformation,[],[f12])).
% 1.33/1.00  
% 1.33/1.00  fof(f36,plain,(
% 1.33/1.00    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v7_struct_0(X0) | v2_struct_0(X0))),
% 1.33/1.00    inference(flattening,[],[f35])).
% 1.33/1.00  
% 1.33/1.00  fof(f61,plain,(
% 1.33/1.00    ( ! [X0,X1] : (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0) | v2_struct_0(X0)) )),
% 1.33/1.00    inference(cnf_transformation,[],[f36])).
% 1.33/1.00  
% 1.33/1.00  fof(f10,axiom,(
% 1.33/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ~(v1_tex_2(X1,X0) & u1_struct_0(X0) = u1_struct_0(X1))))),
% 1.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/1.00  
% 1.33/1.00  fof(f31,plain,(
% 1.33/1.00    ! [X0] : (! [X1] : ((~v1_tex_2(X1,X0) | u1_struct_0(X0) != u1_struct_0(X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.33/1.00    inference(ennf_transformation,[],[f10])).
% 1.33/1.00  
% 1.33/1.00  fof(f32,plain,(
% 1.33/1.00    ! [X0] : (! [X1] : (~v1_tex_2(X1,X0) | u1_struct_0(X0) != u1_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.33/1.00    inference(flattening,[],[f31])).
% 1.33/1.00  
% 1.33/1.00  fof(f59,plain,(
% 1.33/1.00    ( ! [X0,X1] : (~v1_tex_2(X1,X0) | u1_struct_0(X0) != u1_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.33/1.00    inference(cnf_transformation,[],[f32])).
% 1.33/1.00  
% 1.33/1.00  fof(f65,plain,(
% 1.33/1.00    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 1.33/1.00    inference(cnf_transformation,[],[f44])).
% 1.33/1.00  
% 1.33/1.00  fof(f11,axiom,(
% 1.33/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 1.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/1.00  
% 1.33/1.00  fof(f33,plain,(
% 1.33/1.00    ! [X0] : (! [X1] : ((~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.33/1.00    inference(ennf_transformation,[],[f11])).
% 1.33/1.00  
% 1.33/1.00  fof(f34,plain,(
% 1.33/1.00    ! [X0] : (! [X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.33/1.00    inference(flattening,[],[f33])).
% 1.33/1.00  
% 1.33/1.00  fof(f60,plain,(
% 1.33/1.00    ( ! [X0,X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.33/1.00    inference(cnf_transformation,[],[f34])).
% 1.33/1.00  
% 1.33/1.00  fof(f2,axiom,(
% 1.33/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/1.00  
% 1.33/1.00  fof(f18,plain,(
% 1.33/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.33/1.00    inference(ennf_transformation,[],[f2])).
% 1.33/1.00  
% 1.33/1.00  fof(f46,plain,(
% 1.33/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.33/1.00    inference(cnf_transformation,[],[f18])).
% 1.33/1.00  
% 1.33/1.00  fof(f4,axiom,(
% 1.33/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.33/1.00  
% 1.33/1.00  fof(f21,plain,(
% 1.33/1.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.33/1.00    inference(ennf_transformation,[],[f4])).
% 1.33/1.00  
% 1.33/1.00  fof(f48,plain,(
% 1.33/1.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.33/1.00    inference(cnf_transformation,[],[f21])).
% 1.33/1.00  
% 1.33/1.00  cnf(c_0,plain,
% 1.33/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.33/1.00      inference(cnf_transformation,[],[f45]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_2,plain,
% 1.33/1.00      ( v2_struct_0(X0)
% 1.33/1.00      | ~ v1_xboole_0(u1_struct_0(X0))
% 1.33/1.00      | ~ l1_struct_0(X0) ),
% 1.33/1.00      inference(cnf_transformation,[],[f47]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_347,plain,
% 1.33/1.00      ( v2_struct_0(X0)
% 1.33/1.00      | ~ v1_xboole_0(u1_struct_0(X0))
% 1.33/1.00      | ~ l1_pre_topc(X0) ),
% 1.33/1.00      inference(resolution,[status(thm)],[c_0,c_2]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1502,plain,
% 1.33/1.00      ( v2_struct_0(X0_44)
% 1.33/1.00      | ~ v1_xboole_0(u1_struct_0(X0_44))
% 1.33/1.00      | ~ l1_pre_topc(X0_44) ),
% 1.33/1.00      inference(subtyping,[status(esa)],[c_347]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_2179,plain,
% 1.33/1.00      ( v2_struct_0(k1_tex_2(sK0,sK1))
% 1.33/1.00      | ~ v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
% 1.33/1.00      | ~ l1_pre_topc(k1_tex_2(sK0,sK1)) ),
% 1.33/1.00      inference(instantiation,[status(thm)],[c_1502]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_6,plain,
% 1.33/1.00      ( ~ v1_subset_1(X0,u1_struct_0(X1))
% 1.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.33/1.00      | ~ v7_struct_0(X1)
% 1.33/1.00      | v2_struct_0(X1)
% 1.33/1.00      | v1_xboole_0(X0)
% 1.33/1.00      | ~ l1_struct_0(X1) ),
% 1.33/1.00      inference(cnf_transformation,[],[f52]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_361,plain,
% 1.33/1.00      ( ~ v1_subset_1(X0,u1_struct_0(X1))
% 1.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.33/1.00      | ~ v7_struct_0(X1)
% 1.33/1.00      | v2_struct_0(X1)
% 1.33/1.00      | v1_xboole_0(X0)
% 1.33/1.00      | ~ l1_pre_topc(X2)
% 1.33/1.00      | X1 != X2 ),
% 1.33/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_6]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_362,plain,
% 1.33/1.00      ( ~ v1_subset_1(X0,u1_struct_0(X1))
% 1.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.33/1.00      | ~ v7_struct_0(X1)
% 1.33/1.00      | v2_struct_0(X1)
% 1.33/1.00      | v1_xboole_0(X0)
% 1.33/1.00      | ~ l1_pre_topc(X1) ),
% 1.33/1.00      inference(unflattening,[status(thm)],[c_361]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1501,plain,
% 1.33/1.00      ( ~ v1_subset_1(X0_43,u1_struct_0(X0_44))
% 1.33/1.00      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(X0_44)))
% 1.33/1.00      | ~ v7_struct_0(X0_44)
% 1.33/1.00      | v2_struct_0(X0_44)
% 1.33/1.00      | v1_xboole_0(X0_43)
% 1.33/1.00      | ~ l1_pre_topc(X0_44) ),
% 1.33/1.00      inference(subtyping,[status(esa)],[c_362]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_2104,plain,
% 1.33/1.00      ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
% 1.33/1.00      | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.33/1.00      | ~ v7_struct_0(sK0)
% 1.33/1.00      | v2_struct_0(sK0)
% 1.33/1.00      | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
% 1.33/1.00      | ~ l1_pre_topc(sK0) ),
% 1.33/1.00      inference(instantiation,[status(thm)],[c_1501]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_8,plain,
% 1.33/1.00      ( v1_subset_1(X0,X1)
% 1.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.33/1.00      | X0 = X1 ),
% 1.33/1.00      inference(cnf_transformation,[],[f54]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1511,plain,
% 1.33/1.00      ( v1_subset_1(X0_43,X1_43)
% 1.33/1.00      | ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
% 1.33/1.00      | X0_43 = X1_43 ),
% 1.33/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_2058,plain,
% 1.33/1.00      ( v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
% 1.33/1.00      | ~ m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.33/1.00      | u1_struct_0(k1_tex_2(sK0,sK1)) = u1_struct_0(sK0) ),
% 1.33/1.00      inference(instantiation,[status(thm)],[c_1511]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_10,plain,
% 1.33/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.33/1.00      | m1_pre_topc(k1_tex_2(X1,X0),X1)
% 1.33/1.00      | v2_struct_0(X1)
% 1.33/1.00      | ~ l1_pre_topc(X1) ),
% 1.33/1.00      inference(cnf_transformation,[],[f56]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_4,plain,
% 1.33/1.00      ( v1_tex_2(X0,X1)
% 1.33/1.00      | ~ m1_pre_topc(X0,X1)
% 1.33/1.00      | ~ v7_struct_0(X0)
% 1.33/1.00      | v7_struct_0(X1)
% 1.33/1.00      | v2_struct_0(X1)
% 1.33/1.00      | v2_struct_0(X0)
% 1.33/1.00      | ~ l1_pre_topc(X1) ),
% 1.33/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_17,negated_conjecture,
% 1.33/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
% 1.33/1.00      | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
% 1.33/1.00      inference(cnf_transformation,[],[f66]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_155,plain,
% 1.33/1.00      ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
% 1.33/1.00      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
% 1.33/1.00      inference(prop_impl,[status(thm)],[c_17]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_156,plain,
% 1.33/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
% 1.33/1.00      | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
% 1.33/1.00      inference(renaming,[status(thm)],[c_155]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_467,plain,
% 1.33/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
% 1.33/1.00      | ~ m1_pre_topc(X0,X1)
% 1.33/1.00      | ~ v7_struct_0(X0)
% 1.33/1.00      | v7_struct_0(X1)
% 1.33/1.00      | v2_struct_0(X0)
% 1.33/1.00      | v2_struct_0(X1)
% 1.33/1.00      | ~ l1_pre_topc(X1)
% 1.33/1.00      | k1_tex_2(sK0,sK1) != X0
% 1.33/1.00      | sK0 != X1 ),
% 1.33/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_156]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_468,plain,
% 1.33/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
% 1.33/1.00      | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
% 1.33/1.00      | ~ v7_struct_0(k1_tex_2(sK0,sK1))
% 1.33/1.00      | v7_struct_0(sK0)
% 1.33/1.00      | v2_struct_0(k1_tex_2(sK0,sK1))
% 1.33/1.00      | v2_struct_0(sK0)
% 1.33/1.00      | ~ l1_pre_topc(sK0) ),
% 1.33/1.00      inference(unflattening,[status(thm)],[c_467]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_21,negated_conjecture,
% 1.33/1.00      ( ~ v2_struct_0(sK0) ),
% 1.33/1.00      inference(cnf_transformation,[],[f62]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_20,negated_conjecture,
% 1.33/1.00      ( l1_pre_topc(sK0) ),
% 1.33/1.00      inference(cnf_transformation,[],[f63]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_470,plain,
% 1.33/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
% 1.33/1.00      | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
% 1.33/1.00      | ~ v7_struct_0(k1_tex_2(sK0,sK1))
% 1.33/1.00      | v7_struct_0(sK0)
% 1.33/1.00      | v2_struct_0(k1_tex_2(sK0,sK1)) ),
% 1.33/1.00      inference(global_propositional_subsumption,
% 1.33/1.00                [status(thm)],
% 1.33/1.00                [c_468,c_21,c_20]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_612,plain,
% 1.33/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
% 1.33/1.00      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.33/1.00      | ~ v7_struct_0(k1_tex_2(sK0,sK1))
% 1.33/1.00      | v7_struct_0(sK0)
% 1.33/1.00      | v2_struct_0(X1)
% 1.33/1.00      | v2_struct_0(k1_tex_2(sK0,sK1))
% 1.33/1.00      | ~ l1_pre_topc(X1)
% 1.33/1.00      | k1_tex_2(X1,X0) != k1_tex_2(sK0,sK1)
% 1.33/1.00      | sK0 != X1 ),
% 1.33/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_470]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_613,plain,
% 1.33/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
% 1.33/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 1.33/1.00      | ~ v7_struct_0(k1_tex_2(sK0,sK1))
% 1.33/1.00      | v7_struct_0(sK0)
% 1.33/1.00      | v2_struct_0(k1_tex_2(sK0,sK1))
% 1.33/1.00      | v2_struct_0(sK0)
% 1.33/1.00      | ~ l1_pre_topc(sK0)
% 1.33/1.00      | k1_tex_2(sK0,X0) != k1_tex_2(sK0,sK1) ),
% 1.33/1.00      inference(unflattening,[status(thm)],[c_612]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_617,plain,
% 1.33/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
% 1.33/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 1.33/1.00      | ~ v7_struct_0(k1_tex_2(sK0,sK1))
% 1.33/1.00      | v7_struct_0(sK0)
% 1.33/1.00      | v2_struct_0(k1_tex_2(sK0,sK1))
% 1.33/1.00      | k1_tex_2(sK0,X0) != k1_tex_2(sK0,sK1) ),
% 1.33/1.00      inference(global_propositional_subsumption,
% 1.33/1.00                [status(thm)],
% 1.33/1.00                [c_613,c_21,c_20]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1496,plain,
% 1.33/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
% 1.33/1.00      | ~ m1_subset_1(X0_43,u1_struct_0(sK0))
% 1.33/1.00      | ~ v7_struct_0(k1_tex_2(sK0,sK1))
% 1.33/1.00      | v7_struct_0(sK0)
% 1.33/1.00      | v2_struct_0(k1_tex_2(sK0,sK1))
% 1.33/1.00      | k1_tex_2(sK0,X0_43) != k1_tex_2(sK0,sK1) ),
% 1.33/1.00      inference(subtyping,[status(esa)],[c_617]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1514,plain,
% 1.33/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
% 1.33/1.00      | ~ v7_struct_0(k1_tex_2(sK0,sK1))
% 1.33/1.00      | v7_struct_0(sK0)
% 1.33/1.00      | v2_struct_0(k1_tex_2(sK0,sK1))
% 1.33/1.00      | sP0_iProver_split ),
% 1.33/1.00      inference(splitting,
% 1.33/1.00                [splitting(split),new_symbols(definition,[])],
% 1.33/1.00                [c_1496]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_19,negated_conjecture,
% 1.33/1.00      ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
% 1.33/1.00      inference(cnf_transformation,[],[f64]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1528,plain,
% 1.33/1.00      ( X0_44 != X1_44
% 1.33/1.00      | k1_tex_2(X0_44,X0_43) = k1_tex_2(X1_44,X1_43)
% 1.33/1.00      | X0_43 != X1_43 ),
% 1.33/1.00      theory(equality) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1538,plain,
% 1.33/1.00      ( k1_tex_2(sK0,sK1) = k1_tex_2(sK0,sK1) | sK0 != sK0 | sK1 != sK1 ),
% 1.33/1.00      inference(instantiation,[status(thm)],[c_1528]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1516,plain,( X0_43 = X0_43 ),theory(equality) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1541,plain,
% 1.33/1.00      ( sK1 = sK1 ),
% 1.33/1.00      inference(instantiation,[status(thm)],[c_1516]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1517,plain,( X0_44 = X0_44 ),theory(equality) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1542,plain,
% 1.33/1.00      ( sK0 = sK0 ),
% 1.33/1.00      inference(instantiation,[status(thm)],[c_1517]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_13,plain,
% 1.33/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.33/1.00      | v2_struct_0(X1)
% 1.33/1.00      | ~ v2_struct_0(k1_tex_2(X1,X0))
% 1.33/1.00      | ~ l1_pre_topc(X1) ),
% 1.33/1.00      inference(cnf_transformation,[],[f57]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1509,plain,
% 1.33/1.00      ( ~ m1_subset_1(X0_43,u1_struct_0(X0_44))
% 1.33/1.00      | v2_struct_0(X0_44)
% 1.33/1.00      | ~ v2_struct_0(k1_tex_2(X0_44,X0_43))
% 1.33/1.00      | ~ l1_pre_topc(X0_44) ),
% 1.33/1.00      inference(subtyping,[status(esa)],[c_13]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1548,plain,
% 1.33/1.00      ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 1.33/1.00      | ~ v2_struct_0(k1_tex_2(sK0,sK1))
% 1.33/1.00      | v2_struct_0(sK0)
% 1.33/1.00      | ~ l1_pre_topc(sK0) ),
% 1.33/1.00      inference(instantiation,[status(thm)],[c_1509]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_12,plain,
% 1.33/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.33/1.00      | v7_struct_0(k1_tex_2(X1,X0))
% 1.33/1.00      | v2_struct_0(X1)
% 1.33/1.00      | ~ l1_pre_topc(X1) ),
% 1.33/1.00      inference(cnf_transformation,[],[f58]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1508,plain,
% 1.33/1.00      ( ~ m1_subset_1(X0_43,u1_struct_0(X0_44))
% 1.33/1.00      | v7_struct_0(k1_tex_2(X0_44,X0_43))
% 1.33/1.00      | v2_struct_0(X0_44)
% 1.33/1.00      | ~ l1_pre_topc(X0_44) ),
% 1.33/1.00      inference(subtyping,[status(esa)],[c_12]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1551,plain,
% 1.33/1.00      ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 1.33/1.00      | v7_struct_0(k1_tex_2(sK0,sK1))
% 1.33/1.00      | v2_struct_0(sK0)
% 1.33/1.00      | ~ l1_pre_topc(sK0) ),
% 1.33/1.00      inference(instantiation,[status(thm)],[c_1508]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_16,plain,
% 1.33/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
% 1.33/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.33/1.00      | v7_struct_0(X0)
% 1.33/1.00      | v2_struct_0(X0)
% 1.33/1.00      | ~ l1_struct_0(X0) ),
% 1.33/1.00      inference(cnf_transformation,[],[f61]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_307,plain,
% 1.33/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
% 1.33/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.33/1.00      | v7_struct_0(X0)
% 1.33/1.00      | v2_struct_0(X0)
% 1.33/1.00      | ~ l1_pre_topc(X0) ),
% 1.33/1.00      inference(resolution,[status(thm)],[c_0,c_16]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1504,plain,
% 1.33/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(X0_44),X0_43),u1_struct_0(X0_44))
% 1.33/1.00      | ~ m1_subset_1(X0_43,u1_struct_0(X0_44))
% 1.33/1.00      | v7_struct_0(X0_44)
% 1.33/1.00      | v2_struct_0(X0_44)
% 1.33/1.00      | ~ l1_pre_topc(X0_44) ),
% 1.33/1.00      inference(subtyping,[status(esa)],[c_307]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1557,plain,
% 1.33/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
% 1.33/1.00      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 1.33/1.00      | v7_struct_0(sK0)
% 1.33/1.00      | v2_struct_0(sK0)
% 1.33/1.00      | ~ l1_pre_topc(sK0) ),
% 1.33/1.00      inference(instantiation,[status(thm)],[c_1504]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_14,plain,
% 1.33/1.00      ( ~ v1_tex_2(X0,X1)
% 1.33/1.00      | ~ m1_pre_topc(X0,X1)
% 1.33/1.00      | ~ l1_pre_topc(X1)
% 1.33/1.00      | u1_struct_0(X0) != u1_struct_0(X1) ),
% 1.33/1.00      inference(cnf_transformation,[],[f59]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_18,negated_conjecture,
% 1.33/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
% 1.33/1.00      | v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
% 1.33/1.00      inference(cnf_transformation,[],[f65]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_157,plain,
% 1.33/1.00      ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
% 1.33/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
% 1.33/1.00      inference(prop_impl,[status(thm)],[c_18]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_158,plain,
% 1.33/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
% 1.33/1.00      | v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
% 1.33/1.00      inference(renaming,[status(thm)],[c_157]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_490,plain,
% 1.33/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
% 1.33/1.00      | ~ m1_pre_topc(X0,X1)
% 1.33/1.00      | ~ l1_pre_topc(X1)
% 1.33/1.00      | k1_tex_2(sK0,sK1) != X0
% 1.33/1.00      | u1_struct_0(X1) != u1_struct_0(X0)
% 1.33/1.00      | sK0 != X1 ),
% 1.33/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_158]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_491,plain,
% 1.33/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
% 1.33/1.00      | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
% 1.33/1.00      | ~ l1_pre_topc(sK0)
% 1.33/1.00      | u1_struct_0(sK0) != u1_struct_0(k1_tex_2(sK0,sK1)) ),
% 1.33/1.00      inference(unflattening,[status(thm)],[c_490]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_493,plain,
% 1.33/1.00      ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
% 1.33/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
% 1.33/1.00      | u1_struct_0(sK0) != u1_struct_0(k1_tex_2(sK0,sK1)) ),
% 1.33/1.00      inference(global_propositional_subsumption,
% 1.33/1.00                [status(thm)],
% 1.33/1.00                [c_491,c_20]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_494,plain,
% 1.33/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
% 1.33/1.00      | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
% 1.33/1.00      | u1_struct_0(sK0) != u1_struct_0(k1_tex_2(sK0,sK1)) ),
% 1.33/1.00      inference(renaming,[status(thm)],[c_493]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_588,plain,
% 1.33/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
% 1.33/1.00      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.33/1.00      | v2_struct_0(X1)
% 1.33/1.00      | ~ l1_pre_topc(X1)
% 1.33/1.00      | k1_tex_2(X1,X0) != k1_tex_2(sK0,sK1)
% 1.33/1.00      | u1_struct_0(k1_tex_2(sK0,sK1)) != u1_struct_0(sK0)
% 1.33/1.00      | sK0 != X1 ),
% 1.33/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_494]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_589,plain,
% 1.33/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
% 1.33/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 1.33/1.00      | v2_struct_0(sK0)
% 1.33/1.00      | ~ l1_pre_topc(sK0)
% 1.33/1.00      | k1_tex_2(sK0,X0) != k1_tex_2(sK0,sK1)
% 1.33/1.00      | u1_struct_0(k1_tex_2(sK0,sK1)) != u1_struct_0(sK0) ),
% 1.33/1.00      inference(unflattening,[status(thm)],[c_588]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_593,plain,
% 1.33/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
% 1.33/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 1.33/1.00      | k1_tex_2(sK0,X0) != k1_tex_2(sK0,sK1)
% 1.33/1.00      | u1_struct_0(k1_tex_2(sK0,sK1)) != u1_struct_0(sK0) ),
% 1.33/1.00      inference(global_propositional_subsumption,
% 1.33/1.00                [status(thm)],
% 1.33/1.00                [c_589,c_21,c_20]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1497,plain,
% 1.33/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
% 1.33/1.00      | ~ m1_subset_1(X0_43,u1_struct_0(sK0))
% 1.33/1.00      | k1_tex_2(sK0,X0_43) != k1_tex_2(sK0,sK1)
% 1.33/1.00      | u1_struct_0(k1_tex_2(sK0,sK1)) != u1_struct_0(sK0) ),
% 1.33/1.00      inference(subtyping,[status(esa)],[c_593]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1512,plain,
% 1.33/1.00      ( ~ m1_subset_1(X0_43,u1_struct_0(sK0))
% 1.33/1.00      | k1_tex_2(sK0,X0_43) != k1_tex_2(sK0,sK1)
% 1.33/1.00      | ~ sP0_iProver_split ),
% 1.33/1.00      inference(splitting,
% 1.33/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.33/1.00                [c_1497]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1577,plain,
% 1.33/1.00      ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 1.33/1.00      | ~ sP0_iProver_split
% 1.33/1.00      | k1_tex_2(sK0,sK1) != k1_tex_2(sK0,sK1) ),
% 1.33/1.00      inference(instantiation,[status(thm)],[c_1512]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1634,plain,
% 1.33/1.00      ( v7_struct_0(sK0) ),
% 1.33/1.00      inference(global_propositional_subsumption,
% 1.33/1.00                [status(thm)],
% 1.33/1.00                [c_1514,c_21,c_20,c_19,c_1538,c_1541,c_1542,c_1548,
% 1.33/1.00                 c_1551,c_1557,c_1577]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1513,plain,
% 1.33/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
% 1.33/1.00      | sP0_iProver_split
% 1.33/1.00      | u1_struct_0(k1_tex_2(sK0,sK1)) != u1_struct_0(sK0) ),
% 1.33/1.00      inference(splitting,
% 1.33/1.00                [splitting(split),new_symbols(definition,[])],
% 1.33/1.00                [c_1497]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_15,plain,
% 1.33/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
% 1.33/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.33/1.00      | ~ v7_struct_0(X0)
% 1.33/1.00      | v2_struct_0(X0)
% 1.33/1.00      | ~ l1_struct_0(X0) ),
% 1.33/1.00      inference(cnf_transformation,[],[f60]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_327,plain,
% 1.33/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
% 1.33/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.33/1.00      | ~ v7_struct_0(X0)
% 1.33/1.00      | v2_struct_0(X0)
% 1.33/1.00      | ~ l1_pre_topc(X0) ),
% 1.33/1.00      inference(resolution,[status(thm)],[c_0,c_15]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1503,plain,
% 1.33/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0_44),X0_43),u1_struct_0(X0_44))
% 1.33/1.00      | ~ m1_subset_1(X0_43,u1_struct_0(X0_44))
% 1.33/1.00      | ~ v7_struct_0(X0_44)
% 1.33/1.00      | v2_struct_0(X0_44)
% 1.33/1.00      | ~ l1_pre_topc(X0_44) ),
% 1.33/1.00      inference(subtyping,[status(esa)],[c_327]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1560,plain,
% 1.33/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
% 1.33/1.00      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 1.33/1.00      | ~ v7_struct_0(sK0)
% 1.33/1.00      | v2_struct_0(sK0)
% 1.33/1.00      | ~ l1_pre_topc(sK0) ),
% 1.33/1.00      inference(instantiation,[status(thm)],[c_1503]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1626,plain,
% 1.33/1.00      ( u1_struct_0(k1_tex_2(sK0,sK1)) != u1_struct_0(sK0) ),
% 1.33/1.00      inference(global_propositional_subsumption,
% 1.33/1.00                [status(thm)],
% 1.33/1.00                [c_1513,c_21,c_20,c_19,c_1538,c_1541,c_1542,c_1548,
% 1.33/1.00                 c_1551,c_1557,c_1560,c_1577,c_1514]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1,plain,
% 1.33/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 1.33/1.00      inference(cnf_transformation,[],[f46]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_570,plain,
% 1.33/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.33/1.00      | v2_struct_0(X1)
% 1.33/1.00      | ~ l1_pre_topc(X2)
% 1.33/1.00      | ~ l1_pre_topc(X1)
% 1.33/1.00      | l1_pre_topc(X3)
% 1.33/1.00      | X1 != X2
% 1.33/1.00      | k1_tex_2(X1,X0) != X3 ),
% 1.33/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_10]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_571,plain,
% 1.33/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.33/1.00      | v2_struct_0(X1)
% 1.33/1.00      | ~ l1_pre_topc(X1)
% 1.33/1.00      | l1_pre_topc(k1_tex_2(X1,X0)) ),
% 1.33/1.00      inference(unflattening,[status(thm)],[c_570]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1498,plain,
% 1.33/1.00      ( ~ m1_subset_1(X0_43,u1_struct_0(X0_44))
% 1.33/1.00      | v2_struct_0(X0_44)
% 1.33/1.00      | ~ l1_pre_topc(X0_44)
% 1.33/1.00      | l1_pre_topc(k1_tex_2(X0_44,X0_43)) ),
% 1.33/1.00      inference(subtyping,[status(esa)],[c_571]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1573,plain,
% 1.33/1.00      ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 1.33/1.00      | v2_struct_0(sK0)
% 1.33/1.00      | l1_pre_topc(k1_tex_2(sK0,sK1))
% 1.33/1.00      | ~ l1_pre_topc(sK0) ),
% 1.33/1.00      inference(instantiation,[status(thm)],[c_1498]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_3,plain,
% 1.33/1.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.33/1.00      | ~ m1_pre_topc(X0,X1)
% 1.33/1.00      | ~ l1_pre_topc(X1) ),
% 1.33/1.00      inference(cnf_transformation,[],[f48]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_552,plain,
% 1.33/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.33/1.00      | m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X3)))
% 1.33/1.00      | v2_struct_0(X1)
% 1.33/1.00      | ~ l1_pre_topc(X3)
% 1.33/1.00      | ~ l1_pre_topc(X1)
% 1.33/1.00      | X1 != X3
% 1.33/1.00      | k1_tex_2(X1,X0) != X2 ),
% 1.33/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_10]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_553,plain,
% 1.33/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.33/1.00      | m1_subset_1(u1_struct_0(k1_tex_2(X1,X0)),k1_zfmisc_1(u1_struct_0(X1)))
% 1.33/1.00      | v2_struct_0(X1)
% 1.33/1.00      | ~ l1_pre_topc(X1) ),
% 1.33/1.00      inference(unflattening,[status(thm)],[c_552]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1499,plain,
% 1.33/1.00      ( ~ m1_subset_1(X0_43,u1_struct_0(X0_44))
% 1.33/1.00      | m1_subset_1(u1_struct_0(k1_tex_2(X0_44,X0_43)),k1_zfmisc_1(u1_struct_0(X0_44)))
% 1.33/1.00      | v2_struct_0(X0_44)
% 1.33/1.00      | ~ l1_pre_topc(X0_44) ),
% 1.33/1.00      inference(subtyping,[status(esa)],[c_553]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(c_1570,plain,
% 1.33/1.00      ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.33/1.00      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 1.33/1.00      | v2_struct_0(sK0)
% 1.33/1.00      | ~ l1_pre_topc(sK0) ),
% 1.33/1.00      inference(instantiation,[status(thm)],[c_1499]) ).
% 1.33/1.00  
% 1.33/1.00  cnf(contradiction,plain,
% 1.33/1.00      ( $false ),
% 1.33/1.00      inference(minisat,
% 1.33/1.00                [status(thm)],
% 1.33/1.00                [c_2179,c_2104,c_2058,c_1634,c_1626,c_1573,c_1570,c_1548,
% 1.33/1.00                 c_19,c_20,c_21]) ).
% 1.33/1.00  
% 1.33/1.00  
% 1.33/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.33/1.00  
% 1.33/1.00  ------                               Statistics
% 1.33/1.00  
% 1.33/1.00  ------ General
% 1.33/1.00  
% 1.33/1.00  abstr_ref_over_cycles:                  0
% 1.33/1.00  abstr_ref_under_cycles:                 0
% 1.33/1.00  gc_basic_clause_elim:                   0
% 1.33/1.00  forced_gc_time:                         0
% 1.33/1.00  parsing_time:                           0.011
% 1.33/1.00  unif_index_cands_time:                  0.
% 1.33/1.00  unif_index_add_time:                    0.
% 1.33/1.00  orderings_time:                         0.
% 1.33/1.00  out_proof_time:                         0.011
% 1.33/1.00  total_time:                             0.095
% 1.33/1.00  num_of_symbols:                         49
% 1.33/1.00  num_of_terms:                           1200
% 1.33/1.00  
% 1.33/1.00  ------ Preprocessing
% 1.33/1.00  
% 1.33/1.00  num_of_splits:                          2
% 1.33/1.00  num_of_split_atoms:                     1
% 1.33/1.00  num_of_reused_defs:                     1
% 1.33/1.00  num_eq_ax_congr_red:                    2
% 1.33/1.00  num_of_sem_filtered_clauses:            2
% 1.33/1.00  num_of_subtypes:                        2
% 1.33/1.00  monotx_restored_types:                  1
% 1.33/1.00  sat_num_of_epr_types:                   0
% 1.33/1.00  sat_num_of_non_cyclic_types:            0
% 1.33/1.00  sat_guarded_non_collapsed_types:        0
% 1.33/1.00  num_pure_diseq_elim:                    0
% 1.33/1.00  simp_replaced_by:                       0
% 1.33/1.00  res_preprocessed:                       97
% 1.33/1.00  prep_upred:                             0
% 1.33/1.00  prep_unflattend:                        40
% 1.33/1.00  smt_new_axioms:                         0
% 1.33/1.00  pred_elim_cands:                        6
% 1.33/1.00  pred_elim:                              3
% 1.33/1.00  pred_elim_cl:                           3
% 1.33/1.00  pred_elim_cycles:                       8
% 1.33/1.00  merged_defs:                            2
% 1.33/1.00  merged_defs_ncl:                        0
% 1.33/1.00  bin_hyper_res:                          2
% 1.33/1.00  prep_cycles:                            4
% 1.33/1.00  pred_elim_time:                         0.024
% 1.33/1.00  splitting_time:                         0.
% 1.33/1.00  sem_filter_time:                        0.
% 1.33/1.00  monotx_time:                            0.001
% 1.33/1.00  subtype_inf_time:                       0.001
% 1.33/1.00  
% 1.33/1.00  ------ Problem properties
% 1.33/1.00  
% 1.33/1.00  clauses:                                18
% 1.33/1.00  conjectures:                            3
% 1.33/1.00  epr:                                    2
% 1.33/1.00  horn:                                   9
% 1.33/1.00  ground:                                 5
% 1.33/1.00  unary:                                  3
% 1.33/1.00  binary:                                 1
% 1.33/1.00  lits:                                   62
% 1.33/1.00  lits_eq:                                5
% 1.33/1.00  fd_pure:                                0
% 1.33/1.00  fd_pseudo:                              0
% 1.33/1.00  fd_cond:                                0
% 1.33/1.00  fd_pseudo_cond:                         1
% 1.33/1.00  ac_symbols:                             0
% 1.33/1.00  
% 1.33/1.00  ------ Propositional Solver
% 1.33/1.00  
% 1.33/1.00  prop_solver_calls:                      23
% 1.33/1.00  prop_fast_solver_calls:                 911
% 1.33/1.00  smt_solver_calls:                       0
% 1.33/1.00  smt_fast_solver_calls:                  0
% 1.33/1.00  prop_num_of_clauses:                    318
% 1.33/1.00  prop_preprocess_simplified:             2704
% 1.33/1.00  prop_fo_subsumed:                       27
% 1.33/1.00  prop_solver_time:                       0.
% 1.33/1.00  smt_solver_time:                        0.
% 1.33/1.00  smt_fast_solver_time:                   0.
% 1.33/1.00  prop_fast_solver_time:                  0.
% 1.33/1.00  prop_unsat_core_time:                   0.
% 1.33/1.00  
% 1.33/1.00  ------ QBF
% 1.33/1.00  
% 1.33/1.00  qbf_q_res:                              0
% 1.33/1.00  qbf_num_tautologies:                    0
% 1.33/1.00  qbf_prep_cycles:                        0
% 1.33/1.00  
% 1.33/1.00  ------ BMC1
% 1.33/1.00  
% 1.33/1.00  bmc1_current_bound:                     -1
% 1.33/1.00  bmc1_last_solved_bound:                 -1
% 1.33/1.00  bmc1_unsat_core_size:                   -1
% 1.33/1.00  bmc1_unsat_core_parents_size:           -1
% 1.33/1.00  bmc1_merge_next_fun:                    0
% 1.33/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.33/1.00  
% 1.33/1.00  ------ Instantiation
% 1.33/1.00  
% 1.33/1.00  inst_num_of_clauses:                    58
% 1.33/1.00  inst_num_in_passive:                    12
% 1.33/1.00  inst_num_in_active:                     41
% 1.33/1.00  inst_num_in_unprocessed:                4
% 1.33/1.00  inst_num_of_loops:                      44
% 1.33/1.00  inst_num_of_learning_restarts:          0
% 1.33/1.00  inst_num_moves_active_passive:          0
% 1.33/1.00  inst_lit_activity:                      0
% 1.33/1.00  inst_lit_activity_moves:                0
% 1.33/1.00  inst_num_tautologies:                   0
% 1.33/1.00  inst_num_prop_implied:                  0
% 1.33/1.00  inst_num_existing_simplified:           0
% 1.33/1.00  inst_num_eq_res_simplified:             0
% 1.33/1.00  inst_num_child_elim:                    0
% 1.33/1.00  inst_num_of_dismatching_blockings:      0
% 1.33/1.00  inst_num_of_non_proper_insts:           22
% 1.33/1.00  inst_num_of_duplicates:                 0
% 1.33/1.00  inst_inst_num_from_inst_to_res:         0
% 1.33/1.00  inst_dismatching_checking_time:         0.
% 1.33/1.00  
% 1.33/1.00  ------ Resolution
% 1.33/1.00  
% 1.33/1.00  res_num_of_clauses:                     0
% 1.33/1.00  res_num_in_passive:                     0
% 1.33/1.00  res_num_in_active:                      0
% 1.33/1.00  res_num_of_loops:                       101
% 1.33/1.00  res_forward_subset_subsumed:            3
% 1.33/1.00  res_backward_subset_subsumed:           0
% 1.33/1.00  res_forward_subsumed:                   0
% 1.33/1.00  res_backward_subsumed:                  0
% 1.33/1.00  res_forward_subsumption_resolution:     0
% 1.33/1.00  res_backward_subsumption_resolution:    0
% 1.33/1.00  res_clause_to_clause_subsumption:       91
% 1.33/1.00  res_orphan_elimination:                 0
% 1.33/1.00  res_tautology_del:                      14
% 1.33/1.00  res_num_eq_res_simplified:              0
% 1.33/1.00  res_num_sel_changes:                    0
% 1.33/1.00  res_moves_from_active_to_pass:          0
% 1.33/1.00  
% 1.33/1.00  ------ Superposition
% 1.33/1.00  
% 1.33/1.00  sup_time_total:                         0.
% 1.33/1.00  sup_time_generating:                    0.
% 1.33/1.00  sup_time_sim_full:                      0.
% 1.33/1.00  sup_time_sim_immed:                     0.
% 1.33/1.00  
% 1.33/1.00  sup_num_of_clauses:                     18
% 1.33/1.00  sup_num_in_active:                      8
% 1.33/1.00  sup_num_in_passive:                     10
% 1.33/1.00  sup_num_of_loops:                       8
% 1.33/1.00  sup_fw_superposition:                   1
% 1.33/1.00  sup_bw_superposition:                   0
% 1.33/1.00  sup_immediate_simplified:               0
% 1.33/1.00  sup_given_eliminated:                   0
% 1.33/1.00  comparisons_done:                       0
% 1.33/1.00  comparisons_avoided:                    0
% 1.33/1.00  
% 1.33/1.00  ------ Simplifications
% 1.33/1.00  
% 1.33/1.00  
% 1.33/1.00  sim_fw_subset_subsumed:                 0
% 1.33/1.00  sim_bw_subset_subsumed:                 0
% 1.33/1.00  sim_fw_subsumed:                        0
% 1.33/1.00  sim_bw_subsumed:                        0
% 1.33/1.00  sim_fw_subsumption_res:                 0
% 1.33/1.00  sim_bw_subsumption_res:                 0
% 1.33/1.00  sim_tautology_del:                      0
% 1.33/1.00  sim_eq_tautology_del:                   0
% 1.33/1.00  sim_eq_res_simp:                        0
% 1.33/1.00  sim_fw_demodulated:                     0
% 1.33/1.00  sim_bw_demodulated:                     0
% 1.33/1.00  sim_light_normalised:                   0
% 1.33/1.00  sim_joinable_taut:                      0
% 1.33/1.00  sim_joinable_simp:                      0
% 1.33/1.00  sim_ac_normalised:                      0
% 1.33/1.00  sim_smt_subsumption:                    0
% 1.33/1.00  
%------------------------------------------------------------------------------
