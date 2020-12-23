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
% DateTime   : Thu Dec  3 12:25:34 EST 2020

% Result     : Theorem 1.13s
% Output     : CNFRefutation 1.13s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 768 expanded)
%              Number of clauses        :   96 ( 230 expanded)
%              Number of leaves         :   20 ( 158 expanded)
%              Depth                    :   21
%              Number of atoms          :  634 (3942 expanded)
%              Number of equality atoms :  113 ( 209 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f44,plain,(
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

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f47,plain,(
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

fof(f46,plain,
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

fof(f48,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
      | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) )
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f45,f47,f46])).

fof(f71,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f6,axiom,(
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

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f68,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f69,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v7_struct_0(X0)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f70,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f48])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v7_struct_0(X1)
      | v1_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
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
    inference(pure_predicate_removal,[],[f11])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v7_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f49,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

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

fof(f39,plain,(
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

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK0(X0)) = X0
        & m1_subset_1(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK0(X0)) = X0
            & m1_subset_1(sK0(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X0)
      | k6_domain_1(X0,X1) != X0
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

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

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_1573,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_2028,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2) = k6_domain_1(u1_struct_0(sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_1573])).

cnf(c_1575,plain,
    ( X0_45 != X1_45
    | X2_45 != X1_45
    | X2_45 = X0_45 ),
    theory(equality)).

cnf(c_1954,plain,
    ( k6_domain_1(u1_struct_0(sK1),X0_45) != X1_45
    | k6_domain_1(u1_struct_0(sK1),X0_45) = u1_struct_0(sK1)
    | u1_struct_0(sK1) != X1_45 ),
    inference(instantiation,[status(thm)],[c_1575])).

cnf(c_1973,plain,
    ( k6_domain_1(u1_struct_0(sK1),X0_45) != k6_domain_1(u1_struct_0(sK1),sK2)
    | k6_domain_1(u1_struct_0(sK1),X0_45) = u1_struct_0(sK1)
    | u1_struct_0(sK1) != k6_domain_1(u1_struct_0(sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_1954])).

cnf(c_1974,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2) != k6_domain_1(u1_struct_0(sK1),sK2)
    | k6_domain_1(u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | u1_struct_0(sK1) != k6_domain_1(u1_struct_0(sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_1973])).

cnf(c_20,negated_conjecture,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_176,plain,
    ( v1_tex_2(k1_tex_2(sK1,sK2),sK1)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
    inference(prop_impl,[status(thm)],[c_20])).

cnf(c_177,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(renaming,[status(thm)],[c_176])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tex_2(X0,X1)
    | ~ v7_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_14,plain,
    ( m1_pre_topc(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_392,plain,
    ( ~ v1_tex_2(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ v7_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | X3 != X1
    | k1_tex_2(X3,X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_14])).

cnf(c_393,plain,
    ( ~ v1_tex_2(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v7_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(k1_tex_2(X0,X1))
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_409,plain,
    ( ~ v1_tex_2(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v7_struct_0(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_393,c_15])).

cnf(c_432,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k1_tex_2(X1,X0) != k1_tex_2(sK1,sK2)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_177,c_409])).

cnf(c_433,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ v7_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | k1_tex_2(sK1,X0) != k1_tex_2(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_432])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_437,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ v7_struct_0(sK1)
    | k1_tex_2(sK1,X0) != k1_tex_2(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_433,c_23,c_22])).

cnf(c_1,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_18,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v7_struct_0(X0)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_302,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v7_struct_0(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_1,c_18])).

cnf(c_511,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v7_struct_0(X0)
    | v2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_302,c_22])).

cnf(c_512,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),X0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ v7_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_511])).

cnf(c_516,plain,
    ( ~ v7_struct_0(sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),X0),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_512,c_23])).

cnf(c_517,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),X0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ v7_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_516])).

cnf(c_986,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v7_struct_0(sK1)
    | k1_tex_2(sK1,X0) != k1_tex_2(sK1,sK2)
    | k6_domain_1(u1_struct_0(sK1),X1) != k6_domain_1(u1_struct_0(sK1),sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_437,c_517])).

cnf(c_1277,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v7_struct_0(sK1)
    | k1_tex_2(sK1,X0) != k1_tex_2(sK1,sK2)
    | k6_domain_1(u1_struct_0(sK1),X1) != k6_domain_1(u1_struct_0(sK1),sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_986])).

cnf(c_1557,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_45,u1_struct_0(sK1))
    | ~ v7_struct_0(sK1)
    | k1_tex_2(sK1,X0_45) != k1_tex_2(sK1,sK2)
    | k6_domain_1(u1_struct_0(sK1),X1_45) != k6_domain_1(u1_struct_0(sK1),sK2) ),
    inference(subtyping,[status(esa)],[c_1277])).

cnf(c_1571,plain,
    ( ~ v7_struct_0(sK1)
    | sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1557])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1583,plain,
    ( X0_46 != X1_46
    | k1_tex_2(X0_46,X0_45) = k1_tex_2(X1_46,X1_45)
    | X0_45 != X1_45 ),
    theory(equality)).

cnf(c_1590,plain,
    ( k1_tex_2(sK1,sK2) = k1_tex_2(sK1,sK2)
    | sK1 != sK1
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1583])).

cnf(c_1592,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1573])).

cnf(c_1574,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_1593,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1574])).

cnf(c_12,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_19,negated_conjecture,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_174,plain,
    ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_175,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(renaming,[status(thm)],[c_174])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_tex_2(X0,X1)
    | ~ v7_struct_0(X0)
    | v7_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_364,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ v7_struct_0(X0)
    | v7_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | X3 != X1
    | k1_tex_2(X3,X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_14])).

cnf(c_365,plain,
    ( v1_tex_2(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v7_struct_0(X0)
    | ~ v7_struct_0(k1_tex_2(X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(k1_tex_2(X0,X1))
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v7_struct_0(k1_tex_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_383,plain,
    ( v1_tex_2(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v7_struct_0(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_365,c_15,c_16])).

cnf(c_456,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | v7_struct_0(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k1_tex_2(X1,X0) != k1_tex_2(sK1,sK2)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_175,c_383])).

cnf(c_457,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v7_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | k1_tex_2(sK1,X0) != k1_tex_2(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_456])).

cnf(c_461,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v7_struct_0(sK1)
    | k1_tex_2(sK1,X0) != k1_tex_2(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_457,c_23,c_22])).

cnf(c_923,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | v7_struct_0(sK1)
    | X1 = X0
    | k1_tex_2(sK1,X2) != k1_tex_2(sK1,sK2)
    | k6_domain_1(u1_struct_0(sK1),sK2) != X0
    | u1_struct_0(sK1) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_461])).

cnf(c_924,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v7_struct_0(sK1)
    | k1_tex_2(sK1,X0) != k1_tex_2(sK1,sK2)
    | u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK1),sK2) ),
    inference(unflattening,[status(thm)],[c_923])).

cnf(c_1560,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(sK1))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v7_struct_0(sK1)
    | k1_tex_2(sK1,X0_45) != k1_tex_2(sK1,sK2)
    | u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK1),sK2) ),
    inference(subtyping,[status(esa)],[c_924])).

cnf(c_1567,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(sK1))
    | k1_tex_2(sK1,X0_45) != k1_tex_2(sK1,sK2)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1560])).

cnf(c_1612,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ sP0_iProver_split
    | k1_tex_2(sK1,sK2) != k1_tex_2(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1567])).

cnf(c_1668,plain,
    ( sP1_iProver_split
    | ~ v7_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1571,c_21,c_1590,c_1592,c_1593,c_1612])).

cnf(c_1669,plain,
    ( ~ v7_struct_0(sK1)
    | sP1_iProver_split ),
    inference(renaming,[status(thm)],[c_1668])).

cnf(c_1568,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v7_struct_0(sK1)
    | sP0_iProver_split
    | u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK1),sK2) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1560])).

cnf(c_26,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_336,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_1,c_2])).

cnf(c_490,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_336,c_22])).

cnf(c_491,plain,
    ( v2_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_70,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_73,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_493,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_491,c_23,c_22,c_70,c_73])).

cnf(c_712,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | u1_struct_0(sK1) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_493])).

cnf(c_713,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_712])).

cnf(c_1563,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(sK1))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK1),X0_45),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_713])).

cnf(c_1601,plain,
    ( m1_subset_1(X0_45,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK1),X0_45),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1563])).

cnf(c_1603,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1601])).

cnf(c_1610,plain,
    ( u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK1),sK2)
    | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v7_struct_0(sK1) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1568])).

cnf(c_1611,plain,
    ( k1_tex_2(sK1,X0_45) != k1_tex_2(sK1,sK2)
    | m1_subset_1(X0_45,u1_struct_0(sK1)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1567])).

cnf(c_1613,plain,
    ( k1_tex_2(sK1,sK2) != k1_tex_2(sK1,sK2)
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_1611])).

cnf(c_944,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ v7_struct_0(sK1)
    | X1 = X0
    | k6_domain_1(u1_struct_0(sK1),X2) != X0
    | u1_struct_0(sK1) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_517])).

cnf(c_945,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v7_struct_0(sK1)
    | u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK1),X0) ),
    inference(unflattening,[status(thm)],[c_944])).

cnf(c_949,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ v7_struct_0(sK1)
    | u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK1),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_945,c_713])).

cnf(c_1559,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(sK1))
    | ~ v7_struct_0(sK1)
    | u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK1),X0_45) ),
    inference(subtyping,[status(esa)],[c_949])).

cnf(c_1614,plain,
    ( u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK1),X0_45)
    | m1_subset_1(X0_45,u1_struct_0(sK1)) != iProver_top
    | v7_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1559])).

cnf(c_1616,plain,
    ( u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK1),sK2)
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v7_struct_0(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1614])).

cnf(c_1649,plain,
    ( u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK1),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1568,c_26,c_1590,c_1592,c_1593,c_1603,c_1610,c_1613,c_1616])).

cnf(c_1570,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(sK1))
    | k6_domain_1(u1_struct_0(sK1),X0_45) != k6_domain_1(u1_struct_0(sK1),sK2)
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_1557])).

cnf(c_1622,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ sP1_iProver_split
    | k6_domain_1(u1_struct_0(sK1),sK2) != k6_domain_1(u1_struct_0(sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_1570])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | v1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | v1_zfmisc_1(X1)
    | k6_domain_1(X1,X0) != X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_657,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_zfmisc_1(X2)
    | v1_zfmisc_1(X1)
    | X1 != X2
    | k6_domain_1(X1,X0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_9])).

cnf(c_658,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_zfmisc_1(X1)
    | k6_domain_1(X1,X0) != X1 ),
    inference(unflattening,[status(thm)],[c_657])).

cnf(c_3,plain,
    ( v7_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_zfmisc_1(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_322,plain,
    ( v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_zfmisc_1(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_1,c_3])).

cnf(c_501,plain,
    ( v7_struct_0(X0)
    | ~ v1_zfmisc_1(u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_322,c_22])).

cnf(c_502,plain,
    ( v7_struct_0(sK1)
    | ~ v1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_501])).

cnf(c_777,plain,
    ( ~ m1_subset_1(X0,X1)
    | v7_struct_0(sK1)
    | k6_domain_1(X1,X0) != X1
    | u1_struct_0(sK1) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_658,c_502])).

cnf(c_778,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v7_struct_0(sK1)
    | k6_domain_1(u1_struct_0(sK1),X0) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_777])).

cnf(c_1564,plain,
    ( ~ m1_subset_1(X0_45,u1_struct_0(sK1))
    | v7_struct_0(sK1)
    | k6_domain_1(u1_struct_0(sK1),X0_45) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_778])).

cnf(c_1599,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v7_struct_0(sK1)
    | k6_domain_1(u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1564])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2028,c_1974,c_1669,c_1649,c_1622,c_1599,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:02:56 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 1.01/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.01/0.99  
% 1.01/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.01/0.99  
% 1.01/0.99  ------  iProver source info
% 1.01/0.99  
% 1.01/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.01/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.01/0.99  git: non_committed_changes: false
% 1.01/0.99  git: last_make_outside_of_git: false
% 1.01/0.99  
% 1.01/0.99  ------ 
% 1.01/0.99  
% 1.01/0.99  ------ Input Options
% 1.01/0.99  
% 1.01/0.99  --out_options                           all
% 1.01/0.99  --tptp_safe_out                         true
% 1.01/0.99  --problem_path                          ""
% 1.01/0.99  --include_path                          ""
% 1.01/0.99  --clausifier                            res/vclausify_rel
% 1.01/0.99  --clausifier_options                    --mode clausify
% 1.01/0.99  --stdin                                 false
% 1.01/0.99  --stats_out                             all
% 1.01/0.99  
% 1.01/0.99  ------ General Options
% 1.01/0.99  
% 1.01/0.99  --fof                                   false
% 1.01/0.99  --time_out_real                         305.
% 1.01/0.99  --time_out_virtual                      -1.
% 1.01/0.99  --symbol_type_check                     false
% 1.01/0.99  --clausify_out                          false
% 1.01/0.99  --sig_cnt_out                           false
% 1.01/0.99  --trig_cnt_out                          false
% 1.01/0.99  --trig_cnt_out_tolerance                1.
% 1.01/0.99  --trig_cnt_out_sk_spl                   false
% 1.01/0.99  --abstr_cl_out                          false
% 1.01/0.99  
% 1.01/0.99  ------ Global Options
% 1.01/0.99  
% 1.01/0.99  --schedule                              default
% 1.01/0.99  --add_important_lit                     false
% 1.01/0.99  --prop_solver_per_cl                    1000
% 1.01/0.99  --min_unsat_core                        false
% 1.01/0.99  --soft_assumptions                      false
% 1.01/0.99  --soft_lemma_size                       3
% 1.01/0.99  --prop_impl_unit_size                   0
% 1.01/0.99  --prop_impl_unit                        []
% 1.01/0.99  --share_sel_clauses                     true
% 1.01/0.99  --reset_solvers                         false
% 1.01/0.99  --bc_imp_inh                            [conj_cone]
% 1.01/0.99  --conj_cone_tolerance                   3.
% 1.01/0.99  --extra_neg_conj                        none
% 1.01/0.99  --large_theory_mode                     true
% 1.01/0.99  --prolific_symb_bound                   200
% 1.01/0.99  --lt_threshold                          2000
% 1.01/0.99  --clause_weak_htbl                      true
% 1.01/0.99  --gc_record_bc_elim                     false
% 1.01/0.99  
% 1.01/0.99  ------ Preprocessing Options
% 1.01/0.99  
% 1.01/0.99  --preprocessing_flag                    true
% 1.01/0.99  --time_out_prep_mult                    0.1
% 1.01/0.99  --splitting_mode                        input
% 1.01/0.99  --splitting_grd                         true
% 1.01/0.99  --splitting_cvd                         false
% 1.01/0.99  --splitting_cvd_svl                     false
% 1.01/0.99  --splitting_nvd                         32
% 1.01/0.99  --sub_typing                            true
% 1.01/0.99  --prep_gs_sim                           true
% 1.01/0.99  --prep_unflatten                        true
% 1.01/0.99  --prep_res_sim                          true
% 1.01/0.99  --prep_upred                            true
% 1.01/0.99  --prep_sem_filter                       exhaustive
% 1.01/0.99  --prep_sem_filter_out                   false
% 1.01/0.99  --pred_elim                             true
% 1.01/0.99  --res_sim_input                         true
% 1.01/0.99  --eq_ax_congr_red                       true
% 1.01/0.99  --pure_diseq_elim                       true
% 1.01/0.99  --brand_transform                       false
% 1.01/0.99  --non_eq_to_eq                          false
% 1.01/0.99  --prep_def_merge                        true
% 1.01/0.99  --prep_def_merge_prop_impl              false
% 1.01/0.99  --prep_def_merge_mbd                    true
% 1.01/0.99  --prep_def_merge_tr_red                 false
% 1.01/0.99  --prep_def_merge_tr_cl                  false
% 1.01/0.99  --smt_preprocessing                     true
% 1.01/0.99  --smt_ac_axioms                         fast
% 1.01/0.99  --preprocessed_out                      false
% 1.01/0.99  --preprocessed_stats                    false
% 1.01/0.99  
% 1.01/0.99  ------ Abstraction refinement Options
% 1.01/0.99  
% 1.01/0.99  --abstr_ref                             []
% 1.01/0.99  --abstr_ref_prep                        false
% 1.01/0.99  --abstr_ref_until_sat                   false
% 1.01/0.99  --abstr_ref_sig_restrict                funpre
% 1.01/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.01/0.99  --abstr_ref_under                       []
% 1.01/0.99  
% 1.01/0.99  ------ SAT Options
% 1.01/0.99  
% 1.01/0.99  --sat_mode                              false
% 1.01/0.99  --sat_fm_restart_options                ""
% 1.01/0.99  --sat_gr_def                            false
% 1.01/0.99  --sat_epr_types                         true
% 1.01/0.99  --sat_non_cyclic_types                  false
% 1.01/0.99  --sat_finite_models                     false
% 1.01/0.99  --sat_fm_lemmas                         false
% 1.01/0.99  --sat_fm_prep                           false
% 1.01/0.99  --sat_fm_uc_incr                        true
% 1.01/0.99  --sat_out_model                         small
% 1.01/0.99  --sat_out_clauses                       false
% 1.01/0.99  
% 1.01/0.99  ------ QBF Options
% 1.01/0.99  
% 1.01/0.99  --qbf_mode                              false
% 1.01/0.99  --qbf_elim_univ                         false
% 1.01/0.99  --qbf_dom_inst                          none
% 1.01/0.99  --qbf_dom_pre_inst                      false
% 1.01/0.99  --qbf_sk_in                             false
% 1.01/0.99  --qbf_pred_elim                         true
% 1.01/0.99  --qbf_split                             512
% 1.01/0.99  
% 1.01/0.99  ------ BMC1 Options
% 1.01/0.99  
% 1.01/0.99  --bmc1_incremental                      false
% 1.01/0.99  --bmc1_axioms                           reachable_all
% 1.01/0.99  --bmc1_min_bound                        0
% 1.01/0.99  --bmc1_max_bound                        -1
% 1.01/0.99  --bmc1_max_bound_default                -1
% 1.01/0.99  --bmc1_symbol_reachability              true
% 1.01/0.99  --bmc1_property_lemmas                  false
% 1.01/0.99  --bmc1_k_induction                      false
% 1.01/0.99  --bmc1_non_equiv_states                 false
% 1.01/0.99  --bmc1_deadlock                         false
% 1.01/0.99  --bmc1_ucm                              false
% 1.01/0.99  --bmc1_add_unsat_core                   none
% 1.01/0.99  --bmc1_unsat_core_children              false
% 1.01/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.01/0.99  --bmc1_out_stat                         full
% 1.01/0.99  --bmc1_ground_init                      false
% 1.01/0.99  --bmc1_pre_inst_next_state              false
% 1.01/0.99  --bmc1_pre_inst_state                   false
% 1.01/0.99  --bmc1_pre_inst_reach_state             false
% 1.01/0.99  --bmc1_out_unsat_core                   false
% 1.01/0.99  --bmc1_aig_witness_out                  false
% 1.01/0.99  --bmc1_verbose                          false
% 1.01/0.99  --bmc1_dump_clauses_tptp                false
% 1.01/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.01/0.99  --bmc1_dump_file                        -
% 1.01/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.01/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.01/0.99  --bmc1_ucm_extend_mode                  1
% 1.01/0.99  --bmc1_ucm_init_mode                    2
% 1.01/0.99  --bmc1_ucm_cone_mode                    none
% 1.01/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.01/0.99  --bmc1_ucm_relax_model                  4
% 1.01/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.01/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.01/0.99  --bmc1_ucm_layered_model                none
% 1.01/0.99  --bmc1_ucm_max_lemma_size               10
% 1.01/0.99  
% 1.01/0.99  ------ AIG Options
% 1.01/0.99  
% 1.01/0.99  --aig_mode                              false
% 1.01/0.99  
% 1.01/0.99  ------ Instantiation Options
% 1.01/0.99  
% 1.01/0.99  --instantiation_flag                    true
% 1.01/0.99  --inst_sos_flag                         false
% 1.01/0.99  --inst_sos_phase                        true
% 1.01/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.01/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.01/0.99  --inst_lit_sel_side                     num_symb
% 1.01/0.99  --inst_solver_per_active                1400
% 1.01/0.99  --inst_solver_calls_frac                1.
% 1.01/0.99  --inst_passive_queue_type               priority_queues
% 1.01/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.01/0.99  --inst_passive_queues_freq              [25;2]
% 1.01/0.99  --inst_dismatching                      true
% 1.01/0.99  --inst_eager_unprocessed_to_passive     true
% 1.01/0.99  --inst_prop_sim_given                   true
% 1.01/0.99  --inst_prop_sim_new                     false
% 1.01/0.99  --inst_subs_new                         false
% 1.01/0.99  --inst_eq_res_simp                      false
% 1.01/0.99  --inst_subs_given                       false
% 1.01/0.99  --inst_orphan_elimination               true
% 1.01/0.99  --inst_learning_loop_flag               true
% 1.01/0.99  --inst_learning_start                   3000
% 1.01/0.99  --inst_learning_factor                  2
% 1.01/0.99  --inst_start_prop_sim_after_learn       3
% 1.01/0.99  --inst_sel_renew                        solver
% 1.01/0.99  --inst_lit_activity_flag                true
% 1.01/0.99  --inst_restr_to_given                   false
% 1.01/0.99  --inst_activity_threshold               500
% 1.01/0.99  --inst_out_proof                        true
% 1.01/0.99  
% 1.01/0.99  ------ Resolution Options
% 1.01/0.99  
% 1.01/0.99  --resolution_flag                       true
% 1.01/0.99  --res_lit_sel                           adaptive
% 1.01/0.99  --res_lit_sel_side                      none
% 1.01/0.99  --res_ordering                          kbo
% 1.01/0.99  --res_to_prop_solver                    active
% 1.01/0.99  --res_prop_simpl_new                    false
% 1.01/0.99  --res_prop_simpl_given                  true
% 1.01/0.99  --res_passive_queue_type                priority_queues
% 1.01/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.01/0.99  --res_passive_queues_freq               [15;5]
% 1.01/0.99  --res_forward_subs                      full
% 1.01/0.99  --res_backward_subs                     full
% 1.01/0.99  --res_forward_subs_resolution           true
% 1.01/0.99  --res_backward_subs_resolution          true
% 1.01/0.99  --res_orphan_elimination                true
% 1.01/0.99  --res_time_limit                        2.
% 1.01/0.99  --res_out_proof                         true
% 1.01/0.99  
% 1.01/0.99  ------ Superposition Options
% 1.01/0.99  
% 1.01/0.99  --superposition_flag                    true
% 1.01/0.99  --sup_passive_queue_type                priority_queues
% 1.01/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.01/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.01/0.99  --demod_completeness_check              fast
% 1.01/0.99  --demod_use_ground                      true
% 1.01/0.99  --sup_to_prop_solver                    passive
% 1.01/0.99  --sup_prop_simpl_new                    true
% 1.01/0.99  --sup_prop_simpl_given                  true
% 1.01/0.99  --sup_fun_splitting                     false
% 1.01/0.99  --sup_smt_interval                      50000
% 1.01/0.99  
% 1.01/0.99  ------ Superposition Simplification Setup
% 1.01/0.99  
% 1.01/0.99  --sup_indices_passive                   []
% 1.01/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.01/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/0.99  --sup_full_bw                           [BwDemod]
% 1.01/0.99  --sup_immed_triv                        [TrivRules]
% 1.01/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.01/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/0.99  --sup_immed_bw_main                     []
% 1.01/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.01/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.01/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.01/0.99  
% 1.01/0.99  ------ Combination Options
% 1.01/0.99  
% 1.01/0.99  --comb_res_mult                         3
% 1.01/0.99  --comb_sup_mult                         2
% 1.01/0.99  --comb_inst_mult                        10
% 1.01/0.99  
% 1.01/0.99  ------ Debug Options
% 1.01/0.99  
% 1.01/0.99  --dbg_backtrace                         false
% 1.01/0.99  --dbg_dump_prop_clauses                 false
% 1.01/0.99  --dbg_dump_prop_clauses_file            -
% 1.01/0.99  --dbg_out_stat                          false
% 1.01/0.99  ------ Parsing...
% 1.01/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.01/0.99  
% 1.01/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 1.01/0.99  
% 1.01/0.99  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.01/0.99  
% 1.01/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.01/0.99  ------ Proving...
% 1.01/0.99  ------ Problem Properties 
% 1.01/0.99  
% 1.01/0.99  
% 1.01/0.99  clauses                                 14
% 1.01/0.99  conjectures                             1
% 1.01/0.99  EPR                                     1
% 1.01/0.99  Horn                                    12
% 1.01/0.99  unary                                   1
% 1.01/0.99  binary                                  2
% 1.01/0.99  lits                                    40
% 1.01/0.99  lits eq                                 11
% 1.01/0.99  fd_pure                                 0
% 1.01/0.99  fd_pseudo                               0
% 1.01/0.99  fd_cond                                 0
% 1.01/0.99  fd_pseudo_cond                          0
% 1.01/0.99  AC symbols                              0
% 1.01/0.99  
% 1.01/0.99  ------ Schedule dynamic 5 is on 
% 1.01/0.99  
% 1.01/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.01/0.99  
% 1.01/0.99  
% 1.01/0.99  ------ 
% 1.01/0.99  Current options:
% 1.01/0.99  ------ 
% 1.01/0.99  
% 1.01/0.99  ------ Input Options
% 1.01/0.99  
% 1.01/0.99  --out_options                           all
% 1.01/0.99  --tptp_safe_out                         true
% 1.01/0.99  --problem_path                          ""
% 1.01/0.99  --include_path                          ""
% 1.01/0.99  --clausifier                            res/vclausify_rel
% 1.01/0.99  --clausifier_options                    --mode clausify
% 1.01/0.99  --stdin                                 false
% 1.01/0.99  --stats_out                             all
% 1.01/0.99  
% 1.01/0.99  ------ General Options
% 1.01/0.99  
% 1.01/0.99  --fof                                   false
% 1.01/0.99  --time_out_real                         305.
% 1.01/0.99  --time_out_virtual                      -1.
% 1.01/0.99  --symbol_type_check                     false
% 1.01/0.99  --clausify_out                          false
% 1.01/0.99  --sig_cnt_out                           false
% 1.01/0.99  --trig_cnt_out                          false
% 1.01/0.99  --trig_cnt_out_tolerance                1.
% 1.01/0.99  --trig_cnt_out_sk_spl                   false
% 1.01/0.99  --abstr_cl_out                          false
% 1.01/0.99  
% 1.01/0.99  ------ Global Options
% 1.01/0.99  
% 1.01/0.99  --schedule                              default
% 1.01/0.99  --add_important_lit                     false
% 1.01/0.99  --prop_solver_per_cl                    1000
% 1.01/0.99  --min_unsat_core                        false
% 1.01/0.99  --soft_assumptions                      false
% 1.01/0.99  --soft_lemma_size                       3
% 1.01/0.99  --prop_impl_unit_size                   0
% 1.01/0.99  --prop_impl_unit                        []
% 1.01/0.99  --share_sel_clauses                     true
% 1.01/0.99  --reset_solvers                         false
% 1.01/0.99  --bc_imp_inh                            [conj_cone]
% 1.01/0.99  --conj_cone_tolerance                   3.
% 1.01/0.99  --extra_neg_conj                        none
% 1.01/0.99  --large_theory_mode                     true
% 1.01/0.99  --prolific_symb_bound                   200
% 1.01/0.99  --lt_threshold                          2000
% 1.01/0.99  --clause_weak_htbl                      true
% 1.01/0.99  --gc_record_bc_elim                     false
% 1.01/0.99  
% 1.01/0.99  ------ Preprocessing Options
% 1.01/0.99  
% 1.01/0.99  --preprocessing_flag                    true
% 1.01/0.99  --time_out_prep_mult                    0.1
% 1.01/0.99  --splitting_mode                        input
% 1.01/0.99  --splitting_grd                         true
% 1.01/0.99  --splitting_cvd                         false
% 1.01/0.99  --splitting_cvd_svl                     false
% 1.01/0.99  --splitting_nvd                         32
% 1.01/0.99  --sub_typing                            true
% 1.01/0.99  --prep_gs_sim                           true
% 1.01/0.99  --prep_unflatten                        true
% 1.01/0.99  --prep_res_sim                          true
% 1.01/0.99  --prep_upred                            true
% 1.01/0.99  --prep_sem_filter                       exhaustive
% 1.01/0.99  --prep_sem_filter_out                   false
% 1.01/0.99  --pred_elim                             true
% 1.01/0.99  --res_sim_input                         true
% 1.01/0.99  --eq_ax_congr_red                       true
% 1.01/0.99  --pure_diseq_elim                       true
% 1.01/0.99  --brand_transform                       false
% 1.01/0.99  --non_eq_to_eq                          false
% 1.01/0.99  --prep_def_merge                        true
% 1.01/0.99  --prep_def_merge_prop_impl              false
% 1.01/0.99  --prep_def_merge_mbd                    true
% 1.01/0.99  --prep_def_merge_tr_red                 false
% 1.01/0.99  --prep_def_merge_tr_cl                  false
% 1.01/0.99  --smt_preprocessing                     true
% 1.01/0.99  --smt_ac_axioms                         fast
% 1.01/0.99  --preprocessed_out                      false
% 1.01/0.99  --preprocessed_stats                    false
% 1.01/0.99  
% 1.01/0.99  ------ Abstraction refinement Options
% 1.01/0.99  
% 1.01/0.99  --abstr_ref                             []
% 1.01/0.99  --abstr_ref_prep                        false
% 1.01/0.99  --abstr_ref_until_sat                   false
% 1.01/0.99  --abstr_ref_sig_restrict                funpre
% 1.01/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.01/0.99  --abstr_ref_under                       []
% 1.01/0.99  
% 1.01/0.99  ------ SAT Options
% 1.01/0.99  
% 1.01/0.99  --sat_mode                              false
% 1.01/0.99  --sat_fm_restart_options                ""
% 1.01/0.99  --sat_gr_def                            false
% 1.01/0.99  --sat_epr_types                         true
% 1.01/0.99  --sat_non_cyclic_types                  false
% 1.01/0.99  --sat_finite_models                     false
% 1.01/0.99  --sat_fm_lemmas                         false
% 1.01/0.99  --sat_fm_prep                           false
% 1.01/0.99  --sat_fm_uc_incr                        true
% 1.01/0.99  --sat_out_model                         small
% 1.01/0.99  --sat_out_clauses                       false
% 1.01/0.99  
% 1.01/0.99  ------ QBF Options
% 1.01/0.99  
% 1.01/0.99  --qbf_mode                              false
% 1.01/0.99  --qbf_elim_univ                         false
% 1.01/0.99  --qbf_dom_inst                          none
% 1.01/0.99  --qbf_dom_pre_inst                      false
% 1.01/0.99  --qbf_sk_in                             false
% 1.01/0.99  --qbf_pred_elim                         true
% 1.01/0.99  --qbf_split                             512
% 1.01/0.99  
% 1.01/0.99  ------ BMC1 Options
% 1.01/0.99  
% 1.01/0.99  --bmc1_incremental                      false
% 1.01/0.99  --bmc1_axioms                           reachable_all
% 1.01/0.99  --bmc1_min_bound                        0
% 1.01/0.99  --bmc1_max_bound                        -1
% 1.01/0.99  --bmc1_max_bound_default                -1
% 1.13/0.99  --bmc1_symbol_reachability              true
% 1.13/0.99  --bmc1_property_lemmas                  false
% 1.13/0.99  --bmc1_k_induction                      false
% 1.13/0.99  --bmc1_non_equiv_states                 false
% 1.13/0.99  --bmc1_deadlock                         false
% 1.13/0.99  --bmc1_ucm                              false
% 1.13/0.99  --bmc1_add_unsat_core                   none
% 1.13/0.99  --bmc1_unsat_core_children              false
% 1.13/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.13/0.99  --bmc1_out_stat                         full
% 1.13/0.99  --bmc1_ground_init                      false
% 1.13/0.99  --bmc1_pre_inst_next_state              false
% 1.13/0.99  --bmc1_pre_inst_state                   false
% 1.13/0.99  --bmc1_pre_inst_reach_state             false
% 1.13/0.99  --bmc1_out_unsat_core                   false
% 1.13/0.99  --bmc1_aig_witness_out                  false
% 1.13/0.99  --bmc1_verbose                          false
% 1.13/0.99  --bmc1_dump_clauses_tptp                false
% 1.13/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.13/0.99  --bmc1_dump_file                        -
% 1.13/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.13/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.13/0.99  --bmc1_ucm_extend_mode                  1
% 1.13/0.99  --bmc1_ucm_init_mode                    2
% 1.13/0.99  --bmc1_ucm_cone_mode                    none
% 1.13/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.13/0.99  --bmc1_ucm_relax_model                  4
% 1.13/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.13/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.13/0.99  --bmc1_ucm_layered_model                none
% 1.13/0.99  --bmc1_ucm_max_lemma_size               10
% 1.13/0.99  
% 1.13/0.99  ------ AIG Options
% 1.13/0.99  
% 1.13/0.99  --aig_mode                              false
% 1.13/0.99  
% 1.13/0.99  ------ Instantiation Options
% 1.13/0.99  
% 1.13/0.99  --instantiation_flag                    true
% 1.13/0.99  --inst_sos_flag                         false
% 1.13/0.99  --inst_sos_phase                        true
% 1.13/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.13/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.13/0.99  --inst_lit_sel_side                     none
% 1.13/0.99  --inst_solver_per_active                1400
% 1.13/0.99  --inst_solver_calls_frac                1.
% 1.13/0.99  --inst_passive_queue_type               priority_queues
% 1.13/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.13/0.99  --inst_passive_queues_freq              [25;2]
% 1.13/0.99  --inst_dismatching                      true
% 1.13/0.99  --inst_eager_unprocessed_to_passive     true
% 1.13/0.99  --inst_prop_sim_given                   true
% 1.13/0.99  --inst_prop_sim_new                     false
% 1.13/0.99  --inst_subs_new                         false
% 1.13/0.99  --inst_eq_res_simp                      false
% 1.13/0.99  --inst_subs_given                       false
% 1.13/0.99  --inst_orphan_elimination               true
% 1.13/0.99  --inst_learning_loop_flag               true
% 1.13/0.99  --inst_learning_start                   3000
% 1.13/0.99  --inst_learning_factor                  2
% 1.13/0.99  --inst_start_prop_sim_after_learn       3
% 1.13/0.99  --inst_sel_renew                        solver
% 1.13/0.99  --inst_lit_activity_flag                true
% 1.13/0.99  --inst_restr_to_given                   false
% 1.13/0.99  --inst_activity_threshold               500
% 1.13/0.99  --inst_out_proof                        true
% 1.13/0.99  
% 1.13/0.99  ------ Resolution Options
% 1.13/0.99  
% 1.13/0.99  --resolution_flag                       false
% 1.13/0.99  --res_lit_sel                           adaptive
% 1.13/0.99  --res_lit_sel_side                      none
% 1.13/0.99  --res_ordering                          kbo
% 1.13/0.99  --res_to_prop_solver                    active
% 1.13/0.99  --res_prop_simpl_new                    false
% 1.13/0.99  --res_prop_simpl_given                  true
% 1.13/0.99  --res_passive_queue_type                priority_queues
% 1.13/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.13/0.99  --res_passive_queues_freq               [15;5]
% 1.13/0.99  --res_forward_subs                      full
% 1.13/0.99  --res_backward_subs                     full
% 1.13/0.99  --res_forward_subs_resolution           true
% 1.13/0.99  --res_backward_subs_resolution          true
% 1.13/0.99  --res_orphan_elimination                true
% 1.13/0.99  --res_time_limit                        2.
% 1.13/0.99  --res_out_proof                         true
% 1.13/0.99  
% 1.13/0.99  ------ Superposition Options
% 1.13/0.99  
% 1.13/0.99  --superposition_flag                    true
% 1.13/0.99  --sup_passive_queue_type                priority_queues
% 1.13/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.13/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.13/0.99  --demod_completeness_check              fast
% 1.13/0.99  --demod_use_ground                      true
% 1.13/0.99  --sup_to_prop_solver                    passive
% 1.13/0.99  --sup_prop_simpl_new                    true
% 1.13/0.99  --sup_prop_simpl_given                  true
% 1.13/0.99  --sup_fun_splitting                     false
% 1.13/0.99  --sup_smt_interval                      50000
% 1.13/0.99  
% 1.13/0.99  ------ Superposition Simplification Setup
% 1.13/0.99  
% 1.13/0.99  --sup_indices_passive                   []
% 1.13/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.13/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.13/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.13/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.13/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.13/0.99  --sup_full_bw                           [BwDemod]
% 1.13/0.99  --sup_immed_triv                        [TrivRules]
% 1.13/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.13/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.13/0.99  --sup_immed_bw_main                     []
% 1.13/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.13/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.13/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.13/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.13/0.99  
% 1.13/0.99  ------ Combination Options
% 1.13/0.99  
% 1.13/0.99  --comb_res_mult                         3
% 1.13/0.99  --comb_sup_mult                         2
% 1.13/0.99  --comb_inst_mult                        10
% 1.13/0.99  
% 1.13/0.99  ------ Debug Options
% 1.13/0.99  
% 1.13/0.99  --dbg_backtrace                         false
% 1.13/0.99  --dbg_dump_prop_clauses                 false
% 1.13/0.99  --dbg_dump_prop_clauses_file            -
% 1.13/0.99  --dbg_out_stat                          false
% 1.13/0.99  
% 1.13/0.99  
% 1.13/0.99  
% 1.13/0.99  
% 1.13/0.99  ------ Proving...
% 1.13/0.99  
% 1.13/0.99  
% 1.13/0.99  % SZS status Theorem for theBenchmark.p
% 1.13/0.99  
% 1.13/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.13/0.99  
% 1.13/0.99  fof(f13,conjecture,(
% 1.13/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 1.13/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.13/0.99  
% 1.13/0.99  fof(f14,negated_conjecture,(
% 1.13/0.99    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 1.13/0.99    inference(negated_conjecture,[],[f13])).
% 1.13/0.99  
% 1.13/0.99  fof(f37,plain,(
% 1.13/0.99    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.13/0.99    inference(ennf_transformation,[],[f14])).
% 1.13/0.99  
% 1.13/0.99  fof(f38,plain,(
% 1.13/0.99    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.13/0.99    inference(flattening,[],[f37])).
% 1.13/0.99  
% 1.13/0.99  fof(f44,plain,(
% 1.13/0.99    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.13/0.99    inference(nnf_transformation,[],[f38])).
% 1.13/0.99  
% 1.13/0.99  fof(f45,plain,(
% 1.13/0.99    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.13/0.99    inference(flattening,[],[f44])).
% 1.13/0.99  
% 1.13/0.99  fof(f47,plain,(
% 1.13/0.99    ( ! [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),sK2),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,sK2),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),sK2),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,sK2),X0)) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 1.13/0.99    introduced(choice_axiom,[])).
% 1.13/0.99  
% 1.13/0.99  fof(f46,plain,(
% 1.13/0.99    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK1),X1),u1_struct_0(sK1)) | ~v1_tex_2(k1_tex_2(sK1,X1),sK1)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK1),X1),u1_struct_0(sK1)) | v1_tex_2(k1_tex_2(sK1,X1),sK1)) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.13/0.99    introduced(choice_axiom,[])).
% 1.13/0.99  
% 1.13/0.99  fof(f48,plain,(
% 1.13/0.99    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | ~v1_tex_2(k1_tex_2(sK1,sK2),sK1)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | v1_tex_2(k1_tex_2(sK1,sK2),sK1)) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 1.13/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f45,f47,f46])).
% 1.13/0.99  
% 1.13/0.99  fof(f71,plain,(
% 1.13/0.99    v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | v1_tex_2(k1_tex_2(sK1,sK2),sK1)),
% 1.13/0.99    inference(cnf_transformation,[],[f48])).
% 1.13/0.99  
% 1.13/0.99  fof(f6,axiom,(
% 1.13/0.99    ! [X0] : ((l1_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (~v2_struct_0(X1) => (~v1_tex_2(X1,X0) & ~v2_struct_0(X1)))))),
% 1.13/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.13/0.99  
% 1.13/0.99  fof(f25,plain,(
% 1.13/0.99    ! [X0] : (! [X1] : (((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)))),
% 1.13/0.99    inference(ennf_transformation,[],[f6])).
% 1.13/0.99  
% 1.13/0.99  fof(f26,plain,(
% 1.13/0.99    ! [X0] : (! [X1] : ((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))),
% 1.13/0.99    inference(flattening,[],[f25])).
% 1.13/0.99  
% 1.13/0.99  fof(f55,plain,(
% 1.13/0.99    ( ! [X0,X1] : (~v1_tex_2(X1,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)) )),
% 1.13/0.99    inference(cnf_transformation,[],[f26])).
% 1.13/0.99  
% 1.13/0.99  fof(f10,axiom,(
% 1.13/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.13/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.13/0.99  
% 1.13/0.99  fof(f15,plain,(
% 1.13/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.13/0.99    inference(pure_predicate_removal,[],[f10])).
% 1.13/0.99  
% 1.13/0.99  fof(f31,plain,(
% 1.13/0.99    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.13/0.99    inference(ennf_transformation,[],[f15])).
% 1.13/0.99  
% 1.13/0.99  fof(f32,plain,(
% 1.13/0.99    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.13/0.99    inference(flattening,[],[f31])).
% 1.13/0.99  
% 1.13/0.99  fof(f64,plain,(
% 1.13/0.99    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.13/0.99    inference(cnf_transformation,[],[f32])).
% 1.13/0.99  
% 1.13/0.99  fof(f63,plain,(
% 1.13/0.99    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.13/0.99    inference(cnf_transformation,[],[f32])).
% 1.13/0.99  
% 1.13/0.99  fof(f68,plain,(
% 1.13/0.99    ~v2_struct_0(sK1)),
% 1.13/0.99    inference(cnf_transformation,[],[f48])).
% 1.13/0.99  
% 1.13/0.99  fof(f69,plain,(
% 1.13/0.99    l1_pre_topc(sK1)),
% 1.13/0.99    inference(cnf_transformation,[],[f48])).
% 1.13/0.99  
% 1.13/0.99  fof(f2,axiom,(
% 1.13/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.13/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.13/0.99  
% 1.13/0.99  fof(f18,plain,(
% 1.13/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.13/0.99    inference(ennf_transformation,[],[f2])).
% 1.13/0.99  
% 1.13/0.99  fof(f50,plain,(
% 1.13/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.13/0.99    inference(cnf_transformation,[],[f18])).
% 1.13/0.99  
% 1.13/0.99  fof(f12,axiom,(
% 1.13/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 1.13/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.13/0.99  
% 1.13/0.99  fof(f35,plain,(
% 1.13/0.99    ! [X0] : (! [X1] : ((~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.13/0.99    inference(ennf_transformation,[],[f12])).
% 1.13/0.99  
% 1.13/0.99  fof(f36,plain,(
% 1.13/0.99    ! [X0] : (! [X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.13/0.99    inference(flattening,[],[f35])).
% 1.13/0.99  
% 1.13/0.99  fof(f67,plain,(
% 1.13/0.99    ( ! [X0,X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.13/0.99    inference(cnf_transformation,[],[f36])).
% 1.13/0.99  
% 1.13/0.99  fof(f70,plain,(
% 1.13/0.99    m1_subset_1(sK2,u1_struct_0(sK1))),
% 1.13/0.99    inference(cnf_transformation,[],[f48])).
% 1.13/0.99  
% 1.13/0.99  fof(f9,axiom,(
% 1.13/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.13/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.13/0.99  
% 1.13/0.99  fof(f30,plain,(
% 1.13/0.99    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.13/0.99    inference(ennf_transformation,[],[f9])).
% 1.13/0.99  
% 1.13/0.99  fof(f43,plain,(
% 1.13/0.99    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.13/0.99    inference(nnf_transformation,[],[f30])).
% 1.13/0.99  
% 1.13/0.99  fof(f62,plain,(
% 1.13/0.99    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.13/0.99    inference(cnf_transformation,[],[f43])).
% 1.13/0.99  
% 1.13/0.99  fof(f72,plain,(
% 1.13/0.99    ~v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | ~v1_tex_2(k1_tex_2(sK1,sK2),sK1)),
% 1.13/0.99    inference(cnf_transformation,[],[f48])).
% 1.13/0.99  
% 1.13/0.99  fof(f7,axiom,(
% 1.13/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) => (~v7_struct_0(X1) & ~v2_struct_0(X1)))))),
% 1.13/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.13/0.99  
% 1.13/0.99  fof(f27,plain,(
% 1.13/0.99    ! [X0] : (! [X1] : (((~v7_struct_0(X1) & ~v2_struct_0(X1)) | (v1_tex_2(X1,X0) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v7_struct_0(X0) | v2_struct_0(X0)))),
% 1.13/0.99    inference(ennf_transformation,[],[f7])).
% 1.13/0.99  
% 1.13/0.99  fof(f28,plain,(
% 1.13/0.99    ! [X0] : (! [X1] : ((~v7_struct_0(X1) & ~v2_struct_0(X1)) | v1_tex_2(X1,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v7_struct_0(X0) | v2_struct_0(X0))),
% 1.13/0.99    inference(flattening,[],[f27])).
% 1.13/0.99  
% 1.13/0.99  fof(f57,plain,(
% 1.13/0.99    ( ! [X0,X1] : (~v7_struct_0(X1) | v1_tex_2(X1,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v7_struct_0(X0) | v2_struct_0(X0)) )),
% 1.13/0.99    inference(cnf_transformation,[],[f28])).
% 1.13/0.99  
% 1.13/0.99  fof(f11,axiom,(
% 1.13/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.13/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.13/0.99  
% 1.13/0.99  fof(f16,plain,(
% 1.13/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.13/0.99    inference(pure_predicate_removal,[],[f11])).
% 1.13/0.99  
% 1.13/0.99  fof(f33,plain,(
% 1.13/0.99    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.13/0.99    inference(ennf_transformation,[],[f16])).
% 1.13/0.99  
% 1.13/0.99  fof(f34,plain,(
% 1.13/0.99    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.13/0.99    inference(flattening,[],[f33])).
% 1.13/0.99  
% 1.13/0.99  fof(f66,plain,(
% 1.13/0.99    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.13/0.99    inference(cnf_transformation,[],[f34])).
% 1.13/0.99  
% 1.13/0.99  fof(f5,axiom,(
% 1.13/0.99    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.13/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.13/0.99  
% 1.13/0.99  fof(f23,plain,(
% 1.13/0.99    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.13/0.99    inference(ennf_transformation,[],[f5])).
% 1.13/0.99  
% 1.13/0.99  fof(f24,plain,(
% 1.13/0.99    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.13/0.99    inference(flattening,[],[f23])).
% 1.13/0.99  
% 1.13/0.99  fof(f53,plain,(
% 1.13/0.99    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.13/0.99    inference(cnf_transformation,[],[f24])).
% 1.13/0.99  
% 1.13/0.99  fof(f3,axiom,(
% 1.13/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.13/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.13/0.99  
% 1.13/0.99  fof(f19,plain,(
% 1.13/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.13/0.99    inference(ennf_transformation,[],[f3])).
% 1.13/0.99  
% 1.13/0.99  fof(f20,plain,(
% 1.13/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.13/0.99    inference(flattening,[],[f19])).
% 1.13/0.99  
% 1.13/0.99  fof(f51,plain,(
% 1.13/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.13/0.99    inference(cnf_transformation,[],[f20])).
% 1.13/0.99  
% 1.13/0.99  fof(f1,axiom,(
% 1.13/0.99    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 1.13/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.13/0.99  
% 1.13/0.99  fof(f17,plain,(
% 1.13/0.99    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 1.13/0.99    inference(ennf_transformation,[],[f1])).
% 1.13/0.99  
% 1.13/0.99  fof(f49,plain,(
% 1.13/0.99    ( ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0)) )),
% 1.13/0.99    inference(cnf_transformation,[],[f17])).
% 1.13/0.99  
% 1.13/0.99  fof(f8,axiom,(
% 1.13/0.99    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 1.13/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.13/0.99  
% 1.13/0.99  fof(f29,plain,(
% 1.13/0.99    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 1.13/0.99    inference(ennf_transformation,[],[f8])).
% 1.13/0.99  
% 1.13/0.99  fof(f39,plain,(
% 1.13/0.99    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 1.13/0.99    inference(nnf_transformation,[],[f29])).
% 1.13/0.99  
% 1.13/0.99  fof(f40,plain,(
% 1.13/0.99    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 1.13/0.99    inference(rectify,[],[f39])).
% 1.13/0.99  
% 1.13/0.99  fof(f41,plain,(
% 1.13/0.99    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK0(X0)) = X0 & m1_subset_1(sK0(X0),X0)))),
% 1.13/0.99    introduced(choice_axiom,[])).
% 1.13/0.99  
% 1.13/0.99  fof(f42,plain,(
% 1.13/0.99    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK0(X0)) = X0 & m1_subset_1(sK0(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 1.13/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).
% 1.13/0.99  
% 1.13/0.99  fof(f60,plain,(
% 1.13/0.99    ( ! [X0,X1] : (v1_zfmisc_1(X0) | k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.13/0.99    inference(cnf_transformation,[],[f42])).
% 1.13/0.99  
% 1.13/0.99  fof(f4,axiom,(
% 1.13/0.99    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0)) => ~v1_zfmisc_1(u1_struct_0(X0)))),
% 1.13/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.13/0.99  
% 1.13/0.99  fof(f21,plain,(
% 1.13/0.99    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v7_struct_0(X0)))),
% 1.13/0.99    inference(ennf_transformation,[],[f4])).
% 1.13/0.99  
% 1.13/0.99  fof(f22,plain,(
% 1.13/0.99    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 1.13/0.99    inference(flattening,[],[f21])).
% 1.13/0.99  
% 1.13/0.99  fof(f52,plain,(
% 1.13/0.99    ( ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0)) )),
% 1.13/0.99    inference(cnf_transformation,[],[f22])).
% 1.13/0.99  
% 1.13/0.99  cnf(c_1573,plain,( X0_45 = X0_45 ),theory(equality) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_2028,plain,
% 1.13/0.99      ( k6_domain_1(u1_struct_0(sK1),sK2) = k6_domain_1(u1_struct_0(sK1),sK2) ),
% 1.13/0.99      inference(instantiation,[status(thm)],[c_1573]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_1575,plain,
% 1.13/0.99      ( X0_45 != X1_45 | X2_45 != X1_45 | X2_45 = X0_45 ),
% 1.13/0.99      theory(equality) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_1954,plain,
% 1.13/0.99      ( k6_domain_1(u1_struct_0(sK1),X0_45) != X1_45
% 1.13/0.99      | k6_domain_1(u1_struct_0(sK1),X0_45) = u1_struct_0(sK1)
% 1.13/0.99      | u1_struct_0(sK1) != X1_45 ),
% 1.13/0.99      inference(instantiation,[status(thm)],[c_1575]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_1973,plain,
% 1.13/0.99      ( k6_domain_1(u1_struct_0(sK1),X0_45) != k6_domain_1(u1_struct_0(sK1),sK2)
% 1.13/0.99      | k6_domain_1(u1_struct_0(sK1),X0_45) = u1_struct_0(sK1)
% 1.13/0.99      | u1_struct_0(sK1) != k6_domain_1(u1_struct_0(sK1),sK2) ),
% 1.13/0.99      inference(instantiation,[status(thm)],[c_1954]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_1974,plain,
% 1.13/0.99      ( k6_domain_1(u1_struct_0(sK1),sK2) != k6_domain_1(u1_struct_0(sK1),sK2)
% 1.13/0.99      | k6_domain_1(u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 1.13/0.99      | u1_struct_0(sK1) != k6_domain_1(u1_struct_0(sK1),sK2) ),
% 1.13/0.99      inference(instantiation,[status(thm)],[c_1973]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_20,negated_conjecture,
% 1.13/0.99      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.13/0.99      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
% 1.13/0.99      inference(cnf_transformation,[],[f71]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_176,plain,
% 1.13/0.99      ( v1_tex_2(k1_tex_2(sK1,sK2),sK1)
% 1.13/0.99      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
% 1.13/0.99      inference(prop_impl,[status(thm)],[c_20]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_177,plain,
% 1.13/0.99      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.13/0.99      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
% 1.13/0.99      inference(renaming,[status(thm)],[c_176]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_5,plain,
% 1.13/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.13/0.99      | ~ v1_tex_2(X0,X1)
% 1.13/0.99      | ~ v7_struct_0(X1)
% 1.13/0.99      | v2_struct_0(X1)
% 1.13/0.99      | v2_struct_0(X0)
% 1.13/0.99      | ~ l1_pre_topc(X1) ),
% 1.13/0.99      inference(cnf_transformation,[],[f55]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_14,plain,
% 1.13/0.99      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
% 1.13/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.13/0.99      | v2_struct_0(X0)
% 1.13/0.99      | ~ l1_pre_topc(X0) ),
% 1.13/0.99      inference(cnf_transformation,[],[f64]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_392,plain,
% 1.13/0.99      ( ~ v1_tex_2(X0,X1)
% 1.13/0.99      | ~ m1_subset_1(X2,u1_struct_0(X3))
% 1.13/0.99      | ~ v7_struct_0(X1)
% 1.13/0.99      | v2_struct_0(X0)
% 1.13/0.99      | v2_struct_0(X1)
% 1.13/0.99      | v2_struct_0(X3)
% 1.13/0.99      | ~ l1_pre_topc(X1)
% 1.13/0.99      | ~ l1_pre_topc(X3)
% 1.13/0.99      | X3 != X1
% 1.13/0.99      | k1_tex_2(X3,X2) != X0 ),
% 1.13/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_14]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_393,plain,
% 1.13/0.99      ( ~ v1_tex_2(k1_tex_2(X0,X1),X0)
% 1.13/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.13/0.99      | ~ v7_struct_0(X0)
% 1.13/0.99      | v2_struct_0(X0)
% 1.13/0.99      | v2_struct_0(k1_tex_2(X0,X1))
% 1.13/0.99      | ~ l1_pre_topc(X0) ),
% 1.13/0.99      inference(unflattening,[status(thm)],[c_392]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_15,plain,
% 1.13/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.13/0.99      | v2_struct_0(X1)
% 1.13/0.99      | ~ v2_struct_0(k1_tex_2(X1,X0))
% 1.13/0.99      | ~ l1_pre_topc(X1) ),
% 1.13/0.99      inference(cnf_transformation,[],[f63]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_409,plain,
% 1.13/0.99      ( ~ v1_tex_2(k1_tex_2(X0,X1),X0)
% 1.13/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.13/0.99      | ~ v7_struct_0(X0)
% 1.13/0.99      | v2_struct_0(X0)
% 1.13/0.99      | ~ l1_pre_topc(X0) ),
% 1.13/0.99      inference(forward_subsumption_resolution,
% 1.13/0.99                [status(thm)],
% 1.13/0.99                [c_393,c_15]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_432,plain,
% 1.13/0.99      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.13/0.99      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.13/0.99      | ~ v7_struct_0(X1)
% 1.13/0.99      | v2_struct_0(X1)
% 1.13/0.99      | ~ l1_pre_topc(X1)
% 1.13/0.99      | k1_tex_2(X1,X0) != k1_tex_2(sK1,sK2)
% 1.13/0.99      | sK1 != X1 ),
% 1.13/0.99      inference(resolution_lifted,[status(thm)],[c_177,c_409]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_433,plain,
% 1.13/0.99      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.13/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.13/0.99      | ~ v7_struct_0(sK1)
% 1.13/0.99      | v2_struct_0(sK1)
% 1.13/0.99      | ~ l1_pre_topc(sK1)
% 1.13/0.99      | k1_tex_2(sK1,X0) != k1_tex_2(sK1,sK2) ),
% 1.13/0.99      inference(unflattening,[status(thm)],[c_432]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_23,negated_conjecture,
% 1.13/0.99      ( ~ v2_struct_0(sK1) ),
% 1.13/0.99      inference(cnf_transformation,[],[f68]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_22,negated_conjecture,
% 1.13/0.99      ( l1_pre_topc(sK1) ),
% 1.13/0.99      inference(cnf_transformation,[],[f69]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_437,plain,
% 1.13/0.99      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.13/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.13/0.99      | ~ v7_struct_0(sK1)
% 1.13/0.99      | k1_tex_2(sK1,X0) != k1_tex_2(sK1,sK2) ),
% 1.13/0.99      inference(global_propositional_subsumption,
% 1.13/0.99                [status(thm)],
% 1.13/0.99                [c_433,c_23,c_22]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_1,plain,
% 1.13/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.13/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_18,plain,
% 1.13/0.99      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
% 1.13/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.13/0.99      | ~ v7_struct_0(X0)
% 1.13/0.99      | v2_struct_0(X0)
% 1.13/0.99      | ~ l1_struct_0(X0) ),
% 1.13/0.99      inference(cnf_transformation,[],[f67]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_302,plain,
% 1.13/0.99      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
% 1.13/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.13/0.99      | ~ v7_struct_0(X0)
% 1.13/0.99      | v2_struct_0(X0)
% 1.13/0.99      | ~ l1_pre_topc(X0) ),
% 1.13/0.99      inference(resolution,[status(thm)],[c_1,c_18]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_511,plain,
% 1.13/0.99      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
% 1.13/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.13/0.99      | ~ v7_struct_0(X0)
% 1.13/0.99      | v2_struct_0(X0)
% 1.13/0.99      | sK1 != X0 ),
% 1.13/0.99      inference(resolution_lifted,[status(thm)],[c_302,c_22]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_512,plain,
% 1.13/0.99      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),X0),u1_struct_0(sK1))
% 1.13/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.13/0.99      | ~ v7_struct_0(sK1)
% 1.13/0.99      | v2_struct_0(sK1) ),
% 1.13/0.99      inference(unflattening,[status(thm)],[c_511]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_516,plain,
% 1.13/0.99      ( ~ v7_struct_0(sK1)
% 1.13/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.13/0.99      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),X0),u1_struct_0(sK1)) ),
% 1.13/0.99      inference(global_propositional_subsumption,
% 1.13/0.99                [status(thm)],
% 1.13/0.99                [c_512,c_23]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_517,plain,
% 1.13/0.99      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),X0),u1_struct_0(sK1))
% 1.13/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.13/0.99      | ~ v7_struct_0(sK1) ),
% 1.13/0.99      inference(renaming,[status(thm)],[c_516]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_986,plain,
% 1.13/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.13/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.13/0.99      | ~ v7_struct_0(sK1)
% 1.13/0.99      | k1_tex_2(sK1,X0) != k1_tex_2(sK1,sK2)
% 1.13/0.99      | k6_domain_1(u1_struct_0(sK1),X1) != k6_domain_1(u1_struct_0(sK1),sK2)
% 1.13/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.13/0.99      inference(resolution_lifted,[status(thm)],[c_437,c_517]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_1277,plain,
% 1.13/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.13/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.13/0.99      | ~ v7_struct_0(sK1)
% 1.13/0.99      | k1_tex_2(sK1,X0) != k1_tex_2(sK1,sK2)
% 1.13/0.99      | k6_domain_1(u1_struct_0(sK1),X1) != k6_domain_1(u1_struct_0(sK1),sK2) ),
% 1.13/0.99      inference(equality_resolution_simp,[status(thm)],[c_986]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_1557,plain,
% 1.13/0.99      ( ~ m1_subset_1(X0_45,u1_struct_0(sK1))
% 1.13/0.99      | ~ m1_subset_1(X1_45,u1_struct_0(sK1))
% 1.13/0.99      | ~ v7_struct_0(sK1)
% 1.13/0.99      | k1_tex_2(sK1,X0_45) != k1_tex_2(sK1,sK2)
% 1.13/0.99      | k6_domain_1(u1_struct_0(sK1),X1_45) != k6_domain_1(u1_struct_0(sK1),sK2) ),
% 1.13/0.99      inference(subtyping,[status(esa)],[c_1277]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_1571,plain,
% 1.13/0.99      ( ~ v7_struct_0(sK1) | sP1_iProver_split | sP0_iProver_split ),
% 1.13/0.99      inference(splitting,
% 1.13/0.99                [splitting(split),new_symbols(definition,[])],
% 1.13/0.99                [c_1557]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_21,negated_conjecture,
% 1.13/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.13/0.99      inference(cnf_transformation,[],[f70]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_1583,plain,
% 1.13/0.99      ( X0_46 != X1_46
% 1.13/0.99      | k1_tex_2(X0_46,X0_45) = k1_tex_2(X1_46,X1_45)
% 1.13/0.99      | X0_45 != X1_45 ),
% 1.13/0.99      theory(equality) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_1590,plain,
% 1.13/0.99      ( k1_tex_2(sK1,sK2) = k1_tex_2(sK1,sK2) | sK1 != sK1 | sK2 != sK2 ),
% 1.13/0.99      inference(instantiation,[status(thm)],[c_1583]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_1592,plain,
% 1.13/0.99      ( sK2 = sK2 ),
% 1.13/0.99      inference(instantiation,[status(thm)],[c_1573]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_1574,plain,( X0_46 = X0_46 ),theory(equality) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_1593,plain,
% 1.13/0.99      ( sK1 = sK1 ),
% 1.13/0.99      inference(instantiation,[status(thm)],[c_1574]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_12,plain,
% 1.13/0.99      ( v1_subset_1(X0,X1)
% 1.13/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.13/0.99      | X0 = X1 ),
% 1.13/0.99      inference(cnf_transformation,[],[f62]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_19,negated_conjecture,
% 1.13/0.99      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.13/0.99      | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
% 1.13/0.99      inference(cnf_transformation,[],[f72]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_174,plain,
% 1.13/0.99      ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
% 1.13/0.99      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
% 1.13/0.99      inference(prop_impl,[status(thm)],[c_19]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_175,plain,
% 1.13/0.99      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.13/0.99      | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
% 1.13/0.99      inference(renaming,[status(thm)],[c_174]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_7,plain,
% 1.13/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.13/0.99      | v1_tex_2(X0,X1)
% 1.13/0.99      | ~ v7_struct_0(X0)
% 1.13/0.99      | v7_struct_0(X1)
% 1.13/0.99      | v2_struct_0(X1)
% 1.13/0.99      | v2_struct_0(X0)
% 1.13/0.99      | ~ l1_pre_topc(X1) ),
% 1.13/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_364,plain,
% 1.13/0.99      ( v1_tex_2(X0,X1)
% 1.13/0.99      | ~ m1_subset_1(X2,u1_struct_0(X3))
% 1.13/0.99      | ~ v7_struct_0(X0)
% 1.13/0.99      | v7_struct_0(X1)
% 1.13/0.99      | v2_struct_0(X0)
% 1.13/0.99      | v2_struct_0(X1)
% 1.13/0.99      | v2_struct_0(X3)
% 1.13/0.99      | ~ l1_pre_topc(X1)
% 1.13/0.99      | ~ l1_pre_topc(X3)
% 1.13/0.99      | X3 != X1
% 1.13/0.99      | k1_tex_2(X3,X2) != X0 ),
% 1.13/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_14]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_365,plain,
% 1.13/0.99      ( v1_tex_2(k1_tex_2(X0,X1),X0)
% 1.13/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.13/0.99      | v7_struct_0(X0)
% 1.13/0.99      | ~ v7_struct_0(k1_tex_2(X0,X1))
% 1.13/0.99      | v2_struct_0(X0)
% 1.13/0.99      | v2_struct_0(k1_tex_2(X0,X1))
% 1.13/0.99      | ~ l1_pre_topc(X0) ),
% 1.13/0.99      inference(unflattening,[status(thm)],[c_364]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_16,plain,
% 1.13/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.13/0.99      | v7_struct_0(k1_tex_2(X1,X0))
% 1.13/0.99      | v2_struct_0(X1)
% 1.13/0.99      | ~ l1_pre_topc(X1) ),
% 1.13/0.99      inference(cnf_transformation,[],[f66]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_383,plain,
% 1.13/0.99      ( v1_tex_2(k1_tex_2(X0,X1),X0)
% 1.13/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.13/0.99      | v7_struct_0(X0)
% 1.13/0.99      | v2_struct_0(X0)
% 1.13/0.99      | ~ l1_pre_topc(X0) ),
% 1.13/0.99      inference(forward_subsumption_resolution,
% 1.13/0.99                [status(thm)],
% 1.13/0.99                [c_365,c_15,c_16]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_456,plain,
% 1.13/0.99      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.13/0.99      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.13/0.99      | v7_struct_0(X1)
% 1.13/0.99      | v2_struct_0(X1)
% 1.13/0.99      | ~ l1_pre_topc(X1)
% 1.13/0.99      | k1_tex_2(X1,X0) != k1_tex_2(sK1,sK2)
% 1.13/0.99      | sK1 != X1 ),
% 1.13/0.99      inference(resolution_lifted,[status(thm)],[c_175,c_383]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_457,plain,
% 1.13/0.99      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.13/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.13/0.99      | v7_struct_0(sK1)
% 1.13/0.99      | v2_struct_0(sK1)
% 1.13/0.99      | ~ l1_pre_topc(sK1)
% 1.13/0.99      | k1_tex_2(sK1,X0) != k1_tex_2(sK1,sK2) ),
% 1.13/0.99      inference(unflattening,[status(thm)],[c_456]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_461,plain,
% 1.13/0.99      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.13/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.13/0.99      | v7_struct_0(sK1)
% 1.13/0.99      | k1_tex_2(sK1,X0) != k1_tex_2(sK1,sK2) ),
% 1.13/0.99      inference(global_propositional_subsumption,
% 1.13/0.99                [status(thm)],
% 1.13/0.99                [c_457,c_23,c_22]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_923,plain,
% 1.13/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.13/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.13/0.99      | v7_struct_0(sK1)
% 1.13/0.99      | X1 = X0
% 1.13/0.99      | k1_tex_2(sK1,X2) != k1_tex_2(sK1,sK2)
% 1.13/0.99      | k6_domain_1(u1_struct_0(sK1),sK2) != X0
% 1.13/0.99      | u1_struct_0(sK1) != X1 ),
% 1.13/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_461]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_924,plain,
% 1.13/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.13/0.99      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.13/0.99      | v7_struct_0(sK1)
% 1.13/0.99      | k1_tex_2(sK1,X0) != k1_tex_2(sK1,sK2)
% 1.13/0.99      | u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK1),sK2) ),
% 1.13/0.99      inference(unflattening,[status(thm)],[c_923]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_1560,plain,
% 1.13/0.99      ( ~ m1_subset_1(X0_45,u1_struct_0(sK1))
% 1.13/0.99      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.13/0.99      | v7_struct_0(sK1)
% 1.13/0.99      | k1_tex_2(sK1,X0_45) != k1_tex_2(sK1,sK2)
% 1.13/0.99      | u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK1),sK2) ),
% 1.13/0.99      inference(subtyping,[status(esa)],[c_924]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_1567,plain,
% 1.13/0.99      ( ~ m1_subset_1(X0_45,u1_struct_0(sK1))
% 1.13/0.99      | k1_tex_2(sK1,X0_45) != k1_tex_2(sK1,sK2)
% 1.13/0.99      | ~ sP0_iProver_split ),
% 1.13/0.99      inference(splitting,
% 1.13/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.13/0.99                [c_1560]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_1612,plain,
% 1.13/0.99      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.13/0.99      | ~ sP0_iProver_split
% 1.13/0.99      | k1_tex_2(sK1,sK2) != k1_tex_2(sK1,sK2) ),
% 1.13/0.99      inference(instantiation,[status(thm)],[c_1567]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_1668,plain,
% 1.13/0.99      ( sP1_iProver_split | ~ v7_struct_0(sK1) ),
% 1.13/0.99      inference(global_propositional_subsumption,
% 1.13/0.99                [status(thm)],
% 1.13/0.99                [c_1571,c_21,c_1590,c_1592,c_1593,c_1612]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_1669,plain,
% 1.13/0.99      ( ~ v7_struct_0(sK1) | sP1_iProver_split ),
% 1.13/0.99      inference(renaming,[status(thm)],[c_1668]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_1568,plain,
% 1.13/0.99      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.13/0.99      | v7_struct_0(sK1)
% 1.13/0.99      | sP0_iProver_split
% 1.13/0.99      | u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK1),sK2) ),
% 1.13/0.99      inference(splitting,
% 1.13/0.99                [splitting(split),new_symbols(definition,[])],
% 1.13/0.99                [c_1560]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_26,plain,
% 1.13/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 1.13/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_4,plain,
% 1.13/0.99      ( ~ m1_subset_1(X0,X1)
% 1.13/0.99      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 1.13/0.99      | v1_xboole_0(X1) ),
% 1.13/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_2,plain,
% 1.13/0.99      ( v2_struct_0(X0)
% 1.13/0.99      | ~ l1_struct_0(X0)
% 1.13/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.13/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_336,plain,
% 1.13/0.99      ( v2_struct_0(X0)
% 1.13/0.99      | ~ l1_pre_topc(X0)
% 1.13/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.13/0.99      inference(resolution,[status(thm)],[c_1,c_2]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_490,plain,
% 1.13/0.99      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK1 != X0 ),
% 1.13/0.99      inference(resolution_lifted,[status(thm)],[c_336,c_22]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_491,plain,
% 1.13/0.99      ( v2_struct_0(sK1) | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 1.13/0.99      inference(unflattening,[status(thm)],[c_490]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_70,plain,
% 1.13/0.99      ( v2_struct_0(sK1)
% 1.13/0.99      | ~ l1_struct_0(sK1)
% 1.13/0.99      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 1.13/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_73,plain,
% 1.13/0.99      ( ~ l1_pre_topc(sK1) | l1_struct_0(sK1) ),
% 1.13/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_493,plain,
% 1.13/0.99      ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 1.13/0.99      inference(global_propositional_subsumption,
% 1.13/0.99                [status(thm)],
% 1.13/0.99                [c_491,c_23,c_22,c_70,c_73]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_712,plain,
% 1.13/0.99      ( ~ m1_subset_1(X0,X1)
% 1.13/0.99      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 1.13/0.99      | u1_struct_0(sK1) != X1 ),
% 1.13/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_493]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_713,plain,
% 1.13/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.13/0.99      | m1_subset_1(k6_domain_1(u1_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.13/0.99      inference(unflattening,[status(thm)],[c_712]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_1563,plain,
% 1.13/0.99      ( ~ m1_subset_1(X0_45,u1_struct_0(sK1))
% 1.13/0.99      | m1_subset_1(k6_domain_1(u1_struct_0(sK1),X0_45),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.13/0.99      inference(subtyping,[status(esa)],[c_713]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_1601,plain,
% 1.13/0.99      ( m1_subset_1(X0_45,u1_struct_0(sK1)) != iProver_top
% 1.13/0.99      | m1_subset_1(k6_domain_1(u1_struct_0(sK1),X0_45),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.13/0.99      inference(predicate_to_equality,[status(thm)],[c_1563]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_1603,plain,
% 1.13/0.99      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 1.13/0.99      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
% 1.13/0.99      inference(instantiation,[status(thm)],[c_1601]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_1610,plain,
% 1.13/0.99      ( u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK1),sK2)
% 1.13/0.99      | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.13/0.99      | v7_struct_0(sK1) = iProver_top
% 1.13/0.99      | sP0_iProver_split = iProver_top ),
% 1.13/0.99      inference(predicate_to_equality,[status(thm)],[c_1568]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_1611,plain,
% 1.13/0.99      ( k1_tex_2(sK1,X0_45) != k1_tex_2(sK1,sK2)
% 1.13/0.99      | m1_subset_1(X0_45,u1_struct_0(sK1)) != iProver_top
% 1.13/0.99      | sP0_iProver_split != iProver_top ),
% 1.13/0.99      inference(predicate_to_equality,[status(thm)],[c_1567]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_1613,plain,
% 1.13/0.99      ( k1_tex_2(sK1,sK2) != k1_tex_2(sK1,sK2)
% 1.13/0.99      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 1.13/0.99      | sP0_iProver_split != iProver_top ),
% 1.13/0.99      inference(instantiation,[status(thm)],[c_1611]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_944,plain,
% 1.13/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.13/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.13/0.99      | ~ v7_struct_0(sK1)
% 1.13/0.99      | X1 = X0
% 1.13/0.99      | k6_domain_1(u1_struct_0(sK1),X2) != X0
% 1.13/0.99      | u1_struct_0(sK1) != X1 ),
% 1.13/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_517]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_945,plain,
% 1.13/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.13/0.99      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.13/0.99      | ~ v7_struct_0(sK1)
% 1.13/0.99      | u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK1),X0) ),
% 1.13/0.99      inference(unflattening,[status(thm)],[c_944]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_949,plain,
% 1.13/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.13/0.99      | ~ v7_struct_0(sK1)
% 1.13/0.99      | u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK1),X0) ),
% 1.13/0.99      inference(global_propositional_subsumption,
% 1.13/0.99                [status(thm)],
% 1.13/0.99                [c_945,c_713]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_1559,plain,
% 1.13/0.99      ( ~ m1_subset_1(X0_45,u1_struct_0(sK1))
% 1.13/0.99      | ~ v7_struct_0(sK1)
% 1.13/0.99      | u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK1),X0_45) ),
% 1.13/0.99      inference(subtyping,[status(esa)],[c_949]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_1614,plain,
% 1.13/0.99      ( u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK1),X0_45)
% 1.13/0.99      | m1_subset_1(X0_45,u1_struct_0(sK1)) != iProver_top
% 1.13/0.99      | v7_struct_0(sK1) != iProver_top ),
% 1.13/0.99      inference(predicate_to_equality,[status(thm)],[c_1559]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_1616,plain,
% 1.13/0.99      ( u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK1),sK2)
% 1.13/0.99      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 1.13/0.99      | v7_struct_0(sK1) != iProver_top ),
% 1.13/0.99      inference(instantiation,[status(thm)],[c_1614]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_1649,plain,
% 1.13/0.99      ( u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK1),sK2) ),
% 1.13/0.99      inference(global_propositional_subsumption,
% 1.13/0.99                [status(thm)],
% 1.13/0.99                [c_1568,c_26,c_1590,c_1592,c_1593,c_1603,c_1610,c_1613,
% 1.13/0.99                 c_1616]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_1570,plain,
% 1.13/0.99      ( ~ m1_subset_1(X0_45,u1_struct_0(sK1))
% 1.13/0.99      | k6_domain_1(u1_struct_0(sK1),X0_45) != k6_domain_1(u1_struct_0(sK1),sK2)
% 1.13/0.99      | ~ sP1_iProver_split ),
% 1.13/0.99      inference(splitting,
% 1.13/0.99                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 1.13/0.99                [c_1557]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_1622,plain,
% 1.13/0.99      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.13/0.99      | ~ sP1_iProver_split
% 1.13/0.99      | k6_domain_1(u1_struct_0(sK1),sK2) != k6_domain_1(u1_struct_0(sK1),sK2) ),
% 1.13/0.99      inference(instantiation,[status(thm)],[c_1570]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_0,plain,
% 1.13/0.99      ( ~ v1_xboole_0(X0) | v1_zfmisc_1(X0) ),
% 1.13/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_9,plain,
% 1.13/0.99      ( ~ m1_subset_1(X0,X1)
% 1.13/0.99      | v1_xboole_0(X1)
% 1.13/0.99      | v1_zfmisc_1(X1)
% 1.13/0.99      | k6_domain_1(X1,X0) != X1 ),
% 1.13/0.99      inference(cnf_transformation,[],[f60]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_657,plain,
% 1.13/0.99      ( ~ m1_subset_1(X0,X1)
% 1.13/0.99      | v1_zfmisc_1(X2)
% 1.13/0.99      | v1_zfmisc_1(X1)
% 1.13/0.99      | X1 != X2
% 1.13/0.99      | k6_domain_1(X1,X0) != X1 ),
% 1.13/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_9]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_658,plain,
% 1.13/0.99      ( ~ m1_subset_1(X0,X1)
% 1.13/0.99      | v1_zfmisc_1(X1)
% 1.13/0.99      | k6_domain_1(X1,X0) != X1 ),
% 1.13/0.99      inference(unflattening,[status(thm)],[c_657]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_3,plain,
% 1.13/0.99      ( v7_struct_0(X0)
% 1.13/0.99      | ~ l1_struct_0(X0)
% 1.13/0.99      | ~ v1_zfmisc_1(u1_struct_0(X0)) ),
% 1.13/0.99      inference(cnf_transformation,[],[f52]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_322,plain,
% 1.13/0.99      ( v7_struct_0(X0)
% 1.13/0.99      | ~ l1_pre_topc(X0)
% 1.13/0.99      | ~ v1_zfmisc_1(u1_struct_0(X0)) ),
% 1.13/0.99      inference(resolution,[status(thm)],[c_1,c_3]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_501,plain,
% 1.13/0.99      ( v7_struct_0(X0) | ~ v1_zfmisc_1(u1_struct_0(X0)) | sK1 != X0 ),
% 1.13/0.99      inference(resolution_lifted,[status(thm)],[c_322,c_22]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_502,plain,
% 1.13/0.99      ( v7_struct_0(sK1) | ~ v1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.13/0.99      inference(unflattening,[status(thm)],[c_501]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_777,plain,
% 1.13/0.99      ( ~ m1_subset_1(X0,X1)
% 1.13/0.99      | v7_struct_0(sK1)
% 1.13/0.99      | k6_domain_1(X1,X0) != X1
% 1.13/0.99      | u1_struct_0(sK1) != X1 ),
% 1.13/0.99      inference(resolution_lifted,[status(thm)],[c_658,c_502]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_778,plain,
% 1.13/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.13/0.99      | v7_struct_0(sK1)
% 1.13/0.99      | k6_domain_1(u1_struct_0(sK1),X0) != u1_struct_0(sK1) ),
% 1.13/0.99      inference(unflattening,[status(thm)],[c_777]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_1564,plain,
% 1.13/0.99      ( ~ m1_subset_1(X0_45,u1_struct_0(sK1))
% 1.13/0.99      | v7_struct_0(sK1)
% 1.13/0.99      | k6_domain_1(u1_struct_0(sK1),X0_45) != u1_struct_0(sK1) ),
% 1.13/0.99      inference(subtyping,[status(esa)],[c_778]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(c_1599,plain,
% 1.13/0.99      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.13/0.99      | v7_struct_0(sK1)
% 1.13/0.99      | k6_domain_1(u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 1.13/0.99      inference(instantiation,[status(thm)],[c_1564]) ).
% 1.13/0.99  
% 1.13/0.99  cnf(contradiction,plain,
% 1.13/0.99      ( $false ),
% 1.13/0.99      inference(minisat,
% 1.13/0.99                [status(thm)],
% 1.13/0.99                [c_2028,c_1974,c_1669,c_1649,c_1622,c_1599,c_21]) ).
% 1.13/0.99  
% 1.13/0.99  
% 1.13/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.13/0.99  
% 1.13/0.99  ------                               Statistics
% 1.13/0.99  
% 1.13/0.99  ------ General
% 1.13/0.99  
% 1.13/0.99  abstr_ref_over_cycles:                  0
% 1.13/0.99  abstr_ref_under_cycles:                 0
% 1.13/0.99  gc_basic_clause_elim:                   0
% 1.13/0.99  forced_gc_time:                         0
% 1.13/0.99  parsing_time:                           0.014
% 1.13/0.99  unif_index_cands_time:                  0.
% 1.13/0.99  unif_index_add_time:                    0.
% 1.13/0.99  orderings_time:                         0.
% 1.13/0.99  out_proof_time:                         0.014
% 1.13/0.99  total_time:                             0.092
% 1.13/0.99  num_of_symbols:                         52
% 1.13/0.99  num_of_terms:                           976
% 1.13/0.99  
% 1.13/0.99  ------ Preprocessing
% 1.13/0.99  
% 1.13/0.99  num_of_splits:                          4
% 1.13/0.99  num_of_split_atoms:                     2
% 1.13/0.99  num_of_reused_defs:                     2
% 1.13/0.99  num_eq_ax_congr_red:                    4
% 1.13/0.99  num_of_sem_filtered_clauses:            2
% 1.13/0.99  num_of_subtypes:                        2
% 1.13/0.99  monotx_restored_types:                  0
% 1.13/0.99  sat_num_of_epr_types:                   0
% 1.13/0.99  sat_num_of_non_cyclic_types:            0
% 1.13/0.99  sat_guarded_non_collapsed_types:        0
% 1.13/0.99  num_pure_diseq_elim:                    0
% 1.13/0.99  simp_replaced_by:                       0
% 1.13/0.99  res_preprocessed:                       77
% 1.13/0.99  prep_upred:                             0
% 1.13/0.99  prep_unflattend:                        34
% 1.13/0.99  smt_new_axioms:                         0
% 1.13/0.99  pred_elim_cands:                        2
% 1.13/0.99  pred_elim:                              8
% 1.13/0.99  pred_elim_cl:                           11
% 1.13/0.99  pred_elim_cycles:                       12
% 1.13/0.99  merged_defs:                            2
% 1.13/0.99  merged_defs_ncl:                        0
% 1.13/0.99  bin_hyper_res:                          2
% 1.13/0.99  prep_cycles:                            4
% 1.13/0.99  pred_elim_time:                         0.023
% 1.13/0.99  splitting_time:                         0.
% 1.13/0.99  sem_filter_time:                        0.
% 1.13/0.99  monotx_time:                            0.
% 1.13/0.99  subtype_inf_time:                       0.
% 1.13/0.99  
% 1.13/0.99  ------ Problem properties
% 1.13/0.99  
% 1.13/0.99  clauses:                                14
% 1.13/0.99  conjectures:                            1
% 1.13/0.99  epr:                                    1
% 1.13/0.99  horn:                                   12
% 1.13/0.99  ground:                                 4
% 1.13/0.99  unary:                                  1
% 1.13/0.99  binary:                                 2
% 1.13/0.99  lits:                                   40
% 1.13/0.99  lits_eq:                                11
% 1.13/0.99  fd_pure:                                0
% 1.13/0.99  fd_pseudo:                              0
% 1.13/0.99  fd_cond:                                0
% 1.13/0.99  fd_pseudo_cond:                         0
% 1.13/0.99  ac_symbols:                             0
% 1.13/0.99  
% 1.13/0.99  ------ Propositional Solver
% 1.13/0.99  
% 1.13/0.99  prop_solver_calls:                      24
% 1.13/0.99  prop_fast_solver_calls:                 690
% 1.13/0.99  smt_solver_calls:                       0
% 1.13/0.99  smt_fast_solver_calls:                  0
% 1.13/0.99  prop_num_of_clauses:                    400
% 1.13/0.99  prop_preprocess_simplified:             2248
% 1.13/0.99  prop_fo_subsumed:                       22
% 1.13/0.99  prop_solver_time:                       0.
% 1.13/0.99  smt_solver_time:                        0.
% 1.13/0.99  smt_fast_solver_time:                   0.
% 1.13/0.99  prop_fast_solver_time:                  0.
% 1.13/0.99  prop_unsat_core_time:                   0.
% 1.13/0.99  
% 1.13/0.99  ------ QBF
% 1.13/0.99  
% 1.13/0.99  qbf_q_res:                              0
% 1.13/0.99  qbf_num_tautologies:                    0
% 1.13/0.99  qbf_prep_cycles:                        0
% 1.13/0.99  
% 1.13/0.99  ------ BMC1
% 1.13/0.99  
% 1.13/0.99  bmc1_current_bound:                     -1
% 1.13/0.99  bmc1_last_solved_bound:                 -1
% 1.13/0.99  bmc1_unsat_core_size:                   -1
% 1.13/0.99  bmc1_unsat_core_parents_size:           -1
% 1.13/0.99  bmc1_merge_next_fun:                    0
% 1.13/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.13/0.99  
% 1.13/0.99  ------ Instantiation
% 1.13/0.99  
% 1.13/0.99  inst_num_of_clauses:                    49
% 1.13/0.99  inst_num_in_passive:                    15
% 1.13/0.99  inst_num_in_active:                     31
% 1.13/0.99  inst_num_in_unprocessed:                2
% 1.13/0.99  inst_num_of_loops:                      34
% 1.13/0.99  inst_num_of_learning_restarts:          0
% 1.13/0.99  inst_num_moves_active_passive:          0
% 1.13/0.99  inst_lit_activity:                      0
% 1.13/0.99  inst_lit_activity_moves:                0
% 1.13/0.99  inst_num_tautologies:                   0
% 1.13/0.99  inst_num_prop_implied:                  0
% 1.13/0.99  inst_num_existing_simplified:           0
% 1.13/0.99  inst_num_eq_res_simplified:             0
% 1.13/0.99  inst_num_child_elim:                    0
% 1.13/0.99  inst_num_of_dismatching_blockings:      0
% 1.13/0.99  inst_num_of_non_proper_insts:           18
% 1.13/0.99  inst_num_of_duplicates:                 0
% 1.13/0.99  inst_inst_num_from_inst_to_res:         0
% 1.13/0.99  inst_dismatching_checking_time:         0.
% 1.13/0.99  
% 1.13/0.99  ------ Resolution
% 1.13/0.99  
% 1.13/0.99  res_num_of_clauses:                     0
% 1.13/0.99  res_num_in_passive:                     0
% 1.13/0.99  res_num_in_active:                      0
% 1.13/0.99  res_num_of_loops:                       81
% 1.13/0.99  res_forward_subset_subsumed:            7
% 1.13/0.99  res_backward_subset_subsumed:           0
% 1.13/0.99  res_forward_subsumed:                   1
% 1.13/0.99  res_backward_subsumed:                  0
% 1.13/0.99  res_forward_subsumption_resolution:     3
% 1.13/0.99  res_backward_subsumption_resolution:    0
% 1.13/0.99  res_clause_to_clause_subsumption:       66
% 1.13/0.99  res_orphan_elimination:                 0
% 1.13/0.99  res_tautology_del:                      23
% 1.13/0.99  res_num_eq_res_simplified:              1
% 1.13/0.99  res_num_sel_changes:                    0
% 1.13/0.99  res_moves_from_active_to_pass:          0
% 1.13/0.99  
% 1.13/0.99  ------ Superposition
% 1.13/0.99  
% 1.13/0.99  sup_time_total:                         0.
% 1.13/0.99  sup_time_generating:                    0.
% 1.13/0.99  sup_time_sim_full:                      0.
% 1.13/0.99  sup_time_sim_immed:                     0.
% 1.13/0.99  
% 1.13/0.99  sup_num_of_clauses:                     14
% 1.13/0.99  sup_num_in_active:                      6
% 1.13/0.99  sup_num_in_passive:                     8
% 1.13/0.99  sup_num_of_loops:                       6
% 1.13/0.99  sup_fw_superposition:                   2
% 1.13/0.99  sup_bw_superposition:                   0
% 1.13/0.99  sup_immediate_simplified:               0
% 1.13/0.99  sup_given_eliminated:                   0
% 1.13/0.99  comparisons_done:                       0
% 1.13/0.99  comparisons_avoided:                    0
% 1.13/0.99  
% 1.13/0.99  ------ Simplifications
% 1.13/0.99  
% 1.13/0.99  
% 1.13/0.99  sim_fw_subset_subsumed:                 0
% 1.13/0.99  sim_bw_subset_subsumed:                 0
% 1.13/0.99  sim_fw_subsumed:                        0
% 1.13/0.99  sim_bw_subsumed:                        0
% 1.13/0.99  sim_fw_subsumption_res:                 0
% 1.13/0.99  sim_bw_subsumption_res:                 0
% 1.13/0.99  sim_tautology_del:                      0
% 1.13/0.99  sim_eq_tautology_del:                   0
% 1.13/0.99  sim_eq_res_simp:                        0
% 1.13/0.99  sim_fw_demodulated:                     0
% 1.13/0.99  sim_bw_demodulated:                     0
% 1.13/0.99  sim_light_normalised:                   0
% 1.13/0.99  sim_joinable_taut:                      0
% 1.13/0.99  sim_joinable_simp:                      0
% 1.13/0.99  sim_ac_normalised:                      0
% 1.13/0.99  sim_smt_subsumption:                    0
% 1.13/0.99  
%------------------------------------------------------------------------------
