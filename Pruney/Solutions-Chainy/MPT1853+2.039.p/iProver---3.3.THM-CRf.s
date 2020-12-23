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
% DateTime   : Thu Dec  3 12:25:42 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :  233 ( 787 expanded)
%              Number of clauses        :  151 ( 262 expanded)
%              Number of leaves         :   25 ( 159 expanded)
%              Depth                    :   17
%              Number of atoms          :  832 (3634 expanded)
%              Number of equality atoms :  242 ( 351 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

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
    inference(nnf_transformation,[],[f47])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f56,plain,(
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

fof(f55,plain,
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

fof(f57,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
      | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) )
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f54,f56,f55])).

fof(f82,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f57])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f64,f58])).

fof(f80,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f81,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f60,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f83,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f16,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f59,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f84,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
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
    inference(pure_predicate_removal,[],[f12])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ~ ( v1_tex_2(X1,X0)
              & u1_struct_0(X0) = u1_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_tex_2(X1,X0)
          | u1_struct_0(X0) != u1_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_tex_2(X1,X0)
          | u1_struct_0(X0) != u1_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_tex_2(X1,X0)
      | u1_struct_0(X0) != u1_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f77,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f61,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK0(X0,X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
                & u1_struct_0(X1) = sK0(X0,X1)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f49,f50])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK0(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f63,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v7_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

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

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_4853,plain,
    ( X0_47 != X1_47
    | X2_47 != X1_47
    | X2_47 = X0_47 ),
    theory(equality)).

cnf(c_6049,plain,
    ( X0_47 != X1_47
    | u1_struct_0(k1_tex_2(X0_48,X2_47)) != X1_47
    | u1_struct_0(k1_tex_2(X0_48,X2_47)) = X0_47 ),
    inference(instantiation,[status(thm)],[c_4853])).

cnf(c_6750,plain,
    ( X0_47 != u1_struct_0(k1_tex_2(sK1,sK2))
    | u1_struct_0(k1_tex_2(X0_48,X1_47)) = X0_47
    | u1_struct_0(k1_tex_2(X0_48,X1_47)) != u1_struct_0(k1_tex_2(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_6049])).

cnf(c_7153,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) != u1_struct_0(k1_tex_2(sK1,sK2))
    | u1_struct_0(k1_tex_2(X0_48,X0_47)) = sK0(sK1,k1_tex_2(sK1,sK2))
    | u1_struct_0(k1_tex_2(X0_48,X0_47)) != u1_struct_0(k1_tex_2(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_6750])).

cnf(c_7154,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) != u1_struct_0(k1_tex_2(sK1,sK2))
    | u1_struct_0(k1_tex_2(sK1,sK2)) = sK0(sK1,k1_tex_2(sK1,sK2))
    | u1_struct_0(k1_tex_2(sK1,sK2)) != u1_struct_0(k1_tex_2(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_7153])).

cnf(c_5777,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK2)) != X0_47
    | u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
    | u1_struct_0(sK1) != X0_47 ),
    inference(instantiation,[status(thm)],[c_4853])).

cnf(c_7069,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK2)) != sK0(sK1,k1_tex_2(sK1,X0_47))
    | u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
    | u1_struct_0(sK1) != sK0(sK1,k1_tex_2(sK1,X0_47)) ),
    inference(instantiation,[status(thm)],[c_5777])).

cnf(c_7070,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK2)) != sK0(sK1,k1_tex_2(sK1,sK2))
    | u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
    | u1_struct_0(sK1) != sK0(sK1,k1_tex_2(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_7069])).

cnf(c_5826,plain,
    ( X0_47 != X1_47
    | X0_47 = u1_struct_0(k1_tex_2(X0_48,X2_47))
    | u1_struct_0(k1_tex_2(X0_48,X2_47)) != X1_47 ),
    inference(instantiation,[status(thm)],[c_4853])).

cnf(c_6037,plain,
    ( X0_47 != u1_struct_0(X0_48)
    | X0_47 = u1_struct_0(k1_tex_2(X1_48,X1_47))
    | u1_struct_0(k1_tex_2(X1_48,X1_47)) != u1_struct_0(X0_48) ),
    inference(instantiation,[status(thm)],[c_5826])).

cnf(c_6699,plain,
    ( u1_struct_0(X0_48) != u1_struct_0(X1_48)
    | u1_struct_0(X0_48) = u1_struct_0(k1_tex_2(X2_48,X0_47))
    | u1_struct_0(k1_tex_2(X2_48,X0_47)) != u1_struct_0(X1_48) ),
    inference(instantiation,[status(thm)],[c_6037])).

cnf(c_6700,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK2)) != u1_struct_0(sK1)
    | u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK1,sK2))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_6699])).

cnf(c_5894,plain,
    ( X0_47 != X1_47
    | u1_struct_0(sK1) != X1_47
    | u1_struct_0(sK1) = X0_47 ),
    inference(instantiation,[status(thm)],[c_4853])).

cnf(c_6154,plain,
    ( X0_47 != u1_struct_0(sK1)
    | u1_struct_0(sK1) = X0_47
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_5894])).

cnf(c_6526,plain,
    ( sK0(sK1,k1_tex_2(sK1,X0_47)) != u1_struct_0(sK1)
    | u1_struct_0(sK1) = sK0(sK1,k1_tex_2(sK1,X0_47))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_6154])).

cnf(c_6527,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) != u1_struct_0(sK1)
    | u1_struct_0(sK1) = sK0(sK1,k1_tex_2(sK1,sK2))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_6526])).

cnf(c_11,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_4842,plain,
    ( v1_subset_1(X0_47,X1_47)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(X1_47))
    | X0_47 = X1_47 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_5793,plain,
    ( v1_subset_1(X0_47,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK1)))
    | X0_47 = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_4842])).

cnf(c_6308,plain,
    ( v1_subset_1(sK0(sK1,k1_tex_2(sK1,X0_47)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK0(sK1,k1_tex_2(sK1,X0_47)),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK0(sK1,k1_tex_2(sK1,X0_47)) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_5793])).

cnf(c_6312,plain,
    ( v1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_6308])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_4834,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_5495,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4834])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_4847,plain,
    ( ~ m1_subset_1(X0_47,X1_47)
    | v1_xboole_0(X1_47)
    | k6_domain_1(X1_47,X0_47) = k2_tarski(X0_47,X0_47) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_5482,plain,
    ( k6_domain_1(X0_47,X1_47) = k2_tarski(X1_47,X1_47)
    | m1_subset_1(X1_47,X0_47) != iProver_top
    | v1_xboole_0(X0_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4847])).

cnf(c_5855,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2)
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5495,c_5482])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_81,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_85,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_5707,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_4847])).

cnf(c_6017,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5855,c_25,c_24,c_23,c_81,c_85,c_5707])).

cnf(c_22,negated_conjecture,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_4835,negated_conjecture,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_5494,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4835])).

cnf(c_6020,plain,
    ( v1_subset_1(k2_tarski(sK2,sK2),u1_struct_0(sK1)) = iProver_top
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6017,c_5494])).

cnf(c_26,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_27,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_28,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_80,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_82,plain,
    ( v2_struct_0(sK1) = iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_80])).

cnf(c_84,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_86,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_struct_0(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_84])).

cnf(c_20,plain,
    ( v1_subset_1(k6_domain_1(X0,X1),X0)
    | ~ m1_subset_1(X1,X0)
    | v1_xboole_0(X0)
    | v1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | v1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_148,plain,
    ( ~ m1_subset_1(X1,X0)
    | v1_subset_1(k6_domain_1(X0,X1),X0)
    | v1_zfmisc_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_0])).

cnf(c_149,plain,
    ( v1_subset_1(k6_domain_1(X0,X1),X0)
    | ~ m1_subset_1(X1,X0)
    | v1_zfmisc_1(X0) ),
    inference(renaming,[status(thm)],[c_148])).

cnf(c_21,negated_conjecture,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1901,plain,
    ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
    inference(prop_impl,[status(thm)],[c_21])).

cnf(c_1902,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(renaming,[status(thm)],[c_1901])).

cnf(c_2838,plain,
    ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
    | ~ m1_subset_1(X0,X1)
    | v1_zfmisc_1(X1)
    | k6_domain_1(u1_struct_0(sK1),sK2) != k6_domain_1(X1,X0)
    | u1_struct_0(sK1) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_149,c_1902])).

cnf(c_2839,plain,
    ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v1_zfmisc_1(u1_struct_0(sK1))
    | k6_domain_1(u1_struct_0(sK1),sK2) != k6_domain_1(u1_struct_0(sK1),X0) ),
    inference(unflattening,[status(thm)],[c_2838])).

cnf(c_1432,plain,
    ( v1_subset_1(k6_domain_1(X0,X1),X0)
    | v1_zfmisc_1(X0)
    | u1_struct_0(sK1) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_149,c_23])).

cnf(c_1433,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_1432])).

cnf(c_2841,plain,
    ( v1_zfmisc_1(u1_struct_0(sK1))
    | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2839,c_21,c_1433])).

cnf(c_2842,plain,
    ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
    | v1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_2841])).

cnf(c_2843,plain,
    ( v1_tex_2(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2842])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_pre_topc(k1_tex_2(X1,X0),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_4840,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(X0_48))
    | m1_pre_topc(k1_tex_2(X0_48,X0_47),X0_48)
    | v2_struct_0(X0_48)
    | ~ l1_pre_topc(X0_48) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_4898,plain,
    ( m1_subset_1(X0_47,u1_struct_0(X0_48)) != iProver_top
    | m1_pre_topc(k1_tex_2(X0_48,X0_47),X0_48) = iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | l1_pre_topc(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4840])).

cnf(c_4900,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4898])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_4839,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(X0_48))
    | v2_struct_0(X0_48)
    | ~ v2_struct_0(k1_tex_2(X0_48,X0_47))
    | ~ l1_pre_topc(X0_48) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_4901,plain,
    ( m1_subset_1(X0_47,u1_struct_0(X0_48)) != iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | v2_struct_0(k1_tex_2(X0_48,X0_47)) != iProver_top
    | l1_pre_topc(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4839])).

cnf(c_4903,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4901])).

cnf(c_17,plain,
    ( ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_4838,plain,
    ( ~ v1_tex_2(X0_48,X1_48)
    | ~ m1_pre_topc(X0_48,X1_48)
    | ~ l1_pre_topc(X1_48)
    | u1_struct_0(X0_48) != u1_struct_0(X1_48) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_5704,plain,
    ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
    | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(k1_tex_2(sK1,sK2)) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_4838])).

cnf(c_5705,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK2)) != u1_struct_0(sK1)
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5704])).

cnf(c_6,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_441,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_zfmisc_1(X3)
    | X3 = X2
    | u1_struct_0(X0) != X2
    | u1_struct_0(X1) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_18])).

cnf(c_442,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(X0))
    | v1_xboole_0(u1_struct_0(X1))
    | ~ v1_zfmisc_1(u1_struct_0(X1))
    | u1_struct_0(X1) = u1_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_441])).

cnf(c_4829,plain,
    ( ~ m1_pre_topc(X0_48,X1_48)
    | ~ l1_pre_topc(X1_48)
    | v1_xboole_0(u1_struct_0(X0_48))
    | v1_xboole_0(u1_struct_0(X1_48))
    | ~ v1_zfmisc_1(u1_struct_0(X1_48))
    | u1_struct_0(X1_48) = u1_struct_0(X0_48) ),
    inference(subtyping,[status(esa)],[c_442])).

cnf(c_5810,plain,
    ( ~ m1_pre_topc(k1_tex_2(X0_48,X0_47),X1_48)
    | ~ l1_pre_topc(X1_48)
    | v1_xboole_0(u1_struct_0(X1_48))
    | v1_xboole_0(u1_struct_0(k1_tex_2(X0_48,X0_47)))
    | ~ v1_zfmisc_1(u1_struct_0(X1_48))
    | u1_struct_0(X1_48) = u1_struct_0(k1_tex_2(X0_48,X0_47)) ),
    inference(instantiation,[status(thm)],[c_4829])).

cnf(c_5815,plain,
    ( u1_struct_0(X0_48) = u1_struct_0(k1_tex_2(X1_48,X0_47))
    | m1_pre_topc(k1_tex_2(X1_48,X0_47),X0_48) != iProver_top
    | l1_pre_topc(X0_48) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_48)) = iProver_top
    | v1_xboole_0(u1_struct_0(k1_tex_2(X1_48,X0_47))) = iProver_top
    | v1_zfmisc_1(u1_struct_0(X0_48)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5810])).

cnf(c_5817,plain,
    ( u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK1,sK2))
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK1,sK2))) = iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top
    | v1_zfmisc_1(u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5815])).

cnf(c_393,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_1,c_3])).

cnf(c_4830,plain,
    ( v2_struct_0(X0_48)
    | ~ l1_pre_topc(X0_48)
    | ~ v1_xboole_0(u1_struct_0(X0_48)) ),
    inference(subtyping,[status(esa)],[c_393])).

cnf(c_5857,plain,
    ( v2_struct_0(k1_tex_2(sK1,sK2))
    | ~ l1_pre_topc(k1_tex_2(sK1,sK2))
    | ~ v1_xboole_0(u1_struct_0(k1_tex_2(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_4830])).

cnf(c_5858,plain,
    ( v2_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
    | l1_pre_topc(k1_tex_2(sK1,sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5857])).

cnf(c_5489,plain,
    ( m1_subset_1(X0_47,u1_struct_0(X0_48)) != iProver_top
    | m1_pre_topc(k1_tex_2(X0_48,X0_47),X0_48) = iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | l1_pre_topc(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4840])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_4848,plain,
    ( ~ m1_pre_topc(X0_48,X1_48)
    | ~ l1_pre_topc(X1_48)
    | l1_pre_topc(X0_48) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_5481,plain,
    ( m1_pre_topc(X0_48,X1_48) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4848])).

cnf(c_5914,plain,
    ( m1_subset_1(X0_47,u1_struct_0(X0_48)) != iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | l1_pre_topc(X0_48) != iProver_top
    | l1_pre_topc(k1_tex_2(X0_48,X0_47)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5489,c_5481])).

cnf(c_5935,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(k1_tex_2(sK1,sK2)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5914])).

cnf(c_5883,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK2)) != u1_struct_0(X0_48)
    | u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
    | u1_struct_0(sK1) != u1_struct_0(X0_48) ),
    inference(instantiation,[status(thm)],[c_5777])).

cnf(c_6095,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK2)) != u1_struct_0(k1_tex_2(sK1,sK2))
    | u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
    | u1_struct_0(sK1) != u1_struct_0(k1_tex_2(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_5883])).

cnf(c_4851,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_6096,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_4851])).

cnf(c_6100,plain,
    ( v1_subset_1(k2_tarski(sK2,sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6020,c_26,c_27,c_28,c_82,c_86,c_2843,c_4900,c_4903,c_5705,c_5817,c_5858,c_5935,c_6095,c_6096])).

cnf(c_4836,negated_conjecture,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_5493,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4836])).

cnf(c_6021,plain,
    ( v1_subset_1(k2_tarski(sK2,sK2),u1_struct_0(sK1)) != iProver_top
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6017,c_5493])).

cnf(c_5934,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(X0_48))
    | v2_struct_0(X0_48)
    | ~ l1_pre_topc(X0_48)
    | l1_pre_topc(k1_tex_2(X0_48,X0_47)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5914])).

cnf(c_5936,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | l1_pre_topc(k1_tex_2(sK1,sK2))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_5934])).

cnf(c_5816,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK1)
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK1,sK2)))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_5810])).

cnf(c_4854,plain,
    ( ~ v1_zfmisc_1(X0_47)
    | v1_zfmisc_1(X1_47)
    | X1_47 != X0_47 ),
    theory(equality)).

cnf(c_5751,plain,
    ( v1_zfmisc_1(X0_47)
    | ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_48,X1_47)))
    | X0_47 != u1_struct_0(k1_tex_2(X0_48,X1_47)) ),
    inference(instantiation,[status(thm)],[c_4854])).

cnf(c_5809,plain,
    ( v1_zfmisc_1(u1_struct_0(X0_48))
    | ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(X1_48,X0_47)))
    | u1_struct_0(X0_48) != u1_struct_0(k1_tex_2(X1_48,X0_47)) ),
    inference(instantiation,[status(thm)],[c_5751])).

cnf(c_5811,plain,
    ( u1_struct_0(X0_48) != u1_struct_0(k1_tex_2(X1_48,X0_47))
    | v1_zfmisc_1(u1_struct_0(X0_48)) = iProver_top
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1_48,X0_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5809])).

cnf(c_5813,plain,
    ( u1_struct_0(sK1) != u1_struct_0(k1_tex_2(sK1,sK2))
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK1,sK2))) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5811])).

cnf(c_8,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_4845,plain,
    ( v1_tex_2(X0_48,X1_48)
    | ~ m1_pre_topc(X0_48,X1_48)
    | ~ l1_pre_topc(X1_48)
    | sK0(X1_48,X0_48) = u1_struct_0(X0_48) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_5720,plain,
    ( v1_tex_2(k1_tex_2(X0_48,X0_47),X0_48)
    | ~ m1_pre_topc(k1_tex_2(X0_48,X0_47),X0_48)
    | ~ l1_pre_topc(X0_48)
    | sK0(X0_48,k1_tex_2(X0_48,X0_47)) = u1_struct_0(k1_tex_2(X0_48,X0_47)) ),
    inference(instantiation,[status(thm)],[c_4845])).

cnf(c_5721,plain,
    ( sK0(X0_48,k1_tex_2(X0_48,X0_47)) = u1_struct_0(k1_tex_2(X0_48,X0_47))
    | v1_tex_2(k1_tex_2(X0_48,X0_47),X0_48) = iProver_top
    | m1_pre_topc(k1_tex_2(X0_48,X0_47),X0_48) != iProver_top
    | l1_pre_topc(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5720])).

cnf(c_5723,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2))
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) = iProver_top
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5721])).

cnf(c_4,plain,
    ( ~ v7_struct_0(X0)
    | ~ l1_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_379,plain,
    ( ~ v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_zfmisc_1(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_1,c_4])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v7_struct_0(k1_tex_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2041,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | v1_zfmisc_1(u1_struct_0(X2))
    | k1_tex_2(X1,X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_379,c_15])).

cnf(c_2042,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k1_tex_2(X1,X0))
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1,X0))) ),
    inference(unflattening,[status(thm)],[c_2041])).

cnf(c_415,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | v1_zfmisc_1(u1_struct_0(X2))
    | k1_tex_2(X1,X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_379,c_15])).

cnf(c_416,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k1_tex_2(X1,X0))
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1,X0))) ),
    inference(unflattening,[status(thm)],[c_415])).

cnf(c_730,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X3)
    | X1 != X2
    | k1_tex_2(X1,X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_13])).

cnf(c_731,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k1_tex_2(X1,X0)) ),
    inference(unflattening,[status(thm)],[c_730])).

cnf(c_2044,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2042,c_416,c_731])).

cnf(c_2045,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1,X0))) ),
    inference(renaming,[status(thm)],[c_2044])).

cnf(c_4828,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(X0_48))
    | v2_struct_0(X0_48)
    | ~ l1_pre_topc(X0_48)
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_48,X0_47))) ),
    inference(subtyping,[status(esa)],[c_2045])).

cnf(c_4922,plain,
    ( m1_subset_1(X0_47,u1_struct_0(X0_48)) != iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | l1_pre_topc(X0_48) != iProver_top
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_48,X0_47))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4828])).

cnf(c_4924,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK1,sK2))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4922])).

cnf(c_4902,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ v2_struct_0(k1_tex_2(sK1,sK2))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_4839])).

cnf(c_4899,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_4840])).

cnf(c_4852,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_4880,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_4852])).

cnf(c_4858,plain,
    ( X0_48 != X1_48
    | u1_struct_0(X0_48) = u1_struct_0(X1_48) ),
    theory(equality)).

cnf(c_4870,plain,
    ( sK1 != sK1
    | u1_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_4858])).

cnf(c_19,plain,
    ( ~ v1_subset_1(k6_domain_1(X0,X1),X0)
    | ~ m1_subset_1(X1,X0)
    | v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1903,plain,
    ( v1_tex_2(k1_tex_2(sK1,sK2),sK1)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
    inference(prop_impl,[status(thm)],[c_22])).

cnf(c_1904,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(renaming,[status(thm)],[c_1903])).

cnf(c_2852,plain,
    ( v1_tex_2(k1_tex_2(sK1,sK2),sK1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1)
    | k6_domain_1(u1_struct_0(sK1),sK2) != k6_domain_1(X1,X0)
    | u1_struct_0(sK1) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_1904])).

cnf(c_2853,plain,
    ( v1_tex_2(k1_tex_2(sK1,sK2),sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_zfmisc_1(u1_struct_0(sK1))
    | k6_domain_1(u1_struct_0(sK1),sK2) != k6_domain_1(u1_struct_0(sK1),X0) ),
    inference(unflattening,[status(thm)],[c_2852])).

cnf(c_1442,plain,
    ( ~ v1_subset_1(k6_domain_1(X0,X1),X0)
    | v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X0)
    | u1_struct_0(sK1) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_23])).

cnf(c_1443,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_1442])).

cnf(c_2855,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK1))
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2853,c_25,c_24,c_22,c_81,c_85,c_1443])).

cnf(c_2856,plain,
    ( v1_tex_2(k1_tex_2(sK1,sK2),sK1)
    | ~ v1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_2855])).

cnf(c_2857,plain,
    ( v1_tex_2(k1_tex_2(sK1,sK2),sK1) = iProver_top
    | v1_zfmisc_1(u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2856])).

cnf(c_9,plain,
    ( v1_tex_2(X0,X1)
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_204,plain,
    ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
    inference(prop_impl,[status(thm)],[c_21])).

cnf(c_205,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(renaming,[status(thm)],[c_204])).

cnf(c_915,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | k1_tex_2(sK1,sK2) != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_205])).

cnf(c_916,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_915])).

cnf(c_7,plain,
    ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
    | v1_tex_2(X1,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_898,plain,
    ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | k1_tex_2(sK1,sK2) != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_205])).

cnf(c_899,plain,
    ( ~ v1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_898])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7154,c_7070,c_6700,c_6527,c_6312,c_6100,c_6096,c_6021,c_5936,c_5857,c_5816,c_5813,c_5723,c_4924,c_4902,c_4900,c_4899,c_4880,c_4870,c_2857,c_1433,c_916,c_899,c_85,c_81,c_28,c_23,c_27,c_24,c_26,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:14:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.09/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/0.99  
% 2.09/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.09/0.99  
% 2.09/0.99  ------  iProver source info
% 2.09/0.99  
% 2.09/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.09/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.09/0.99  git: non_committed_changes: false
% 2.09/0.99  git: last_make_outside_of_git: false
% 2.09/0.99  
% 2.09/0.99  ------ 
% 2.09/0.99  
% 2.09/0.99  ------ Input Options
% 2.09/0.99  
% 2.09/0.99  --out_options                           all
% 2.09/0.99  --tptp_safe_out                         true
% 2.09/0.99  --problem_path                          ""
% 2.09/0.99  --include_path                          ""
% 2.09/0.99  --clausifier                            res/vclausify_rel
% 2.09/0.99  --clausifier_options                    --mode clausify
% 2.09/0.99  --stdin                                 false
% 2.09/0.99  --stats_out                             all
% 2.09/0.99  
% 2.09/0.99  ------ General Options
% 2.09/0.99  
% 2.09/0.99  --fof                                   false
% 2.09/0.99  --time_out_real                         305.
% 2.09/0.99  --time_out_virtual                      -1.
% 2.09/0.99  --symbol_type_check                     false
% 2.09/0.99  --clausify_out                          false
% 2.09/0.99  --sig_cnt_out                           false
% 2.09/0.99  --trig_cnt_out                          false
% 2.09/0.99  --trig_cnt_out_tolerance                1.
% 2.09/0.99  --trig_cnt_out_sk_spl                   false
% 2.09/0.99  --abstr_cl_out                          false
% 2.09/0.99  
% 2.09/0.99  ------ Global Options
% 2.09/0.99  
% 2.09/0.99  --schedule                              default
% 2.09/0.99  --add_important_lit                     false
% 2.09/0.99  --prop_solver_per_cl                    1000
% 2.09/0.99  --min_unsat_core                        false
% 2.09/0.99  --soft_assumptions                      false
% 2.09/0.99  --soft_lemma_size                       3
% 2.09/0.99  --prop_impl_unit_size                   0
% 2.09/0.99  --prop_impl_unit                        []
% 2.09/0.99  --share_sel_clauses                     true
% 2.09/0.99  --reset_solvers                         false
% 2.09/0.99  --bc_imp_inh                            [conj_cone]
% 2.09/0.99  --conj_cone_tolerance                   3.
% 2.09/0.99  --extra_neg_conj                        none
% 2.09/0.99  --large_theory_mode                     true
% 2.09/0.99  --prolific_symb_bound                   200
% 2.09/0.99  --lt_threshold                          2000
% 2.09/0.99  --clause_weak_htbl                      true
% 2.09/0.99  --gc_record_bc_elim                     false
% 2.09/0.99  
% 2.09/0.99  ------ Preprocessing Options
% 2.09/0.99  
% 2.09/0.99  --preprocessing_flag                    true
% 2.09/0.99  --time_out_prep_mult                    0.1
% 2.09/0.99  --splitting_mode                        input
% 2.09/0.99  --splitting_grd                         true
% 2.09/0.99  --splitting_cvd                         false
% 2.09/0.99  --splitting_cvd_svl                     false
% 2.09/0.99  --splitting_nvd                         32
% 2.09/0.99  --sub_typing                            true
% 2.09/0.99  --prep_gs_sim                           true
% 2.09/0.99  --prep_unflatten                        true
% 2.09/0.99  --prep_res_sim                          true
% 2.09/0.99  --prep_upred                            true
% 2.09/0.99  --prep_sem_filter                       exhaustive
% 2.09/0.99  --prep_sem_filter_out                   false
% 2.09/0.99  --pred_elim                             true
% 2.09/0.99  --res_sim_input                         true
% 2.09/0.99  --eq_ax_congr_red                       true
% 2.09/0.99  --pure_diseq_elim                       true
% 2.09/0.99  --brand_transform                       false
% 2.09/0.99  --non_eq_to_eq                          false
% 2.09/0.99  --prep_def_merge                        true
% 2.09/0.99  --prep_def_merge_prop_impl              false
% 2.09/0.99  --prep_def_merge_mbd                    true
% 2.09/0.99  --prep_def_merge_tr_red                 false
% 2.09/0.99  --prep_def_merge_tr_cl                  false
% 2.09/0.99  --smt_preprocessing                     true
% 2.09/0.99  --smt_ac_axioms                         fast
% 2.09/0.99  --preprocessed_out                      false
% 2.09/0.99  --preprocessed_stats                    false
% 2.09/0.99  
% 2.09/0.99  ------ Abstraction refinement Options
% 2.09/0.99  
% 2.09/0.99  --abstr_ref                             []
% 2.09/0.99  --abstr_ref_prep                        false
% 2.09/0.99  --abstr_ref_until_sat                   false
% 2.09/0.99  --abstr_ref_sig_restrict                funpre
% 2.09/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.09/0.99  --abstr_ref_under                       []
% 2.09/0.99  
% 2.09/0.99  ------ SAT Options
% 2.09/0.99  
% 2.09/0.99  --sat_mode                              false
% 2.09/0.99  --sat_fm_restart_options                ""
% 2.09/0.99  --sat_gr_def                            false
% 2.09/0.99  --sat_epr_types                         true
% 2.09/0.99  --sat_non_cyclic_types                  false
% 2.09/0.99  --sat_finite_models                     false
% 2.09/0.99  --sat_fm_lemmas                         false
% 2.09/0.99  --sat_fm_prep                           false
% 2.09/0.99  --sat_fm_uc_incr                        true
% 2.09/0.99  --sat_out_model                         small
% 2.09/0.99  --sat_out_clauses                       false
% 2.09/0.99  
% 2.09/0.99  ------ QBF Options
% 2.09/0.99  
% 2.09/0.99  --qbf_mode                              false
% 2.09/0.99  --qbf_elim_univ                         false
% 2.09/0.99  --qbf_dom_inst                          none
% 2.09/0.99  --qbf_dom_pre_inst                      false
% 2.09/0.99  --qbf_sk_in                             false
% 2.09/0.99  --qbf_pred_elim                         true
% 2.09/0.99  --qbf_split                             512
% 2.09/0.99  
% 2.09/0.99  ------ BMC1 Options
% 2.09/0.99  
% 2.09/0.99  --bmc1_incremental                      false
% 2.09/0.99  --bmc1_axioms                           reachable_all
% 2.09/0.99  --bmc1_min_bound                        0
% 2.09/0.99  --bmc1_max_bound                        -1
% 2.09/0.99  --bmc1_max_bound_default                -1
% 2.09/0.99  --bmc1_symbol_reachability              true
% 2.09/0.99  --bmc1_property_lemmas                  false
% 2.09/0.99  --bmc1_k_induction                      false
% 2.09/0.99  --bmc1_non_equiv_states                 false
% 2.09/0.99  --bmc1_deadlock                         false
% 2.09/0.99  --bmc1_ucm                              false
% 2.09/0.99  --bmc1_add_unsat_core                   none
% 2.09/0.99  --bmc1_unsat_core_children              false
% 2.09/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.09/0.99  --bmc1_out_stat                         full
% 2.09/0.99  --bmc1_ground_init                      false
% 2.09/0.99  --bmc1_pre_inst_next_state              false
% 2.09/0.99  --bmc1_pre_inst_state                   false
% 2.09/0.99  --bmc1_pre_inst_reach_state             false
% 2.09/0.99  --bmc1_out_unsat_core                   false
% 2.09/0.99  --bmc1_aig_witness_out                  false
% 2.09/0.99  --bmc1_verbose                          false
% 2.09/0.99  --bmc1_dump_clauses_tptp                false
% 2.09/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.09/0.99  --bmc1_dump_file                        -
% 2.09/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.09/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.09/0.99  --bmc1_ucm_extend_mode                  1
% 2.09/0.99  --bmc1_ucm_init_mode                    2
% 2.09/0.99  --bmc1_ucm_cone_mode                    none
% 2.09/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.09/0.99  --bmc1_ucm_relax_model                  4
% 2.09/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.09/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.09/0.99  --bmc1_ucm_layered_model                none
% 2.09/0.99  --bmc1_ucm_max_lemma_size               10
% 2.09/0.99  
% 2.09/0.99  ------ AIG Options
% 2.09/0.99  
% 2.09/0.99  --aig_mode                              false
% 2.09/0.99  
% 2.09/0.99  ------ Instantiation Options
% 2.09/0.99  
% 2.09/0.99  --instantiation_flag                    true
% 2.09/0.99  --inst_sos_flag                         false
% 2.09/0.99  --inst_sos_phase                        true
% 2.09/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.09/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.09/0.99  --inst_lit_sel_side                     num_symb
% 2.09/0.99  --inst_solver_per_active                1400
% 2.09/0.99  --inst_solver_calls_frac                1.
% 2.09/0.99  --inst_passive_queue_type               priority_queues
% 2.09/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.09/0.99  --inst_passive_queues_freq              [25;2]
% 2.09/0.99  --inst_dismatching                      true
% 2.09/0.99  --inst_eager_unprocessed_to_passive     true
% 2.09/0.99  --inst_prop_sim_given                   true
% 2.09/0.99  --inst_prop_sim_new                     false
% 2.09/0.99  --inst_subs_new                         false
% 2.09/0.99  --inst_eq_res_simp                      false
% 2.09/0.99  --inst_subs_given                       false
% 2.09/0.99  --inst_orphan_elimination               true
% 2.09/0.99  --inst_learning_loop_flag               true
% 2.09/0.99  --inst_learning_start                   3000
% 2.09/0.99  --inst_learning_factor                  2
% 2.09/0.99  --inst_start_prop_sim_after_learn       3
% 2.09/0.99  --inst_sel_renew                        solver
% 2.09/0.99  --inst_lit_activity_flag                true
% 2.09/0.99  --inst_restr_to_given                   false
% 2.09/0.99  --inst_activity_threshold               500
% 2.09/0.99  --inst_out_proof                        true
% 2.09/0.99  
% 2.09/0.99  ------ Resolution Options
% 2.09/0.99  
% 2.09/0.99  --resolution_flag                       true
% 2.09/0.99  --res_lit_sel                           adaptive
% 2.09/0.99  --res_lit_sel_side                      none
% 2.09/0.99  --res_ordering                          kbo
% 2.09/0.99  --res_to_prop_solver                    active
% 2.09/0.99  --res_prop_simpl_new                    false
% 2.09/0.99  --res_prop_simpl_given                  true
% 2.09/0.99  --res_passive_queue_type                priority_queues
% 2.09/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.09/0.99  --res_passive_queues_freq               [15;5]
% 2.09/0.99  --res_forward_subs                      full
% 2.09/0.99  --res_backward_subs                     full
% 2.09/0.99  --res_forward_subs_resolution           true
% 2.09/0.99  --res_backward_subs_resolution          true
% 2.09/0.99  --res_orphan_elimination                true
% 2.09/0.99  --res_time_limit                        2.
% 2.09/0.99  --res_out_proof                         true
% 2.09/0.99  
% 2.09/0.99  ------ Superposition Options
% 2.09/0.99  
% 2.09/0.99  --superposition_flag                    true
% 2.09/0.99  --sup_passive_queue_type                priority_queues
% 2.09/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.09/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.09/0.99  --demod_completeness_check              fast
% 2.09/0.99  --demod_use_ground                      true
% 2.09/0.99  --sup_to_prop_solver                    passive
% 2.09/0.99  --sup_prop_simpl_new                    true
% 2.09/0.99  --sup_prop_simpl_given                  true
% 2.09/0.99  --sup_fun_splitting                     false
% 2.09/0.99  --sup_smt_interval                      50000
% 2.09/0.99  
% 2.09/0.99  ------ Superposition Simplification Setup
% 2.09/0.99  
% 2.09/0.99  --sup_indices_passive                   []
% 2.09/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.09/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_full_bw                           [BwDemod]
% 2.09/0.99  --sup_immed_triv                        [TrivRules]
% 2.09/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.09/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_immed_bw_main                     []
% 2.09/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.09/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/0.99  
% 2.09/0.99  ------ Combination Options
% 2.09/0.99  
% 2.09/0.99  --comb_res_mult                         3
% 2.09/0.99  --comb_sup_mult                         2
% 2.09/0.99  --comb_inst_mult                        10
% 2.09/0.99  
% 2.09/0.99  ------ Debug Options
% 2.09/0.99  
% 2.09/0.99  --dbg_backtrace                         false
% 2.09/0.99  --dbg_dump_prop_clauses                 false
% 2.09/0.99  --dbg_dump_prop_clauses_file            -
% 2.09/0.99  --dbg_out_stat                          false
% 2.09/0.99  ------ Parsing...
% 2.09/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.09/0.99  
% 2.09/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.09/0.99  
% 2.09/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.09/0.99  
% 2.09/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.09/0.99  ------ Proving...
% 2.09/0.99  ------ Problem Properties 
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  clauses                                 22
% 2.09/0.99  conjectures                             5
% 2.09/0.99  EPR                                     4
% 2.09/0.99  Horn                                    13
% 2.09/0.99  unary                                   3
% 2.09/0.99  binary                                  4
% 2.09/0.99  lits                                    69
% 2.09/0.99  lits eq                                 5
% 2.09/0.99  fd_pure                                 0
% 2.09/0.99  fd_pseudo                               0
% 2.09/0.99  fd_cond                                 0
% 2.09/0.99  fd_pseudo_cond                          1
% 2.09/0.99  AC symbols                              0
% 2.09/0.99  
% 2.09/0.99  ------ Schedule dynamic 5 is on 
% 2.09/0.99  
% 2.09/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  ------ 
% 2.09/0.99  Current options:
% 2.09/0.99  ------ 
% 2.09/0.99  
% 2.09/0.99  ------ Input Options
% 2.09/0.99  
% 2.09/0.99  --out_options                           all
% 2.09/0.99  --tptp_safe_out                         true
% 2.09/0.99  --problem_path                          ""
% 2.09/0.99  --include_path                          ""
% 2.09/0.99  --clausifier                            res/vclausify_rel
% 2.09/0.99  --clausifier_options                    --mode clausify
% 2.09/0.99  --stdin                                 false
% 2.09/0.99  --stats_out                             all
% 2.09/0.99  
% 2.09/0.99  ------ General Options
% 2.09/0.99  
% 2.09/0.99  --fof                                   false
% 2.09/0.99  --time_out_real                         305.
% 2.09/0.99  --time_out_virtual                      -1.
% 2.09/0.99  --symbol_type_check                     false
% 2.09/0.99  --clausify_out                          false
% 2.09/0.99  --sig_cnt_out                           false
% 2.09/0.99  --trig_cnt_out                          false
% 2.09/0.99  --trig_cnt_out_tolerance                1.
% 2.09/0.99  --trig_cnt_out_sk_spl                   false
% 2.09/0.99  --abstr_cl_out                          false
% 2.09/0.99  
% 2.09/0.99  ------ Global Options
% 2.09/0.99  
% 2.09/0.99  --schedule                              default
% 2.09/0.99  --add_important_lit                     false
% 2.09/0.99  --prop_solver_per_cl                    1000
% 2.09/0.99  --min_unsat_core                        false
% 2.09/0.99  --soft_assumptions                      false
% 2.09/0.99  --soft_lemma_size                       3
% 2.09/0.99  --prop_impl_unit_size                   0
% 2.09/0.99  --prop_impl_unit                        []
% 2.09/0.99  --share_sel_clauses                     true
% 2.09/0.99  --reset_solvers                         false
% 2.09/0.99  --bc_imp_inh                            [conj_cone]
% 2.09/0.99  --conj_cone_tolerance                   3.
% 2.09/0.99  --extra_neg_conj                        none
% 2.09/0.99  --large_theory_mode                     true
% 2.09/0.99  --prolific_symb_bound                   200
% 2.09/0.99  --lt_threshold                          2000
% 2.09/0.99  --clause_weak_htbl                      true
% 2.09/0.99  --gc_record_bc_elim                     false
% 2.09/0.99  
% 2.09/0.99  ------ Preprocessing Options
% 2.09/0.99  
% 2.09/0.99  --preprocessing_flag                    true
% 2.09/0.99  --time_out_prep_mult                    0.1
% 2.09/0.99  --splitting_mode                        input
% 2.09/0.99  --splitting_grd                         true
% 2.09/0.99  --splitting_cvd                         false
% 2.09/0.99  --splitting_cvd_svl                     false
% 2.09/0.99  --splitting_nvd                         32
% 2.09/0.99  --sub_typing                            true
% 2.09/0.99  --prep_gs_sim                           true
% 2.09/0.99  --prep_unflatten                        true
% 2.09/0.99  --prep_res_sim                          true
% 2.09/0.99  --prep_upred                            true
% 2.09/0.99  --prep_sem_filter                       exhaustive
% 2.09/0.99  --prep_sem_filter_out                   false
% 2.09/0.99  --pred_elim                             true
% 2.09/0.99  --res_sim_input                         true
% 2.09/0.99  --eq_ax_congr_red                       true
% 2.09/0.99  --pure_diseq_elim                       true
% 2.09/0.99  --brand_transform                       false
% 2.09/0.99  --non_eq_to_eq                          false
% 2.09/0.99  --prep_def_merge                        true
% 2.09/0.99  --prep_def_merge_prop_impl              false
% 2.09/0.99  --prep_def_merge_mbd                    true
% 2.09/0.99  --prep_def_merge_tr_red                 false
% 2.09/0.99  --prep_def_merge_tr_cl                  false
% 2.09/0.99  --smt_preprocessing                     true
% 2.09/0.99  --smt_ac_axioms                         fast
% 2.09/0.99  --preprocessed_out                      false
% 2.09/0.99  --preprocessed_stats                    false
% 2.09/0.99  
% 2.09/0.99  ------ Abstraction refinement Options
% 2.09/0.99  
% 2.09/0.99  --abstr_ref                             []
% 2.09/0.99  --abstr_ref_prep                        false
% 2.09/0.99  --abstr_ref_until_sat                   false
% 2.09/0.99  --abstr_ref_sig_restrict                funpre
% 2.09/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.09/0.99  --abstr_ref_under                       []
% 2.09/0.99  
% 2.09/0.99  ------ SAT Options
% 2.09/0.99  
% 2.09/0.99  --sat_mode                              false
% 2.09/0.99  --sat_fm_restart_options                ""
% 2.09/0.99  --sat_gr_def                            false
% 2.09/0.99  --sat_epr_types                         true
% 2.09/0.99  --sat_non_cyclic_types                  false
% 2.09/0.99  --sat_finite_models                     false
% 2.09/0.99  --sat_fm_lemmas                         false
% 2.09/0.99  --sat_fm_prep                           false
% 2.09/0.99  --sat_fm_uc_incr                        true
% 2.09/0.99  --sat_out_model                         small
% 2.09/0.99  --sat_out_clauses                       false
% 2.09/0.99  
% 2.09/0.99  ------ QBF Options
% 2.09/0.99  
% 2.09/0.99  --qbf_mode                              false
% 2.09/0.99  --qbf_elim_univ                         false
% 2.09/0.99  --qbf_dom_inst                          none
% 2.09/0.99  --qbf_dom_pre_inst                      false
% 2.09/0.99  --qbf_sk_in                             false
% 2.09/0.99  --qbf_pred_elim                         true
% 2.09/0.99  --qbf_split                             512
% 2.09/0.99  
% 2.09/0.99  ------ BMC1 Options
% 2.09/0.99  
% 2.09/0.99  --bmc1_incremental                      false
% 2.09/0.99  --bmc1_axioms                           reachable_all
% 2.09/0.99  --bmc1_min_bound                        0
% 2.09/0.99  --bmc1_max_bound                        -1
% 2.09/0.99  --bmc1_max_bound_default                -1
% 2.09/0.99  --bmc1_symbol_reachability              true
% 2.09/0.99  --bmc1_property_lemmas                  false
% 2.09/0.99  --bmc1_k_induction                      false
% 2.09/0.99  --bmc1_non_equiv_states                 false
% 2.09/0.99  --bmc1_deadlock                         false
% 2.09/0.99  --bmc1_ucm                              false
% 2.09/0.99  --bmc1_add_unsat_core                   none
% 2.09/0.99  --bmc1_unsat_core_children              false
% 2.09/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.09/0.99  --bmc1_out_stat                         full
% 2.09/0.99  --bmc1_ground_init                      false
% 2.09/0.99  --bmc1_pre_inst_next_state              false
% 2.09/0.99  --bmc1_pre_inst_state                   false
% 2.09/0.99  --bmc1_pre_inst_reach_state             false
% 2.09/0.99  --bmc1_out_unsat_core                   false
% 2.09/0.99  --bmc1_aig_witness_out                  false
% 2.09/0.99  --bmc1_verbose                          false
% 2.09/0.99  --bmc1_dump_clauses_tptp                false
% 2.09/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.09/0.99  --bmc1_dump_file                        -
% 2.09/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.09/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.09/0.99  --bmc1_ucm_extend_mode                  1
% 2.09/0.99  --bmc1_ucm_init_mode                    2
% 2.09/0.99  --bmc1_ucm_cone_mode                    none
% 2.09/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.09/0.99  --bmc1_ucm_relax_model                  4
% 2.09/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.09/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.09/0.99  --bmc1_ucm_layered_model                none
% 2.09/0.99  --bmc1_ucm_max_lemma_size               10
% 2.09/0.99  
% 2.09/0.99  ------ AIG Options
% 2.09/0.99  
% 2.09/0.99  --aig_mode                              false
% 2.09/0.99  
% 2.09/0.99  ------ Instantiation Options
% 2.09/0.99  
% 2.09/0.99  --instantiation_flag                    true
% 2.09/0.99  --inst_sos_flag                         false
% 2.09/0.99  --inst_sos_phase                        true
% 2.09/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.09/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.09/0.99  --inst_lit_sel_side                     none
% 2.09/0.99  --inst_solver_per_active                1400
% 2.09/0.99  --inst_solver_calls_frac                1.
% 2.09/0.99  --inst_passive_queue_type               priority_queues
% 2.09/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.09/0.99  --inst_passive_queues_freq              [25;2]
% 2.09/0.99  --inst_dismatching                      true
% 2.09/0.99  --inst_eager_unprocessed_to_passive     true
% 2.09/0.99  --inst_prop_sim_given                   true
% 2.09/0.99  --inst_prop_sim_new                     false
% 2.09/0.99  --inst_subs_new                         false
% 2.09/0.99  --inst_eq_res_simp                      false
% 2.09/0.99  --inst_subs_given                       false
% 2.09/0.99  --inst_orphan_elimination               true
% 2.09/0.99  --inst_learning_loop_flag               true
% 2.09/0.99  --inst_learning_start                   3000
% 2.09/0.99  --inst_learning_factor                  2
% 2.09/0.99  --inst_start_prop_sim_after_learn       3
% 2.09/0.99  --inst_sel_renew                        solver
% 2.09/0.99  --inst_lit_activity_flag                true
% 2.09/0.99  --inst_restr_to_given                   false
% 2.09/0.99  --inst_activity_threshold               500
% 2.09/0.99  --inst_out_proof                        true
% 2.09/0.99  
% 2.09/0.99  ------ Resolution Options
% 2.09/0.99  
% 2.09/0.99  --resolution_flag                       false
% 2.09/0.99  --res_lit_sel                           adaptive
% 2.09/0.99  --res_lit_sel_side                      none
% 2.09/0.99  --res_ordering                          kbo
% 2.09/0.99  --res_to_prop_solver                    active
% 2.09/0.99  --res_prop_simpl_new                    false
% 2.09/0.99  --res_prop_simpl_given                  true
% 2.09/0.99  --res_passive_queue_type                priority_queues
% 2.09/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.09/0.99  --res_passive_queues_freq               [15;5]
% 2.09/0.99  --res_forward_subs                      full
% 2.09/0.99  --res_backward_subs                     full
% 2.09/0.99  --res_forward_subs_resolution           true
% 2.09/0.99  --res_backward_subs_resolution          true
% 2.09/0.99  --res_orphan_elimination                true
% 2.09/0.99  --res_time_limit                        2.
% 2.09/0.99  --res_out_proof                         true
% 2.09/0.99  
% 2.09/0.99  ------ Superposition Options
% 2.09/0.99  
% 2.09/0.99  --superposition_flag                    true
% 2.09/0.99  --sup_passive_queue_type                priority_queues
% 2.09/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.09/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.09/0.99  --demod_completeness_check              fast
% 2.09/0.99  --demod_use_ground                      true
% 2.09/0.99  --sup_to_prop_solver                    passive
% 2.09/0.99  --sup_prop_simpl_new                    true
% 2.09/0.99  --sup_prop_simpl_given                  true
% 2.09/0.99  --sup_fun_splitting                     false
% 2.09/0.99  --sup_smt_interval                      50000
% 2.09/0.99  
% 2.09/0.99  ------ Superposition Simplification Setup
% 2.09/0.99  
% 2.09/0.99  --sup_indices_passive                   []
% 2.09/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.09/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_full_bw                           [BwDemod]
% 2.09/0.99  --sup_immed_triv                        [TrivRules]
% 2.09/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.09/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_immed_bw_main                     []
% 2.09/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.09/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/0.99  
% 2.09/0.99  ------ Combination Options
% 2.09/0.99  
% 2.09/0.99  --comb_res_mult                         3
% 2.09/0.99  --comb_sup_mult                         2
% 2.09/0.99  --comb_inst_mult                        10
% 2.09/0.99  
% 2.09/0.99  ------ Debug Options
% 2.09/0.99  
% 2.09/0.99  --dbg_backtrace                         false
% 2.09/0.99  --dbg_dump_prop_clauses                 false
% 2.09/0.99  --dbg_dump_prop_clauses_file            -
% 2.09/0.99  --dbg_out_stat                          false
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  ------ Proving...
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  % SZS status Theorem for theBenchmark.p
% 2.09/0.99  
% 2.09/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.09/0.99  
% 2.09/0.99  fof(f10,axiom,(
% 2.09/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f33,plain,(
% 2.09/0.99    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f10])).
% 2.09/0.99  
% 2.09/0.99  fof(f52,plain,(
% 2.09/0.99    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.09/0.99    inference(nnf_transformation,[],[f33])).
% 2.09/0.99  
% 2.09/0.99  fof(f71,plain,(
% 2.09/0.99    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.09/0.99    inference(cnf_transformation,[],[f52])).
% 2.09/0.99  
% 2.09/0.99  fof(f17,conjecture,(
% 2.09/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f18,negated_conjecture,(
% 2.09/0.99    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 2.09/0.99    inference(negated_conjecture,[],[f17])).
% 2.09/0.99  
% 2.09/0.99  fof(f46,plain,(
% 2.09/0.99    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f18])).
% 2.09/0.99  
% 2.09/0.99  fof(f47,plain,(
% 2.09/0.99    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.09/0.99    inference(flattening,[],[f46])).
% 2.09/0.99  
% 2.09/0.99  fof(f53,plain,(
% 2.09/0.99    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.09/0.99    inference(nnf_transformation,[],[f47])).
% 2.09/0.99  
% 2.09/0.99  fof(f54,plain,(
% 2.09/0.99    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.09/0.99    inference(flattening,[],[f53])).
% 2.09/0.99  
% 2.09/0.99  fof(f56,plain,(
% 2.09/0.99    ( ! [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),sK2),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,sK2),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),sK2),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,sK2),X0)) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 2.09/0.99    introduced(choice_axiom,[])).
% 2.09/0.99  
% 2.09/0.99  fof(f55,plain,(
% 2.09/0.99    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK1),X1),u1_struct_0(sK1)) | ~v1_tex_2(k1_tex_2(sK1,X1),sK1)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK1),X1),u1_struct_0(sK1)) | v1_tex_2(k1_tex_2(sK1,X1),sK1)) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.09/0.99    introduced(choice_axiom,[])).
% 2.09/0.99  
% 2.09/0.99  fof(f57,plain,(
% 2.09/0.99    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | ~v1_tex_2(k1_tex_2(sK1,sK2),sK1)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | v1_tex_2(k1_tex_2(sK1,sK2),sK1)) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.09/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f54,f56,f55])).
% 2.09/0.99  
% 2.09/0.99  fof(f82,plain,(
% 2.09/0.99    m1_subset_1(sK2,u1_struct_0(sK1))),
% 2.09/0.99    inference(cnf_transformation,[],[f57])).
% 2.09/0.99  
% 2.09/0.99  fof(f7,axiom,(
% 2.09/0.99    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f28,plain,(
% 2.09/0.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f7])).
% 2.09/0.99  
% 2.09/0.99  fof(f29,plain,(
% 2.09/0.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.09/0.99    inference(flattening,[],[f28])).
% 2.09/0.99  
% 2.09/0.99  fof(f64,plain,(
% 2.09/0.99    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f29])).
% 2.09/0.99  
% 2.09/0.99  fof(f1,axiom,(
% 2.09/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f58,plain,(
% 2.09/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f1])).
% 2.09/0.99  
% 2.09/0.99  fof(f85,plain,(
% 2.09/0.99    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.09/0.99    inference(definition_unfolding,[],[f64,f58])).
% 2.09/0.99  
% 2.09/0.99  fof(f80,plain,(
% 2.09/0.99    ~v2_struct_0(sK1)),
% 2.09/0.99    inference(cnf_transformation,[],[f57])).
% 2.09/0.99  
% 2.09/0.99  fof(f81,plain,(
% 2.09/0.99    l1_pre_topc(sK1)),
% 2.09/0.99    inference(cnf_transformation,[],[f57])).
% 2.09/0.99  
% 2.09/0.99  fof(f5,axiom,(
% 2.09/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f24,plain,(
% 2.09/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f5])).
% 2.09/0.99  
% 2.09/0.99  fof(f25,plain,(
% 2.09/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.09/0.99    inference(flattening,[],[f24])).
% 2.09/0.99  
% 2.09/0.99  fof(f62,plain,(
% 2.09/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f25])).
% 2.09/0.99  
% 2.09/0.99  fof(f3,axiom,(
% 2.09/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f22,plain,(
% 2.09/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.09/0.99    inference(ennf_transformation,[],[f3])).
% 2.09/0.99  
% 2.09/0.99  fof(f60,plain,(
% 2.09/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f22])).
% 2.09/0.99  
% 2.09/0.99  fof(f83,plain,(
% 2.09/0.99    v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | v1_tex_2(k1_tex_2(sK1,sK2),sK1)),
% 2.09/0.99    inference(cnf_transformation,[],[f57])).
% 2.09/0.99  
% 2.09/0.99  fof(f16,axiom,(
% 2.09/0.99    ! [X0] : ((~v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => v1_subset_1(k6_domain_1(X0,X1),X0)))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f44,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | (v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f16])).
% 2.09/0.99  
% 2.09/0.99  fof(f45,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 2.09/0.99    inference(flattening,[],[f44])).
% 2.09/0.99  
% 2.09/0.99  fof(f79,plain,(
% 2.09/0.99    ( ! [X0,X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f45])).
% 2.09/0.99  
% 2.09/0.99  fof(f2,axiom,(
% 2.09/0.99    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f21,plain,(
% 2.09/0.99    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 2.09/0.99    inference(ennf_transformation,[],[f2])).
% 2.09/0.99  
% 2.09/0.99  fof(f59,plain,(
% 2.09/0.99    ( ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f21])).
% 2.09/0.99  
% 2.09/0.99  fof(f84,plain,(
% 2.09/0.99    ~v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | ~v1_tex_2(k1_tex_2(sK1,sK2),sK1)),
% 2.09/0.99    inference(cnf_transformation,[],[f57])).
% 2.09/0.99  
% 2.09/0.99  fof(f11,axiom,(
% 2.09/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f20,plain,(
% 2.09/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.09/0.99    inference(pure_predicate_removal,[],[f11])).
% 2.09/0.99  
% 2.09/0.99  fof(f34,plain,(
% 2.09/0.99    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f20])).
% 2.09/0.99  
% 2.09/0.99  fof(f35,plain,(
% 2.09/0.99    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.09/0.99    inference(flattening,[],[f34])).
% 2.09/0.99  
% 2.09/0.99  fof(f73,plain,(
% 2.09/0.99    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f35])).
% 2.09/0.99  
% 2.09/0.99  fof(f12,axiom,(
% 2.09/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f19,plain,(
% 2.09/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.09/0.99    inference(pure_predicate_removal,[],[f12])).
% 2.09/0.99  
% 2.09/0.99  fof(f36,plain,(
% 2.09/0.99    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f19])).
% 2.09/0.99  
% 2.09/0.99  fof(f37,plain,(
% 2.09/0.99    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.09/0.99    inference(flattening,[],[f36])).
% 2.09/0.99  
% 2.09/0.99  fof(f74,plain,(
% 2.09/0.99    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f37])).
% 2.09/0.99  
% 2.09/0.99  fof(f13,axiom,(
% 2.09/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ~(v1_tex_2(X1,X0) & u1_struct_0(X0) = u1_struct_0(X1))))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f38,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : ((~v1_tex_2(X1,X0) | u1_struct_0(X0) != u1_struct_0(X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.09/0.99    inference(ennf_transformation,[],[f13])).
% 2.09/0.99  
% 2.09/0.99  fof(f39,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (~v1_tex_2(X1,X0) | u1_struct_0(X0) != u1_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.09/0.99    inference(flattening,[],[f38])).
% 2.09/0.99  
% 2.09/0.99  fof(f76,plain,(
% 2.09/0.99    ( ! [X0,X1] : (~v1_tex_2(X1,X0) | u1_struct_0(X0) != u1_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f39])).
% 2.09/0.99  
% 2.09/0.99  fof(f8,axiom,(
% 2.09/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f30,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.09/0.99    inference(ennf_transformation,[],[f8])).
% 2.09/0.99  
% 2.09/0.99  fof(f65,plain,(
% 2.09/0.99    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f30])).
% 2.09/0.99  
% 2.09/0.99  fof(f14,axiom,(
% 2.09/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f40,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 2.09/0.99    inference(ennf_transformation,[],[f14])).
% 2.09/0.99  
% 2.09/0.99  fof(f41,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.09/0.99    inference(flattening,[],[f40])).
% 2.09/0.99  
% 2.09/0.99  fof(f77,plain,(
% 2.09/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f41])).
% 2.09/0.99  
% 2.09/0.99  fof(f4,axiom,(
% 2.09/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f23,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.09/0.99    inference(ennf_transformation,[],[f4])).
% 2.09/0.99  
% 2.09/0.99  fof(f61,plain,(
% 2.09/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f23])).
% 2.09/0.99  
% 2.09/0.99  fof(f9,axiom,(
% 2.09/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f31,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.09/0.99    inference(ennf_transformation,[],[f9])).
% 2.09/0.99  
% 2.09/0.99  fof(f32,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.09/0.99    inference(flattening,[],[f31])).
% 2.09/0.99  
% 2.09/0.99  fof(f48,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.09/0.99    inference(nnf_transformation,[],[f32])).
% 2.09/0.99  
% 2.09/0.99  fof(f49,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.09/0.99    inference(rectify,[],[f48])).
% 2.09/0.99  
% 2.09/0.99  fof(f50,plain,(
% 2.09/0.99    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.09/0.99    introduced(choice_axiom,[])).
% 2.09/0.99  
% 2.09/0.99  fof(f51,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.09/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f49,f50])).
% 2.09/0.99  
% 2.09/0.99  fof(f68,plain,(
% 2.09/0.99    ( ! [X0,X1] : (v1_tex_2(X1,X0) | u1_struct_0(X1) = sK0(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f51])).
% 2.09/0.99  
% 2.09/0.99  fof(f6,axiom,(
% 2.09/0.99    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f26,plain,(
% 2.09/0.99    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 2.09/0.99    inference(ennf_transformation,[],[f6])).
% 2.09/0.99  
% 2.09/0.99  fof(f27,plain,(
% 2.09/0.99    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 2.09/0.99    inference(flattening,[],[f26])).
% 2.09/0.99  
% 2.09/0.99  fof(f63,plain,(
% 2.09/0.99    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f27])).
% 2.09/0.99  
% 2.09/0.99  fof(f75,plain,(
% 2.09/0.99    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f37])).
% 2.09/0.99  
% 2.09/0.99  fof(f15,axiom,(
% 2.09/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 2.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f42,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : ((~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0)) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 2.09/0.99    inference(ennf_transformation,[],[f15])).
% 2.09/0.99  
% 2.09/0.99  fof(f43,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 2.09/0.99    inference(flattening,[],[f42])).
% 2.09/0.99  
% 2.09/0.99  fof(f78,plain,(
% 2.09/0.99    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f43])).
% 2.09/0.99  
% 2.09/0.99  fof(f67,plain,(
% 2.09/0.99    ( ! [X0,X1] : (v1_tex_2(X1,X0) | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f51])).
% 2.09/0.99  
% 2.09/0.99  fof(f69,plain,(
% 2.09/0.99    ( ! [X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f51])).
% 2.09/0.99  
% 2.09/0.99  cnf(c_4853,plain,
% 2.09/0.99      ( X0_47 != X1_47 | X2_47 != X1_47 | X2_47 = X0_47 ),
% 2.09/0.99      theory(equality) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_6049,plain,
% 2.09/0.99      ( X0_47 != X1_47
% 2.09/0.99      | u1_struct_0(k1_tex_2(X0_48,X2_47)) != X1_47
% 2.09/0.99      | u1_struct_0(k1_tex_2(X0_48,X2_47)) = X0_47 ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_4853]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_6750,plain,
% 2.09/0.99      ( X0_47 != u1_struct_0(k1_tex_2(sK1,sK2))
% 2.09/0.99      | u1_struct_0(k1_tex_2(X0_48,X1_47)) = X0_47
% 2.09/0.99      | u1_struct_0(k1_tex_2(X0_48,X1_47)) != u1_struct_0(k1_tex_2(sK1,sK2)) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_6049]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_7153,plain,
% 2.09/0.99      ( sK0(sK1,k1_tex_2(sK1,sK2)) != u1_struct_0(k1_tex_2(sK1,sK2))
% 2.09/0.99      | u1_struct_0(k1_tex_2(X0_48,X0_47)) = sK0(sK1,k1_tex_2(sK1,sK2))
% 2.09/0.99      | u1_struct_0(k1_tex_2(X0_48,X0_47)) != u1_struct_0(k1_tex_2(sK1,sK2)) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_6750]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_7154,plain,
% 2.09/0.99      ( sK0(sK1,k1_tex_2(sK1,sK2)) != u1_struct_0(k1_tex_2(sK1,sK2))
% 2.09/0.99      | u1_struct_0(k1_tex_2(sK1,sK2)) = sK0(sK1,k1_tex_2(sK1,sK2))
% 2.09/0.99      | u1_struct_0(k1_tex_2(sK1,sK2)) != u1_struct_0(k1_tex_2(sK1,sK2)) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_7153]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_5777,plain,
% 2.09/0.99      ( u1_struct_0(k1_tex_2(sK1,sK2)) != X0_47
% 2.09/0.99      | u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
% 2.09/0.99      | u1_struct_0(sK1) != X0_47 ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_4853]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_7069,plain,
% 2.09/0.99      ( u1_struct_0(k1_tex_2(sK1,sK2)) != sK0(sK1,k1_tex_2(sK1,X0_47))
% 2.09/0.99      | u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
% 2.09/0.99      | u1_struct_0(sK1) != sK0(sK1,k1_tex_2(sK1,X0_47)) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_5777]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_7070,plain,
% 2.09/0.99      ( u1_struct_0(k1_tex_2(sK1,sK2)) != sK0(sK1,k1_tex_2(sK1,sK2))
% 2.09/0.99      | u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
% 2.09/0.99      | u1_struct_0(sK1) != sK0(sK1,k1_tex_2(sK1,sK2)) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_7069]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_5826,plain,
% 2.09/0.99      ( X0_47 != X1_47
% 2.09/0.99      | X0_47 = u1_struct_0(k1_tex_2(X0_48,X2_47))
% 2.09/0.99      | u1_struct_0(k1_tex_2(X0_48,X2_47)) != X1_47 ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_4853]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_6037,plain,
% 2.09/0.99      ( X0_47 != u1_struct_0(X0_48)
% 2.09/0.99      | X0_47 = u1_struct_0(k1_tex_2(X1_48,X1_47))
% 2.09/0.99      | u1_struct_0(k1_tex_2(X1_48,X1_47)) != u1_struct_0(X0_48) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_5826]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_6699,plain,
% 2.09/0.99      ( u1_struct_0(X0_48) != u1_struct_0(X1_48)
% 2.09/0.99      | u1_struct_0(X0_48) = u1_struct_0(k1_tex_2(X2_48,X0_47))
% 2.09/0.99      | u1_struct_0(k1_tex_2(X2_48,X0_47)) != u1_struct_0(X1_48) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_6037]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_6700,plain,
% 2.09/0.99      ( u1_struct_0(k1_tex_2(sK1,sK2)) != u1_struct_0(sK1)
% 2.09/0.99      | u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK1,sK2))
% 2.09/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_6699]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_5894,plain,
% 2.09/0.99      ( X0_47 != X1_47
% 2.09/0.99      | u1_struct_0(sK1) != X1_47
% 2.09/0.99      | u1_struct_0(sK1) = X0_47 ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_4853]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_6154,plain,
% 2.09/0.99      ( X0_47 != u1_struct_0(sK1)
% 2.09/0.99      | u1_struct_0(sK1) = X0_47
% 2.09/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_5894]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_6526,plain,
% 2.09/0.99      ( sK0(sK1,k1_tex_2(sK1,X0_47)) != u1_struct_0(sK1)
% 2.09/0.99      | u1_struct_0(sK1) = sK0(sK1,k1_tex_2(sK1,X0_47))
% 2.09/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_6154]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_6527,plain,
% 2.09/0.99      ( sK0(sK1,k1_tex_2(sK1,sK2)) != u1_struct_0(sK1)
% 2.09/0.99      | u1_struct_0(sK1) = sK0(sK1,k1_tex_2(sK1,sK2))
% 2.09/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_6526]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_11,plain,
% 2.09/0.99      ( v1_subset_1(X0,X1)
% 2.09/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.09/0.99      | X0 = X1 ),
% 2.09/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_4842,plain,
% 2.09/0.99      ( v1_subset_1(X0_47,X1_47)
% 2.09/0.99      | ~ m1_subset_1(X0_47,k1_zfmisc_1(X1_47))
% 2.09/1.00      | X0_47 = X1_47 ),
% 2.09/1.00      inference(subtyping,[status(esa)],[c_11]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_5793,plain,
% 2.09/1.00      ( v1_subset_1(X0_47,u1_struct_0(sK1))
% 2.09/1.00      | ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.09/1.00      | X0_47 = u1_struct_0(sK1) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_4842]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_6308,plain,
% 2.09/1.00      ( v1_subset_1(sK0(sK1,k1_tex_2(sK1,X0_47)),u1_struct_0(sK1))
% 2.09/1.00      | ~ m1_subset_1(sK0(sK1,k1_tex_2(sK1,X0_47)),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.09/1.00      | sK0(sK1,k1_tex_2(sK1,X0_47)) = u1_struct_0(sK1) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_5793]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_6312,plain,
% 2.09/1.00      ( v1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
% 2.09/1.00      | ~ m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.09/1.00      | sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(sK1) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_6308]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_23,negated_conjecture,
% 2.09/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.09/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_4834,negated_conjecture,
% 2.09/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.09/1.00      inference(subtyping,[status(esa)],[c_23]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_5495,plain,
% 2.09/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 2.09/1.00      inference(predicate_to_equality,[status(thm)],[c_4834]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_5,plain,
% 2.09/1.00      ( ~ m1_subset_1(X0,X1)
% 2.09/1.00      | v1_xboole_0(X1)
% 2.09/1.00      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 2.09/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_4847,plain,
% 2.09/1.00      ( ~ m1_subset_1(X0_47,X1_47)
% 2.09/1.00      | v1_xboole_0(X1_47)
% 2.09/1.00      | k6_domain_1(X1_47,X0_47) = k2_tarski(X0_47,X0_47) ),
% 2.09/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_5482,plain,
% 2.09/1.00      ( k6_domain_1(X0_47,X1_47) = k2_tarski(X1_47,X1_47)
% 2.09/1.00      | m1_subset_1(X1_47,X0_47) != iProver_top
% 2.09/1.00      | v1_xboole_0(X0_47) = iProver_top ),
% 2.09/1.00      inference(predicate_to_equality,[status(thm)],[c_4847]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_5855,plain,
% 2.09/1.00      ( k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2)
% 2.09/1.00      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 2.09/1.00      inference(superposition,[status(thm)],[c_5495,c_5482]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_25,negated_conjecture,
% 2.09/1.00      ( ~ v2_struct_0(sK1) ),
% 2.09/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_24,negated_conjecture,
% 2.09/1.00      ( l1_pre_topc(sK1) ),
% 2.09/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_3,plain,
% 2.09/1.00      ( v2_struct_0(X0)
% 2.09/1.00      | ~ l1_struct_0(X0)
% 2.09/1.00      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.09/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_81,plain,
% 2.09/1.00      ( v2_struct_0(sK1)
% 2.09/1.00      | ~ l1_struct_0(sK1)
% 2.09/1.00      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_1,plain,
% 2.09/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.09/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_85,plain,
% 2.09/1.00      ( ~ l1_pre_topc(sK1) | l1_struct_0(sK1) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_5707,plain,
% 2.09/1.00      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.09/1.00      | v1_xboole_0(u1_struct_0(sK1))
% 2.09/1.00      | k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_4847]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_6017,plain,
% 2.09/1.00      ( k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2) ),
% 2.09/1.00      inference(global_propositional_subsumption,
% 2.09/1.00                [status(thm)],
% 2.09/1.00                [c_5855,c_25,c_24,c_23,c_81,c_85,c_5707]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_22,negated_conjecture,
% 2.09/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.09/1.00      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
% 2.09/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_4835,negated_conjecture,
% 2.09/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.09/1.00      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
% 2.09/1.00      inference(subtyping,[status(esa)],[c_22]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_5494,plain,
% 2.09/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
% 2.09/1.00      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) = iProver_top ),
% 2.09/1.00      inference(predicate_to_equality,[status(thm)],[c_4835]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_6020,plain,
% 2.09/1.00      ( v1_subset_1(k2_tarski(sK2,sK2),u1_struct_0(sK1)) = iProver_top
% 2.09/1.00      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) = iProver_top ),
% 2.09/1.00      inference(demodulation,[status(thm)],[c_6017,c_5494]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_26,plain,
% 2.09/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 2.09/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_27,plain,
% 2.09/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 2.09/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_28,plain,
% 2.09/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 2.09/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_80,plain,
% 2.09/1.00      ( v2_struct_0(X0) = iProver_top
% 2.09/1.00      | l1_struct_0(X0) != iProver_top
% 2.09/1.00      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 2.09/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_82,plain,
% 2.09/1.00      ( v2_struct_0(sK1) = iProver_top
% 2.09/1.00      | l1_struct_0(sK1) != iProver_top
% 2.09/1.00      | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_80]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_84,plain,
% 2.09/1.00      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 2.09/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_86,plain,
% 2.09/1.00      ( l1_pre_topc(sK1) != iProver_top
% 2.09/1.00      | l1_struct_0(sK1) = iProver_top ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_84]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_20,plain,
% 2.09/1.00      ( v1_subset_1(k6_domain_1(X0,X1),X0)
% 2.09/1.00      | ~ m1_subset_1(X1,X0)
% 2.09/1.00      | v1_xboole_0(X0)
% 2.09/1.00      | v1_zfmisc_1(X0) ),
% 2.09/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_0,plain,
% 2.09/1.00      ( ~ v1_xboole_0(X0) | v1_zfmisc_1(X0) ),
% 2.09/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_148,plain,
% 2.09/1.00      ( ~ m1_subset_1(X1,X0)
% 2.09/1.00      | v1_subset_1(k6_domain_1(X0,X1),X0)
% 2.09/1.00      | v1_zfmisc_1(X0) ),
% 2.09/1.00      inference(global_propositional_subsumption,
% 2.09/1.00                [status(thm)],
% 2.09/1.00                [c_20,c_0]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_149,plain,
% 2.09/1.00      ( v1_subset_1(k6_domain_1(X0,X1),X0)
% 2.09/1.00      | ~ m1_subset_1(X1,X0)
% 2.09/1.00      | v1_zfmisc_1(X0) ),
% 2.09/1.00      inference(renaming,[status(thm)],[c_148]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_21,negated_conjecture,
% 2.09/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.09/1.00      | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
% 2.09/1.00      inference(cnf_transformation,[],[f84]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_1901,plain,
% 2.09/1.00      ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
% 2.09/1.00      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
% 2.09/1.00      inference(prop_impl,[status(thm)],[c_21]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_1902,plain,
% 2.09/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.09/1.00      | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
% 2.09/1.00      inference(renaming,[status(thm)],[c_1901]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_2838,plain,
% 2.09/1.00      ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
% 2.09/1.00      | ~ m1_subset_1(X0,X1)
% 2.09/1.00      | v1_zfmisc_1(X1)
% 2.09/1.00      | k6_domain_1(u1_struct_0(sK1),sK2) != k6_domain_1(X1,X0)
% 2.09/1.00      | u1_struct_0(sK1) != X1 ),
% 2.09/1.00      inference(resolution_lifted,[status(thm)],[c_149,c_1902]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_2839,plain,
% 2.09/1.00      ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
% 2.09/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.09/1.00      | v1_zfmisc_1(u1_struct_0(sK1))
% 2.09/1.00      | k6_domain_1(u1_struct_0(sK1),sK2) != k6_domain_1(u1_struct_0(sK1),X0) ),
% 2.09/1.00      inference(unflattening,[status(thm)],[c_2838]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_1432,plain,
% 2.09/1.00      ( v1_subset_1(k6_domain_1(X0,X1),X0)
% 2.09/1.00      | v1_zfmisc_1(X0)
% 2.09/1.00      | u1_struct_0(sK1) != X0
% 2.09/1.00      | sK2 != X1 ),
% 2.09/1.00      inference(resolution_lifted,[status(thm)],[c_149,c_23]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_1433,plain,
% 2.09/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.09/1.00      | v1_zfmisc_1(u1_struct_0(sK1)) ),
% 2.09/1.00      inference(unflattening,[status(thm)],[c_1432]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_2841,plain,
% 2.09/1.00      ( v1_zfmisc_1(u1_struct_0(sK1))
% 2.09/1.00      | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
% 2.09/1.00      inference(global_propositional_subsumption,
% 2.09/1.00                [status(thm)],
% 2.09/1.00                [c_2839,c_21,c_1433]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_2842,plain,
% 2.09/1.00      ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
% 2.09/1.00      | v1_zfmisc_1(u1_struct_0(sK1)) ),
% 2.09/1.00      inference(renaming,[status(thm)],[c_2841]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_2843,plain,
% 2.09/1.00      ( v1_tex_2(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 2.09/1.00      | v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top ),
% 2.09/1.00      inference(predicate_to_equality,[status(thm)],[c_2842]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_13,plain,
% 2.09/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.09/1.00      | m1_pre_topc(k1_tex_2(X1,X0),X1)
% 2.09/1.00      | v2_struct_0(X1)
% 2.09/1.00      | ~ l1_pre_topc(X1) ),
% 2.09/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_4840,plain,
% 2.09/1.00      ( ~ m1_subset_1(X0_47,u1_struct_0(X0_48))
% 2.09/1.00      | m1_pre_topc(k1_tex_2(X0_48,X0_47),X0_48)
% 2.09/1.00      | v2_struct_0(X0_48)
% 2.09/1.00      | ~ l1_pre_topc(X0_48) ),
% 2.09/1.00      inference(subtyping,[status(esa)],[c_13]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_4898,plain,
% 2.09/1.00      ( m1_subset_1(X0_47,u1_struct_0(X0_48)) != iProver_top
% 2.09/1.00      | m1_pre_topc(k1_tex_2(X0_48,X0_47),X0_48) = iProver_top
% 2.09/1.00      | v2_struct_0(X0_48) = iProver_top
% 2.09/1.00      | l1_pre_topc(X0_48) != iProver_top ),
% 2.09/1.00      inference(predicate_to_equality,[status(thm)],[c_4840]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_4900,plain,
% 2.09/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.09/1.00      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) = iProver_top
% 2.09/1.00      | v2_struct_0(sK1) = iProver_top
% 2.09/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_4898]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_16,plain,
% 2.09/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.09/1.00      | v2_struct_0(X1)
% 2.09/1.00      | ~ v2_struct_0(k1_tex_2(X1,X0))
% 2.09/1.00      | ~ l1_pre_topc(X1) ),
% 2.09/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_4839,plain,
% 2.09/1.00      ( ~ m1_subset_1(X0_47,u1_struct_0(X0_48))
% 2.09/1.00      | v2_struct_0(X0_48)
% 2.09/1.00      | ~ v2_struct_0(k1_tex_2(X0_48,X0_47))
% 2.09/1.00      | ~ l1_pre_topc(X0_48) ),
% 2.09/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_4901,plain,
% 2.09/1.00      ( m1_subset_1(X0_47,u1_struct_0(X0_48)) != iProver_top
% 2.09/1.00      | v2_struct_0(X0_48) = iProver_top
% 2.09/1.00      | v2_struct_0(k1_tex_2(X0_48,X0_47)) != iProver_top
% 2.09/1.00      | l1_pre_topc(X0_48) != iProver_top ),
% 2.09/1.00      inference(predicate_to_equality,[status(thm)],[c_4839]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_4903,plain,
% 2.09/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.09/1.00      | v2_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
% 2.09/1.00      | v2_struct_0(sK1) = iProver_top
% 2.09/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_4901]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_17,plain,
% 2.09/1.00      ( ~ v1_tex_2(X0,X1)
% 2.09/1.00      | ~ m1_pre_topc(X0,X1)
% 2.09/1.00      | ~ l1_pre_topc(X1)
% 2.09/1.00      | u1_struct_0(X0) != u1_struct_0(X1) ),
% 2.09/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_4838,plain,
% 2.09/1.00      ( ~ v1_tex_2(X0_48,X1_48)
% 2.09/1.00      | ~ m1_pre_topc(X0_48,X1_48)
% 2.09/1.00      | ~ l1_pre_topc(X1_48)
% 2.09/1.00      | u1_struct_0(X0_48) != u1_struct_0(X1_48) ),
% 2.09/1.00      inference(subtyping,[status(esa)],[c_17]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_5704,plain,
% 2.09/1.00      ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
% 2.09/1.00      | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.09/1.00      | ~ l1_pre_topc(sK1)
% 2.09/1.00      | u1_struct_0(k1_tex_2(sK1,sK2)) != u1_struct_0(sK1) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_4838]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_5705,plain,
% 2.09/1.00      ( u1_struct_0(k1_tex_2(sK1,sK2)) != u1_struct_0(sK1)
% 2.09/1.00      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 2.09/1.00      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 2.09/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.09/1.00      inference(predicate_to_equality,[status(thm)],[c_5704]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_6,plain,
% 2.09/1.00      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 2.09/1.00      | ~ m1_pre_topc(X0,X1)
% 2.09/1.00      | ~ l1_pre_topc(X1) ),
% 2.09/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_18,plain,
% 2.09/1.00      ( ~ r1_tarski(X0,X1)
% 2.09/1.00      | v1_xboole_0(X0)
% 2.09/1.00      | v1_xboole_0(X1)
% 2.09/1.00      | ~ v1_zfmisc_1(X1)
% 2.09/1.00      | X1 = X0 ),
% 2.09/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_441,plain,
% 2.09/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.09/1.00      | ~ l1_pre_topc(X1)
% 2.09/1.00      | v1_xboole_0(X2)
% 2.09/1.00      | v1_xboole_0(X3)
% 2.09/1.00      | ~ v1_zfmisc_1(X3)
% 2.09/1.00      | X3 = X2
% 2.09/1.00      | u1_struct_0(X0) != X2
% 2.09/1.00      | u1_struct_0(X1) != X3 ),
% 2.09/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_18]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_442,plain,
% 2.09/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.09/1.00      | ~ l1_pre_topc(X1)
% 2.09/1.00      | v1_xboole_0(u1_struct_0(X0))
% 2.09/1.00      | v1_xboole_0(u1_struct_0(X1))
% 2.09/1.00      | ~ v1_zfmisc_1(u1_struct_0(X1))
% 2.09/1.00      | u1_struct_0(X1) = u1_struct_0(X0) ),
% 2.09/1.00      inference(unflattening,[status(thm)],[c_441]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_4829,plain,
% 2.09/1.00      ( ~ m1_pre_topc(X0_48,X1_48)
% 2.09/1.00      | ~ l1_pre_topc(X1_48)
% 2.09/1.00      | v1_xboole_0(u1_struct_0(X0_48))
% 2.09/1.00      | v1_xboole_0(u1_struct_0(X1_48))
% 2.09/1.00      | ~ v1_zfmisc_1(u1_struct_0(X1_48))
% 2.09/1.00      | u1_struct_0(X1_48) = u1_struct_0(X0_48) ),
% 2.09/1.00      inference(subtyping,[status(esa)],[c_442]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_5810,plain,
% 2.09/1.00      ( ~ m1_pre_topc(k1_tex_2(X0_48,X0_47),X1_48)
% 2.09/1.00      | ~ l1_pre_topc(X1_48)
% 2.09/1.00      | v1_xboole_0(u1_struct_0(X1_48))
% 2.09/1.00      | v1_xboole_0(u1_struct_0(k1_tex_2(X0_48,X0_47)))
% 2.09/1.00      | ~ v1_zfmisc_1(u1_struct_0(X1_48))
% 2.09/1.00      | u1_struct_0(X1_48) = u1_struct_0(k1_tex_2(X0_48,X0_47)) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_4829]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_5815,plain,
% 2.09/1.00      ( u1_struct_0(X0_48) = u1_struct_0(k1_tex_2(X1_48,X0_47))
% 2.09/1.00      | m1_pre_topc(k1_tex_2(X1_48,X0_47),X0_48) != iProver_top
% 2.09/1.00      | l1_pre_topc(X0_48) != iProver_top
% 2.09/1.00      | v1_xboole_0(u1_struct_0(X0_48)) = iProver_top
% 2.09/1.00      | v1_xboole_0(u1_struct_0(k1_tex_2(X1_48,X0_47))) = iProver_top
% 2.09/1.00      | v1_zfmisc_1(u1_struct_0(X0_48)) != iProver_top ),
% 2.09/1.00      inference(predicate_to_equality,[status(thm)],[c_5810]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_5817,plain,
% 2.09/1.00      ( u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK1,sK2))
% 2.09/1.00      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 2.09/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.09/1.00      | v1_xboole_0(u1_struct_0(k1_tex_2(sK1,sK2))) = iProver_top
% 2.09/1.00      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top
% 2.09/1.00      | v1_zfmisc_1(u1_struct_0(sK1)) != iProver_top ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_5815]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_393,plain,
% 2.09/1.00      ( v2_struct_0(X0)
% 2.09/1.00      | ~ l1_pre_topc(X0)
% 2.09/1.00      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.09/1.00      inference(resolution,[status(thm)],[c_1,c_3]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_4830,plain,
% 2.09/1.00      ( v2_struct_0(X0_48)
% 2.09/1.00      | ~ l1_pre_topc(X0_48)
% 2.09/1.00      | ~ v1_xboole_0(u1_struct_0(X0_48)) ),
% 2.09/1.00      inference(subtyping,[status(esa)],[c_393]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_5857,plain,
% 2.09/1.00      ( v2_struct_0(k1_tex_2(sK1,sK2))
% 2.09/1.00      | ~ l1_pre_topc(k1_tex_2(sK1,sK2))
% 2.09/1.00      | ~ v1_xboole_0(u1_struct_0(k1_tex_2(sK1,sK2))) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_4830]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_5858,plain,
% 2.09/1.00      ( v2_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
% 2.09/1.00      | l1_pre_topc(k1_tex_2(sK1,sK2)) != iProver_top
% 2.09/1.00      | v1_xboole_0(u1_struct_0(k1_tex_2(sK1,sK2))) != iProver_top ),
% 2.09/1.00      inference(predicate_to_equality,[status(thm)],[c_5857]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_5489,plain,
% 2.09/1.00      ( m1_subset_1(X0_47,u1_struct_0(X0_48)) != iProver_top
% 2.09/1.00      | m1_pre_topc(k1_tex_2(X0_48,X0_47),X0_48) = iProver_top
% 2.09/1.00      | v2_struct_0(X0_48) = iProver_top
% 2.09/1.00      | l1_pre_topc(X0_48) != iProver_top ),
% 2.09/1.00      inference(predicate_to_equality,[status(thm)],[c_4840]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_2,plain,
% 2.09/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.09/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_4848,plain,
% 2.09/1.00      ( ~ m1_pre_topc(X0_48,X1_48)
% 2.09/1.00      | ~ l1_pre_topc(X1_48)
% 2.09/1.00      | l1_pre_topc(X0_48) ),
% 2.09/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_5481,plain,
% 2.09/1.00      ( m1_pre_topc(X0_48,X1_48) != iProver_top
% 2.09/1.00      | l1_pre_topc(X1_48) != iProver_top
% 2.09/1.00      | l1_pre_topc(X0_48) = iProver_top ),
% 2.09/1.00      inference(predicate_to_equality,[status(thm)],[c_4848]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_5914,plain,
% 2.09/1.00      ( m1_subset_1(X0_47,u1_struct_0(X0_48)) != iProver_top
% 2.09/1.00      | v2_struct_0(X0_48) = iProver_top
% 2.09/1.00      | l1_pre_topc(X0_48) != iProver_top
% 2.09/1.00      | l1_pre_topc(k1_tex_2(X0_48,X0_47)) = iProver_top ),
% 2.09/1.00      inference(superposition,[status(thm)],[c_5489,c_5481]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_5935,plain,
% 2.09/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.09/1.00      | v2_struct_0(sK1) = iProver_top
% 2.09/1.00      | l1_pre_topc(k1_tex_2(sK1,sK2)) = iProver_top
% 2.09/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_5914]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_5883,plain,
% 2.09/1.00      ( u1_struct_0(k1_tex_2(sK1,sK2)) != u1_struct_0(X0_48)
% 2.09/1.00      | u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
% 2.09/1.00      | u1_struct_0(sK1) != u1_struct_0(X0_48) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_5777]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_6095,plain,
% 2.09/1.00      ( u1_struct_0(k1_tex_2(sK1,sK2)) != u1_struct_0(k1_tex_2(sK1,sK2))
% 2.09/1.00      | u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
% 2.09/1.00      | u1_struct_0(sK1) != u1_struct_0(k1_tex_2(sK1,sK2)) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_5883]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_4851,plain,( X0_47 = X0_47 ),theory(equality) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_6096,plain,
% 2.09/1.00      ( u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_4851]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_6100,plain,
% 2.09/1.00      ( v1_subset_1(k2_tarski(sK2,sK2),u1_struct_0(sK1)) = iProver_top ),
% 2.09/1.00      inference(global_propositional_subsumption,
% 2.09/1.00                [status(thm)],
% 2.09/1.00                [c_6020,c_26,c_27,c_28,c_82,c_86,c_2843,c_4900,c_4903,
% 2.09/1.00                 c_5705,c_5817,c_5858,c_5935,c_6095,c_6096]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_4836,negated_conjecture,
% 2.09/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.09/1.00      | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
% 2.09/1.00      inference(subtyping,[status(esa)],[c_21]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_5493,plain,
% 2.09/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
% 2.09/1.00      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
% 2.09/1.00      inference(predicate_to_equality,[status(thm)],[c_4836]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_6021,plain,
% 2.09/1.00      ( v1_subset_1(k2_tarski(sK2,sK2),u1_struct_0(sK1)) != iProver_top
% 2.09/1.00      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
% 2.09/1.00      inference(demodulation,[status(thm)],[c_6017,c_5493]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_5934,plain,
% 2.09/1.00      ( ~ m1_subset_1(X0_47,u1_struct_0(X0_48))
% 2.09/1.00      | v2_struct_0(X0_48)
% 2.09/1.00      | ~ l1_pre_topc(X0_48)
% 2.09/1.00      | l1_pre_topc(k1_tex_2(X0_48,X0_47)) ),
% 2.09/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_5914]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_5936,plain,
% 2.09/1.00      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.09/1.00      | v2_struct_0(sK1)
% 2.09/1.00      | l1_pre_topc(k1_tex_2(sK1,sK2))
% 2.09/1.00      | ~ l1_pre_topc(sK1) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_5934]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_5816,plain,
% 2.09/1.00      ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.09/1.00      | ~ l1_pre_topc(sK1)
% 2.09/1.00      | v1_xboole_0(u1_struct_0(k1_tex_2(sK1,sK2)))
% 2.09/1.00      | v1_xboole_0(u1_struct_0(sK1))
% 2.09/1.00      | ~ v1_zfmisc_1(u1_struct_0(sK1))
% 2.09/1.00      | u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_5810]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_4854,plain,
% 2.09/1.00      ( ~ v1_zfmisc_1(X0_47) | v1_zfmisc_1(X1_47) | X1_47 != X0_47 ),
% 2.09/1.00      theory(equality) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_5751,plain,
% 2.09/1.00      ( v1_zfmisc_1(X0_47)
% 2.09/1.00      | ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_48,X1_47)))
% 2.09/1.00      | X0_47 != u1_struct_0(k1_tex_2(X0_48,X1_47)) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_4854]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_5809,plain,
% 2.09/1.00      ( v1_zfmisc_1(u1_struct_0(X0_48))
% 2.09/1.00      | ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(X1_48,X0_47)))
% 2.09/1.00      | u1_struct_0(X0_48) != u1_struct_0(k1_tex_2(X1_48,X0_47)) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_5751]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_5811,plain,
% 2.09/1.00      ( u1_struct_0(X0_48) != u1_struct_0(k1_tex_2(X1_48,X0_47))
% 2.09/1.00      | v1_zfmisc_1(u1_struct_0(X0_48)) = iProver_top
% 2.09/1.00      | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1_48,X0_47))) != iProver_top ),
% 2.09/1.00      inference(predicate_to_equality,[status(thm)],[c_5809]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_5813,plain,
% 2.09/1.00      ( u1_struct_0(sK1) != u1_struct_0(k1_tex_2(sK1,sK2))
% 2.09/1.00      | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK1,sK2))) != iProver_top
% 2.09/1.00      | v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_5811]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_8,plain,
% 2.09/1.00      ( v1_tex_2(X0,X1)
% 2.09/1.00      | ~ m1_pre_topc(X0,X1)
% 2.09/1.00      | ~ l1_pre_topc(X1)
% 2.09/1.00      | sK0(X1,X0) = u1_struct_0(X0) ),
% 2.09/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_4845,plain,
% 2.09/1.00      ( v1_tex_2(X0_48,X1_48)
% 2.09/1.00      | ~ m1_pre_topc(X0_48,X1_48)
% 2.09/1.00      | ~ l1_pre_topc(X1_48)
% 2.09/1.00      | sK0(X1_48,X0_48) = u1_struct_0(X0_48) ),
% 2.09/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_5720,plain,
% 2.09/1.00      ( v1_tex_2(k1_tex_2(X0_48,X0_47),X0_48)
% 2.09/1.00      | ~ m1_pre_topc(k1_tex_2(X0_48,X0_47),X0_48)
% 2.09/1.00      | ~ l1_pre_topc(X0_48)
% 2.09/1.00      | sK0(X0_48,k1_tex_2(X0_48,X0_47)) = u1_struct_0(k1_tex_2(X0_48,X0_47)) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_4845]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_5721,plain,
% 2.09/1.00      ( sK0(X0_48,k1_tex_2(X0_48,X0_47)) = u1_struct_0(k1_tex_2(X0_48,X0_47))
% 2.09/1.00      | v1_tex_2(k1_tex_2(X0_48,X0_47),X0_48) = iProver_top
% 2.09/1.00      | m1_pre_topc(k1_tex_2(X0_48,X0_47),X0_48) != iProver_top
% 2.09/1.00      | l1_pre_topc(X0_48) != iProver_top ),
% 2.09/1.00      inference(predicate_to_equality,[status(thm)],[c_5720]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_5723,plain,
% 2.09/1.00      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2))
% 2.09/1.00      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) = iProver_top
% 2.09/1.00      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 2.09/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_5721]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_4,plain,
% 2.09/1.00      ( ~ v7_struct_0(X0)
% 2.09/1.00      | ~ l1_struct_0(X0)
% 2.09/1.00      | v1_zfmisc_1(u1_struct_0(X0)) ),
% 2.09/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_379,plain,
% 2.09/1.00      ( ~ v7_struct_0(X0)
% 2.09/1.00      | ~ l1_pre_topc(X0)
% 2.09/1.00      | v1_zfmisc_1(u1_struct_0(X0)) ),
% 2.09/1.00      inference(resolution,[status(thm)],[c_1,c_4]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_15,plain,
% 2.09/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.09/1.00      | v7_struct_0(k1_tex_2(X1,X0))
% 2.09/1.00      | v2_struct_0(X1)
% 2.09/1.00      | ~ l1_pre_topc(X1) ),
% 2.09/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_2041,plain,
% 2.09/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.09/1.00      | v2_struct_0(X1)
% 2.09/1.00      | ~ l1_pre_topc(X2)
% 2.09/1.00      | ~ l1_pre_topc(X1)
% 2.09/1.00      | v1_zfmisc_1(u1_struct_0(X2))
% 2.09/1.00      | k1_tex_2(X1,X0) != X2 ),
% 2.09/1.00      inference(resolution_lifted,[status(thm)],[c_379,c_15]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_2042,plain,
% 2.09/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.09/1.00      | v2_struct_0(X1)
% 2.09/1.00      | ~ l1_pre_topc(X1)
% 2.09/1.00      | ~ l1_pre_topc(k1_tex_2(X1,X0))
% 2.09/1.00      | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1,X0))) ),
% 2.09/1.00      inference(unflattening,[status(thm)],[c_2041]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_415,plain,
% 2.09/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.09/1.00      | v2_struct_0(X1)
% 2.09/1.00      | ~ l1_pre_topc(X2)
% 2.09/1.00      | ~ l1_pre_topc(X1)
% 2.09/1.00      | v1_zfmisc_1(u1_struct_0(X2))
% 2.09/1.00      | k1_tex_2(X1,X0) != X2 ),
% 2.09/1.00      inference(resolution_lifted,[status(thm)],[c_379,c_15]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_416,plain,
% 2.09/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.09/1.00      | v2_struct_0(X1)
% 2.09/1.00      | ~ l1_pre_topc(X1)
% 2.09/1.00      | ~ l1_pre_topc(k1_tex_2(X1,X0))
% 2.09/1.00      | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1,X0))) ),
% 2.09/1.00      inference(unflattening,[status(thm)],[c_415]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_730,plain,
% 2.09/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.09/1.00      | v2_struct_0(X1)
% 2.09/1.00      | ~ l1_pre_topc(X2)
% 2.09/1.00      | ~ l1_pre_topc(X1)
% 2.09/1.00      | l1_pre_topc(X3)
% 2.09/1.00      | X1 != X2
% 2.09/1.00      | k1_tex_2(X1,X0) != X3 ),
% 2.09/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_13]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_731,plain,
% 2.09/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.09/1.00      | v2_struct_0(X1)
% 2.09/1.00      | ~ l1_pre_topc(X1)
% 2.09/1.00      | l1_pre_topc(k1_tex_2(X1,X0)) ),
% 2.09/1.00      inference(unflattening,[status(thm)],[c_730]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_2044,plain,
% 2.09/1.00      ( ~ l1_pre_topc(X1)
% 2.09/1.00      | v2_struct_0(X1)
% 2.09/1.00      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.09/1.00      | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1,X0))) ),
% 2.09/1.00      inference(global_propositional_subsumption,
% 2.09/1.00                [status(thm)],
% 2.09/1.00                [c_2042,c_416,c_731]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_2045,plain,
% 2.09/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.09/1.00      | v2_struct_0(X1)
% 2.09/1.00      | ~ l1_pre_topc(X1)
% 2.09/1.00      | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1,X0))) ),
% 2.09/1.00      inference(renaming,[status(thm)],[c_2044]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_4828,plain,
% 2.09/1.00      ( ~ m1_subset_1(X0_47,u1_struct_0(X0_48))
% 2.09/1.00      | v2_struct_0(X0_48)
% 2.09/1.00      | ~ l1_pre_topc(X0_48)
% 2.09/1.00      | v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_48,X0_47))) ),
% 2.09/1.00      inference(subtyping,[status(esa)],[c_2045]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_4922,plain,
% 2.09/1.00      ( m1_subset_1(X0_47,u1_struct_0(X0_48)) != iProver_top
% 2.09/1.00      | v2_struct_0(X0_48) = iProver_top
% 2.09/1.00      | l1_pre_topc(X0_48) != iProver_top
% 2.09/1.00      | v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_48,X0_47))) = iProver_top ),
% 2.09/1.00      inference(predicate_to_equality,[status(thm)],[c_4828]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_4924,plain,
% 2.09/1.00      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.09/1.00      | v2_struct_0(sK1) = iProver_top
% 2.09/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.09/1.00      | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK1,sK2))) = iProver_top ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_4922]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_4902,plain,
% 2.09/1.00      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.09/1.00      | ~ v2_struct_0(k1_tex_2(sK1,sK2))
% 2.09/1.00      | v2_struct_0(sK1)
% 2.09/1.00      | ~ l1_pre_topc(sK1) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_4839]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_4899,plain,
% 2.09/1.00      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 2.09/1.00      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.09/1.00      | v2_struct_0(sK1)
% 2.09/1.00      | ~ l1_pre_topc(sK1) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_4840]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_4852,plain,( X0_48 = X0_48 ),theory(equality) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_4880,plain,
% 2.09/1.00      ( sK1 = sK1 ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_4852]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_4858,plain,
% 2.09/1.00      ( X0_48 != X1_48 | u1_struct_0(X0_48) = u1_struct_0(X1_48) ),
% 2.09/1.00      theory(equality) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_4870,plain,
% 2.09/1.00      ( sK1 != sK1 | u1_struct_0(sK1) = u1_struct_0(sK1) ),
% 2.09/1.00      inference(instantiation,[status(thm)],[c_4858]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_19,plain,
% 2.09/1.00      ( ~ v1_subset_1(k6_domain_1(X0,X1),X0)
% 2.09/1.00      | ~ m1_subset_1(X1,X0)
% 2.09/1.00      | v1_xboole_0(X0)
% 2.09/1.00      | ~ v1_zfmisc_1(X0) ),
% 2.09/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_1903,plain,
% 2.09/1.00      ( v1_tex_2(k1_tex_2(sK1,sK2),sK1)
% 2.09/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
% 2.09/1.00      inference(prop_impl,[status(thm)],[c_22]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_1904,plain,
% 2.09/1.00      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.09/1.00      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
% 2.09/1.00      inference(renaming,[status(thm)],[c_1903]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_2852,plain,
% 2.09/1.00      ( v1_tex_2(k1_tex_2(sK1,sK2),sK1)
% 2.09/1.00      | ~ m1_subset_1(X0,X1)
% 2.09/1.00      | v1_xboole_0(X1)
% 2.09/1.00      | ~ v1_zfmisc_1(X1)
% 2.09/1.00      | k6_domain_1(u1_struct_0(sK1),sK2) != k6_domain_1(X1,X0)
% 2.09/1.00      | u1_struct_0(sK1) != X1 ),
% 2.09/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_1904]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_2853,plain,
% 2.09/1.00      ( v1_tex_2(k1_tex_2(sK1,sK2),sK1)
% 2.09/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.09/1.00      | v1_xboole_0(u1_struct_0(sK1))
% 2.09/1.00      | ~ v1_zfmisc_1(u1_struct_0(sK1))
% 2.09/1.00      | k6_domain_1(u1_struct_0(sK1),sK2) != k6_domain_1(u1_struct_0(sK1),X0) ),
% 2.09/1.00      inference(unflattening,[status(thm)],[c_2852]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_1442,plain,
% 2.09/1.00      ( ~ v1_subset_1(k6_domain_1(X0,X1),X0)
% 2.09/1.00      | v1_xboole_0(X0)
% 2.09/1.00      | ~ v1_zfmisc_1(X0)
% 2.09/1.00      | u1_struct_0(sK1) != X0
% 2.09/1.00      | sK2 != X1 ),
% 2.09/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_23]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_1443,plain,
% 2.09/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.09/1.00      | v1_xboole_0(u1_struct_0(sK1))
% 2.09/1.00      | ~ v1_zfmisc_1(u1_struct_0(sK1)) ),
% 2.09/1.00      inference(unflattening,[status(thm)],[c_1442]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_2855,plain,
% 2.09/1.00      ( ~ v1_zfmisc_1(u1_struct_0(sK1))
% 2.09/1.00      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
% 2.09/1.00      inference(global_propositional_subsumption,
% 2.09/1.00                [status(thm)],
% 2.09/1.00                [c_2853,c_25,c_24,c_22,c_81,c_85,c_1443]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_2856,plain,
% 2.09/1.00      ( v1_tex_2(k1_tex_2(sK1,sK2),sK1)
% 2.09/1.00      | ~ v1_zfmisc_1(u1_struct_0(sK1)) ),
% 2.09/1.00      inference(renaming,[status(thm)],[c_2855]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_2857,plain,
% 2.09/1.00      ( v1_tex_2(k1_tex_2(sK1,sK2),sK1) = iProver_top
% 2.09/1.00      | v1_zfmisc_1(u1_struct_0(sK1)) != iProver_top ),
% 2.09/1.00      inference(predicate_to_equality,[status(thm)],[c_2856]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_9,plain,
% 2.09/1.00      ( v1_tex_2(X0,X1)
% 2.09/1.00      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.09/1.00      | ~ m1_pre_topc(X0,X1)
% 2.09/1.00      | ~ l1_pre_topc(X1) ),
% 2.09/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_204,plain,
% 2.09/1.00      ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
% 2.09/1.00      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
% 2.09/1.00      inference(prop_impl,[status(thm)],[c_21]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_205,plain,
% 2.09/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.09/1.00      | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
% 2.09/1.00      inference(renaming,[status(thm)],[c_204]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_915,plain,
% 2.09/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.09/1.00      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 2.09/1.00      | ~ m1_pre_topc(X1,X0)
% 2.09/1.00      | ~ l1_pre_topc(X0)
% 2.09/1.00      | k1_tex_2(sK1,sK2) != X1
% 2.09/1.00      | sK1 != X0 ),
% 2.09/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_205]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_916,plain,
% 2.09/1.00      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.09/1.00      | m1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.09/1.00      | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.09/1.00      | ~ l1_pre_topc(sK1) ),
% 2.09/1.00      inference(unflattening,[status(thm)],[c_915]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_7,plain,
% 2.09/1.00      ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
% 2.09/1.00      | v1_tex_2(X1,X0)
% 2.09/1.00      | ~ m1_pre_topc(X1,X0)
% 2.09/1.00      | ~ l1_pre_topc(X0) ),
% 2.09/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_898,plain,
% 2.09/1.00      ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
% 2.09/1.00      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.09/1.00      | ~ m1_pre_topc(X1,X0)
% 2.09/1.00      | ~ l1_pre_topc(X0)
% 2.09/1.00      | k1_tex_2(sK1,sK2) != X1
% 2.09/1.00      | sK1 != X0 ),
% 2.09/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_205]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(c_899,plain,
% 2.09/1.00      ( ~ v1_subset_1(sK0(sK1,k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
% 2.09/1.00      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.09/1.00      | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.09/1.00      | ~ l1_pre_topc(sK1) ),
% 2.09/1.00      inference(unflattening,[status(thm)],[c_898]) ).
% 2.09/1.00  
% 2.09/1.00  cnf(contradiction,plain,
% 2.09/1.00      ( $false ),
% 2.09/1.00      inference(minisat,
% 2.09/1.00                [status(thm)],
% 2.09/1.00                [c_7154,c_7070,c_6700,c_6527,c_6312,c_6100,c_6096,c_6021,
% 2.09/1.00                 c_5936,c_5857,c_5816,c_5813,c_5723,c_4924,c_4902,c_4900,
% 2.09/1.00                 c_4899,c_4880,c_4870,c_2857,c_1433,c_916,c_899,c_85,
% 2.09/1.00                 c_81,c_28,c_23,c_27,c_24,c_26,c_25]) ).
% 2.09/1.00  
% 2.09/1.00  
% 2.09/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.09/1.00  
% 2.09/1.00  ------                               Statistics
% 2.09/1.00  
% 2.09/1.00  ------ General
% 2.09/1.00  
% 2.09/1.00  abstr_ref_over_cycles:                  0
% 2.09/1.00  abstr_ref_under_cycles:                 0
% 2.09/1.00  gc_basic_clause_elim:                   0
% 2.09/1.00  forced_gc_time:                         0
% 2.09/1.00  parsing_time:                           0.01
% 2.09/1.00  unif_index_cands_time:                  0.
% 2.09/1.00  unif_index_add_time:                    0.
% 2.09/1.00  orderings_time:                         0.
% 2.09/1.00  out_proof_time:                         0.012
% 2.09/1.00  total_time:                             0.188
% 2.09/1.00  num_of_symbols:                         52
% 2.09/1.00  num_of_terms:                           3372
% 2.09/1.00  
% 2.09/1.00  ------ Preprocessing
% 2.09/1.00  
% 2.09/1.00  num_of_splits:                          0
% 2.09/1.00  num_of_split_atoms:                     0
% 2.09/1.00  num_of_reused_defs:                     0
% 2.09/1.00  num_eq_ax_congr_red:                    21
% 2.09/1.00  num_of_sem_filtered_clauses:            1
% 2.09/1.00  num_of_subtypes:                        2
% 2.09/1.00  monotx_restored_types:                  1
% 2.09/1.00  sat_num_of_epr_types:                   0
% 2.09/1.00  sat_num_of_non_cyclic_types:            0
% 2.09/1.00  sat_guarded_non_collapsed_types:        0
% 2.09/1.00  num_pure_diseq_elim:                    0
% 2.09/1.00  simp_replaced_by:                       0
% 2.09/1.00  res_preprocessed:                       145
% 2.09/1.00  prep_upred:                             0
% 2.09/1.00  prep_unflattend:                        209
% 2.09/1.00  smt_new_axioms:                         0
% 2.09/1.00  pred_elim_cands:                        8
% 2.09/1.00  pred_elim:                              3
% 2.09/1.00  pred_elim_cl:                           3
% 2.09/1.00  pred_elim_cycles:                       20
% 2.09/1.00  merged_defs:                            10
% 2.09/1.00  merged_defs_ncl:                        0
% 2.09/1.00  bin_hyper_res:                          10
% 2.09/1.00  prep_cycles:                            5
% 2.09/1.00  pred_elim_time:                         0.083
% 2.09/1.00  splitting_time:                         0.
% 2.09/1.00  sem_filter_time:                        0.
% 2.09/1.00  monotx_time:                            0.
% 2.09/1.00  subtype_inf_time:                       0.001
% 2.09/1.00  
% 2.09/1.00  ------ Problem properties
% 2.09/1.00  
% 2.09/1.00  clauses:                                22
% 2.09/1.00  conjectures:                            5
% 2.09/1.00  epr:                                    4
% 2.09/1.00  horn:                                   13
% 2.09/1.00  ground:                                 5
% 2.09/1.00  unary:                                  3
% 2.09/1.00  binary:                                 4
% 2.09/1.00  lits:                                   69
% 2.09/1.00  lits_eq:                                5
% 2.09/1.00  fd_pure:                                0
% 2.09/1.00  fd_pseudo:                              0
% 2.09/1.00  fd_cond:                                0
% 2.09/1.00  fd_pseudo_cond:                         1
% 2.09/1.00  ac_symbols:                             0
% 2.09/1.00  
% 2.09/1.00  ------ Propositional Solver
% 2.09/1.00  
% 2.09/1.00  prop_solver_calls:                      31
% 2.09/1.00  prop_fast_solver_calls:                 1947
% 2.09/1.00  smt_solver_calls:                       0
% 2.09/1.00  smt_fast_solver_calls:                  0
% 2.09/1.00  prop_num_of_clauses:                    1021
% 2.09/1.00  prop_preprocess_simplified:             5882
% 2.09/1.00  prop_fo_subsumed:                       55
% 2.09/1.00  prop_solver_time:                       0.
% 2.09/1.00  smt_solver_time:                        0.
% 2.09/1.00  smt_fast_solver_time:                   0.
% 2.09/1.00  prop_fast_solver_time:                  0.
% 2.09/1.00  prop_unsat_core_time:                   0.
% 2.09/1.00  
% 2.09/1.00  ------ QBF
% 2.09/1.00  
% 2.09/1.00  qbf_q_res:                              0
% 2.09/1.00  qbf_num_tautologies:                    0
% 2.09/1.00  qbf_prep_cycles:                        0
% 2.09/1.00  
% 2.09/1.00  ------ BMC1
% 2.09/1.00  
% 2.09/1.00  bmc1_current_bound:                     -1
% 2.09/1.00  bmc1_last_solved_bound:                 -1
% 2.09/1.00  bmc1_unsat_core_size:                   -1
% 2.09/1.00  bmc1_unsat_core_parents_size:           -1
% 2.09/1.00  bmc1_merge_next_fun:                    0
% 2.09/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.09/1.00  
% 2.09/1.00  ------ Instantiation
% 2.09/1.00  
% 2.09/1.00  inst_num_of_clauses:                    269
% 2.09/1.00  inst_num_in_passive:                    47
% 2.09/1.00  inst_num_in_active:                     178
% 2.09/1.00  inst_num_in_unprocessed:                43
% 2.09/1.00  inst_num_of_loops:                      200
% 2.09/1.00  inst_num_of_learning_restarts:          0
% 2.09/1.00  inst_num_moves_active_passive:          17
% 2.09/1.00  inst_lit_activity:                      0
% 2.09/1.00  inst_lit_activity_moves:                0
% 2.09/1.00  inst_num_tautologies:                   0
% 2.09/1.00  inst_num_prop_implied:                  0
% 2.09/1.00  inst_num_existing_simplified:           0
% 2.09/1.00  inst_num_eq_res_simplified:             0
% 2.09/1.00  inst_num_child_elim:                    0
% 2.09/1.00  inst_num_of_dismatching_blockings:      134
% 2.09/1.00  inst_num_of_non_proper_insts:           300
% 2.09/1.00  inst_num_of_duplicates:                 0
% 2.09/1.00  inst_inst_num_from_inst_to_res:         0
% 2.09/1.00  inst_dismatching_checking_time:         0.
% 2.09/1.00  
% 2.09/1.00  ------ Resolution
% 2.09/1.00  
% 2.09/1.00  res_num_of_clauses:                     0
% 2.09/1.00  res_num_in_passive:                     0
% 2.09/1.00  res_num_in_active:                      0
% 2.09/1.00  res_num_of_loops:                       150
% 2.09/1.00  res_forward_subset_subsumed:            29
% 2.09/1.00  res_backward_subset_subsumed:           0
% 2.09/1.00  res_forward_subsumed:                   0
% 2.09/1.00  res_backward_subsumed:                  0
% 2.09/1.00  res_forward_subsumption_resolution:     1
% 2.09/1.00  res_backward_subsumption_resolution:    0
% 2.09/1.00  res_clause_to_clause_subsumption:       244
% 2.09/1.00  res_orphan_elimination:                 0
% 2.09/1.00  res_tautology_del:                      90
% 2.09/1.00  res_num_eq_res_simplified:              0
% 2.09/1.00  res_num_sel_changes:                    0
% 2.09/1.00  res_moves_from_active_to_pass:          0
% 2.09/1.00  
% 2.09/1.00  ------ Superposition
% 2.09/1.00  
% 2.09/1.00  sup_time_total:                         0.
% 2.09/1.00  sup_time_generating:                    0.
% 2.09/1.00  sup_time_sim_full:                      0.
% 2.09/1.00  sup_time_sim_immed:                     0.
% 2.09/1.00  
% 2.09/1.00  sup_num_of_clauses:                     39
% 2.09/1.00  sup_num_in_active:                      36
% 2.09/1.00  sup_num_in_passive:                     3
% 2.09/1.00  sup_num_of_loops:                       38
% 2.09/1.00  sup_fw_superposition:                   7
% 2.09/1.00  sup_bw_superposition:                   15
% 2.09/1.00  sup_immediate_simplified:               2
% 2.09/1.00  sup_given_eliminated:                   0
% 2.09/1.00  comparisons_done:                       0
% 2.09/1.00  comparisons_avoided:                    0
% 2.09/1.00  
% 2.09/1.00  ------ Simplifications
% 2.09/1.00  
% 2.09/1.00  
% 2.09/1.00  sim_fw_subset_subsumed:                 1
% 2.09/1.00  sim_bw_subset_subsumed:                 2
% 2.09/1.00  sim_fw_subsumed:                        1
% 2.09/1.00  sim_bw_subsumed:                        0
% 2.09/1.00  sim_fw_subsumption_res:                 0
% 2.09/1.00  sim_bw_subsumption_res:                 0
% 2.09/1.00  sim_tautology_del:                      2
% 2.09/1.00  sim_eq_tautology_del:                   1
% 2.09/1.00  sim_eq_res_simp:                        0
% 2.09/1.00  sim_fw_demodulated:                     0
% 2.09/1.00  sim_bw_demodulated:                     2
% 2.09/1.00  sim_light_normalised:                   0
% 2.09/1.00  sim_joinable_taut:                      0
% 2.09/1.00  sim_joinable_simp:                      0
% 2.09/1.00  sim_ac_normalised:                      0
% 2.09/1.00  sim_smt_subsumption:                    0
% 2.09/1.00  
%------------------------------------------------------------------------------
