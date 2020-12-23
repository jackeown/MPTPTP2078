%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:50 EST 2020

% Result     : Theorem 19.31s
% Output     : CNFRefutation 19.31s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 222 expanded)
%              Number of clauses        :   69 (  77 expanded)
%              Number of leaves         :   22 (  52 expanded)
%              Depth                    :   18
%              Number of atoms          :  384 ( 678 expanded)
%              Number of equality atoms :  144 ( 163 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f16,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f70,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f17,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
     => ( v1_zfmisc_1(X0)
        & v1_subset_1(k6_domain_1(X0,sK3),X0)
        & m1_subset_1(sK3,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_zfmisc_1(X0)
            & v1_subset_1(k6_domain_1(X0,X1),X0)
            & m1_subset_1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( v1_zfmisc_1(sK2)
          & v1_subset_1(k6_domain_1(sK2,X1),sK2)
          & m1_subset_1(X1,sK2) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( v1_zfmisc_1(sK2)
    & v1_subset_1(k6_domain_1(sK2,sK3),sK2)
    & m1_subset_1(sK3,sK2)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f37,f47,f46])).

fof(f74,plain,(
    v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f71,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f72,plain,(
    m1_subset_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f75,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X1,X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f69,f75])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f52,f75])).

fof(f81,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_enumset1(X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f78])).

fof(f82,plain,(
    ! [X3] : r2_hidden(X3,k1_enumset1(X3,X3,X3)) ),
    inference(equality_resolution,[],[f81])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f49,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f60,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f64,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f61,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f63,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f73,plain,(
    v1_subset_1(k6_domain_1(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1161,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_95840,plain,
    ( k6_domain_1(sK2,sK3) != X0
    | k6_domain_1(sK2,sK3) = u1_struct_0(g1_pre_topc(X1,k1_xboole_0))
    | u1_struct_0(g1_pre_topc(X1,k1_xboole_0)) != X0 ),
    inference(instantiation,[status(thm)],[c_1161])).

cnf(c_95846,plain,
    ( k6_domain_1(sK2,sK3) = u1_struct_0(g1_pre_topc(sK2,k1_xboole_0))
    | k6_domain_1(sK2,sK3) != sK2
    | u1_struct_0(g1_pre_topc(sK2,k1_xboole_0)) != sK2 ),
    inference(instantiation,[status(thm)],[c_95840])).

cnf(c_4429,plain,
    ( X0 != X1
    | X0 = k6_domain_1(sK2,sK3)
    | k6_domain_1(sK2,sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_1161])).

cnf(c_13092,plain,
    ( k6_domain_1(sK2,sK3) != X0
    | k2_struct_0(g1_pre_topc(X1,k1_xboole_0)) != X0
    | k2_struct_0(g1_pre_topc(X1,k1_xboole_0)) = k6_domain_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_4429])).

cnf(c_19346,plain,
    ( k6_domain_1(sK2,sK3) != u1_struct_0(g1_pre_topc(X0,k1_xboole_0))
    | k2_struct_0(g1_pre_topc(X0,k1_xboole_0)) = k6_domain_1(sK2,sK3)
    | k2_struct_0(g1_pre_topc(X0,k1_xboole_0)) != u1_struct_0(g1_pre_topc(X0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_13092])).

cnf(c_19347,plain,
    ( k6_domain_1(sK2,sK3) != u1_struct_0(g1_pre_topc(sK2,k1_xboole_0))
    | k2_struct_0(g1_pre_topc(sK2,k1_xboole_0)) = k6_domain_1(sK2,sK3)
    | k2_struct_0(g1_pre_topc(sK2,k1_xboole_0)) != u1_struct_0(g1_pre_topc(sK2,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_19346])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1602,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_19,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_20,negated_conjecture,
    ( v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_356,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_20])).

cnf(c_357,plain,
    ( ~ r1_tarski(X0,sK2)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | sK2 = X0 ),
    inference(unflattening,[status(thm)],[c_356])).

cnf(c_23,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_361,plain,
    ( v1_xboole_0(X0)
    | ~ r1_tarski(X0,sK2)
    | sK2 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_357,c_23])).

cnf(c_362,plain,
    ( ~ r1_tarski(X0,sK2)
    | v1_xboole_0(X0)
    | sK2 = X0 ),
    inference(renaming,[status(thm)],[c_361])).

cnf(c_379,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(X2)
    | X2 != X0
    | sK2 != X1
    | sK2 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_362])).

cnf(c_380,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
    | v1_xboole_0(X0)
    | sK2 = X0 ),
    inference(unflattening,[status(thm)],[c_379])).

cnf(c_1595,plain,
    ( sK2 = X0
    | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_380])).

cnf(c_3370,plain,
    ( k6_domain_1(sK2,X0) = sK2
    | m1_subset_1(X0,sK2) != iProver_top
    | v1_xboole_0(k6_domain_1(sK2,X0)) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1602,c_1595])).

cnf(c_24,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4167,plain,
    ( v1_xboole_0(k6_domain_1(sK2,X0)) = iProver_top
    | m1_subset_1(X0,sK2) != iProver_top
    | k6_domain_1(sK2,X0) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3370,c_24])).

cnf(c_4168,plain,
    ( k6_domain_1(sK2,X0) = sK2
    | m1_subset_1(X0,sK2) != iProver_top
    | v1_xboole_0(k6_domain_1(sK2,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4167])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1599,plain,
    ( m1_subset_1(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1601,plain,
    ( k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0)
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3184,plain,
    ( k1_enumset1(sK3,sK3,sK3) = k6_domain_1(sK2,sK3)
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1599,c_1601])).

cnf(c_1827,plain,
    ( ~ m1_subset_1(sK3,sK2)
    | v1_xboole_0(sK2)
    | k1_enumset1(sK3,sK3,sK3) = k6_domain_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_3872,plain,
    ( k1_enumset1(sK3,sK3,sK3) = k6_domain_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3184,c_23,c_22,c_1827])).

cnf(c_4,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1611,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1614,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2265,plain,
    ( v1_xboole_0(k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1611,c_1614])).

cnf(c_3875,plain,
    ( v1_xboole_0(k6_domain_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3872,c_2265])).

cnf(c_4176,plain,
    ( k6_domain_1(sK2,sK3) = sK2
    | m1_subset_1(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4168,c_3875])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2509,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(X1,k1_xboole_0)),X2) != g1_pre_topc(sK2,X0)
    | u1_struct_0(g1_pre_topc(X1,k1_xboole_0)) = sK2 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_4107,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(sK2,k1_xboole_0)),u1_pre_topc(g1_pre_topc(sK2,k1_xboole_0))) != g1_pre_topc(sK2,k1_xboole_0)
    | u1_struct_0(g1_pre_topc(sK2,k1_xboole_0)) = sK2 ),
    inference(instantiation,[status(thm)],[c_2509])).

cnf(c_1169,plain,
    ( ~ v1_subset_1(X0,X1)
    | v1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1840,plain,
    ( v1_subset_1(X0,X1)
    | ~ v1_subset_1(k6_domain_1(sK2,sK3),sK2)
    | X0 != k6_domain_1(sK2,sK3)
    | X1 != sK2 ),
    inference(instantiation,[status(thm)],[c_1169])).

cnf(c_2251,plain,
    ( ~ v1_subset_1(k6_domain_1(sK2,sK3),sK2)
    | v1_subset_1(k2_struct_0(g1_pre_topc(X0,k1_xboole_0)),u1_struct_0(g1_pre_topc(X0,k1_xboole_0)))
    | k2_struct_0(g1_pre_topc(X0,k1_xboole_0)) != k6_domain_1(sK2,sK3)
    | u1_struct_0(g1_pre_topc(X0,k1_xboole_0)) != sK2 ),
    inference(instantiation,[status(thm)],[c_1840])).

cnf(c_2253,plain,
    ( ~ v1_subset_1(k6_domain_1(sK2,sK3),sK2)
    | v1_subset_1(k2_struct_0(g1_pre_topc(sK2,k1_xboole_0)),u1_struct_0(g1_pre_topc(sK2,k1_xboole_0)))
    | k2_struct_0(g1_pre_topc(sK2,k1_xboole_0)) != k6_domain_1(sK2,sK3)
    | u1_struct_0(g1_pre_topc(sK2,k1_xboole_0)) != sK2 ),
    inference(instantiation,[status(thm)],[c_2251])).

cnf(c_9,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2241,plain,
    ( ~ l1_pre_topc(g1_pre_topc(X0,k1_xboole_0))
    | ~ v1_pre_topc(g1_pre_topc(X0,k1_xboole_0))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(X0,k1_xboole_0)),u1_pre_topc(g1_pre_topc(X0,k1_xboole_0))) = g1_pre_topc(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2248,plain,
    ( ~ l1_pre_topc(g1_pre_topc(sK2,k1_xboole_0))
    | ~ v1_pre_topc(g1_pre_topc(sK2,k1_xboole_0))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(sK2,k1_xboole_0)),u1_pre_topc(g1_pre_topc(sK2,k1_xboole_0))) = g1_pre_topc(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2241])).

cnf(c_13,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_10,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_322,plain,
    ( ~ l1_pre_topc(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_13,c_10])).

cnf(c_2030,plain,
    ( ~ l1_pre_topc(g1_pre_topc(X0,k1_xboole_0))
    | k2_struct_0(g1_pre_topc(X0,k1_xboole_0)) = u1_struct_0(g1_pre_topc(X0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_322])).

cnf(c_2037,plain,
    ( ~ l1_pre_topc(g1_pre_topc(sK2,k1_xboole_0))
    | k2_struct_0(g1_pre_topc(sK2,k1_xboole_0)) = u1_struct_0(g1_pre_topc(sK2,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_2030])).

cnf(c_14,plain,
    ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_311,plain,
    ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_13,c_14])).

cnf(c_2031,plain,
    ( ~ v1_subset_1(k2_struct_0(g1_pre_topc(X0,k1_xboole_0)),u1_struct_0(g1_pre_topc(X0,k1_xboole_0)))
    | ~ l1_pre_topc(g1_pre_topc(X0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_311])).

cnf(c_2033,plain,
    ( ~ v1_subset_1(k2_struct_0(g1_pre_topc(sK2,k1_xboole_0)),u1_struct_0(g1_pre_topc(sK2,k1_xboole_0)))
    | ~ l1_pre_topc(g1_pre_topc(sK2,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_2031])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | v1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1902,plain,
    ( v1_pre_topc(g1_pre_topc(X0,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_12,c_6])).

cnf(c_1904,plain,
    ( v1_pre_topc(g1_pre_topc(sK2,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1902])).

cnf(c_1775,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1781,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_1775])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1774,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | l1_pre_topc(g1_pre_topc(X0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1777,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | l1_pre_topc(g1_pre_topc(sK2,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1774])).

cnf(c_21,negated_conjecture,
    ( v1_subset_1(k6_domain_1(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_25,plain,
    ( m1_subset_1(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_95846,c_19347,c_4176,c_4107,c_2253,c_2248,c_2037,c_2033,c_1904,c_1781,c_1777,c_21,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:09:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 19.31/3.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.31/3.03  
% 19.31/3.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.31/3.03  
% 19.31/3.03  ------  iProver source info
% 19.31/3.03  
% 19.31/3.03  git: date: 2020-06-30 10:37:57 +0100
% 19.31/3.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.31/3.03  git: non_committed_changes: false
% 19.31/3.03  git: last_make_outside_of_git: false
% 19.31/3.03  
% 19.31/3.03  ------ 
% 19.31/3.03  ------ Parsing...
% 19.31/3.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.31/3.03  
% 19.31/3.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 19.31/3.03  
% 19.31/3.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.31/3.03  
% 19.31/3.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.31/3.03  ------ Proving...
% 19.31/3.03  ------ Problem Properties 
% 19.31/3.03  
% 19.31/3.03  
% 19.31/3.03  clauses                                 21
% 19.31/3.03  conjectures                             3
% 19.31/3.03  EPR                                     3
% 19.31/3.03  Horn                                    16
% 19.31/3.03  unary                                   5
% 19.31/3.03  binary                                  7
% 19.31/3.03  lits                                    46
% 19.31/3.03  lits eq                                 13
% 19.31/3.03  fd_pure                                 0
% 19.31/3.03  fd_pseudo                               0
% 19.31/3.03  fd_cond                                 1
% 19.31/3.03  fd_pseudo_cond                          4
% 19.31/3.03  AC symbols                              0
% 19.31/3.03  
% 19.31/3.03  ------ Input Options Time Limit: Unbounded
% 19.31/3.03  
% 19.31/3.03  
% 19.31/3.03  ------ 
% 19.31/3.03  Current options:
% 19.31/3.03  ------ 
% 19.31/3.03  
% 19.31/3.03  
% 19.31/3.03  
% 19.31/3.03  
% 19.31/3.03  ------ Proving...
% 19.31/3.03  
% 19.31/3.03  
% 19.31/3.03  % SZS status Theorem for theBenchmark.p
% 19.31/3.03  
% 19.31/3.03  % SZS output start CNFRefutation for theBenchmark.p
% 19.31/3.03  
% 19.31/3.03  fof(f14,axiom,(
% 19.31/3.03    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 19.31/3.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.31/3.03  
% 19.31/3.03  fof(f30,plain,(
% 19.31/3.03    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 19.31/3.03    inference(ennf_transformation,[],[f14])).
% 19.31/3.03  
% 19.31/3.03  fof(f31,plain,(
% 19.31/3.03    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 19.31/3.03    inference(flattening,[],[f30])).
% 19.31/3.03  
% 19.31/3.03  fof(f68,plain,(
% 19.31/3.03    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 19.31/3.03    inference(cnf_transformation,[],[f31])).
% 19.31/3.03  
% 19.31/3.03  fof(f6,axiom,(
% 19.31/3.03    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 19.31/3.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.31/3.03  
% 19.31/3.03  fof(f19,plain,(
% 19.31/3.03    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 19.31/3.03    inference(unused_predicate_definition_removal,[],[f6])).
% 19.31/3.03  
% 19.31/3.03  fof(f20,plain,(
% 19.31/3.03    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 19.31/3.03    inference(ennf_transformation,[],[f19])).
% 19.31/3.03  
% 19.31/3.03  fof(f58,plain,(
% 19.31/3.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 19.31/3.03    inference(cnf_transformation,[],[f20])).
% 19.31/3.03  
% 19.31/3.03  fof(f16,axiom,(
% 19.31/3.03    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 19.31/3.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.31/3.03  
% 19.31/3.03  fof(f34,plain,(
% 19.31/3.03    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 19.31/3.03    inference(ennf_transformation,[],[f16])).
% 19.31/3.03  
% 19.31/3.03  fof(f35,plain,(
% 19.31/3.03    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 19.31/3.03    inference(flattening,[],[f34])).
% 19.31/3.03  
% 19.31/3.03  fof(f70,plain,(
% 19.31/3.03    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 19.31/3.03    inference(cnf_transformation,[],[f35])).
% 19.31/3.03  
% 19.31/3.03  fof(f17,conjecture,(
% 19.31/3.03    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 19.31/3.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.31/3.03  
% 19.31/3.03  fof(f18,negated_conjecture,(
% 19.31/3.03    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 19.31/3.03    inference(negated_conjecture,[],[f17])).
% 19.31/3.03  
% 19.31/3.03  fof(f36,plain,(
% 19.31/3.03    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 19.31/3.03    inference(ennf_transformation,[],[f18])).
% 19.31/3.03  
% 19.31/3.03  fof(f37,plain,(
% 19.31/3.03    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 19.31/3.03    inference(flattening,[],[f36])).
% 19.31/3.03  
% 19.31/3.03  fof(f47,plain,(
% 19.31/3.03    ( ! [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) => (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,sK3),X0) & m1_subset_1(sK3,X0))) )),
% 19.31/3.03    introduced(choice_axiom,[])).
% 19.31/3.03  
% 19.31/3.03  fof(f46,plain,(
% 19.31/3.03    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK2) & v1_subset_1(k6_domain_1(sK2,X1),sK2) & m1_subset_1(X1,sK2)) & ~v1_xboole_0(sK2))),
% 19.31/3.03    introduced(choice_axiom,[])).
% 19.31/3.03  
% 19.31/3.03  fof(f48,plain,(
% 19.31/3.03    (v1_zfmisc_1(sK2) & v1_subset_1(k6_domain_1(sK2,sK3),sK2) & m1_subset_1(sK3,sK2)) & ~v1_xboole_0(sK2)),
% 19.31/3.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f37,f47,f46])).
% 19.31/3.03  
% 19.31/3.03  fof(f74,plain,(
% 19.31/3.03    v1_zfmisc_1(sK2)),
% 19.31/3.03    inference(cnf_transformation,[],[f48])).
% 19.31/3.03  
% 19.31/3.03  fof(f71,plain,(
% 19.31/3.03    ~v1_xboole_0(sK2)),
% 19.31/3.03    inference(cnf_transformation,[],[f48])).
% 19.31/3.03  
% 19.31/3.03  fof(f72,plain,(
% 19.31/3.03    m1_subset_1(sK3,sK2)),
% 19.31/3.03    inference(cnf_transformation,[],[f48])).
% 19.31/3.03  
% 19.31/3.03  fof(f15,axiom,(
% 19.31/3.03    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 19.31/3.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.31/3.03  
% 19.31/3.03  fof(f32,plain,(
% 19.31/3.03    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 19.31/3.03    inference(ennf_transformation,[],[f15])).
% 19.31/3.03  
% 19.31/3.03  fof(f33,plain,(
% 19.31/3.03    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 19.31/3.03    inference(flattening,[],[f32])).
% 19.31/3.03  
% 19.31/3.03  fof(f69,plain,(
% 19.31/3.03    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 19.31/3.03    inference(cnf_transformation,[],[f33])).
% 19.31/3.03  
% 19.31/3.03  fof(f3,axiom,(
% 19.31/3.03    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 19.31/3.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.31/3.03  
% 19.31/3.03  fof(f55,plain,(
% 19.31/3.03    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 19.31/3.03    inference(cnf_transformation,[],[f3])).
% 19.31/3.03  
% 19.31/3.03  fof(f4,axiom,(
% 19.31/3.03    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 19.31/3.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.31/3.03  
% 19.31/3.03  fof(f56,plain,(
% 19.31/3.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 19.31/3.03    inference(cnf_transformation,[],[f4])).
% 19.31/3.03  
% 19.31/3.03  fof(f75,plain,(
% 19.31/3.03    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 19.31/3.03    inference(definition_unfolding,[],[f55,f56])).
% 19.31/3.03  
% 19.31/3.03  fof(f80,plain,(
% 19.31/3.03    ( ! [X0,X1] : (k1_enumset1(X1,X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 19.31/3.03    inference(definition_unfolding,[],[f69,f75])).
% 19.31/3.03  
% 19.31/3.03  fof(f2,axiom,(
% 19.31/3.03    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 19.31/3.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.31/3.03  
% 19.31/3.03  fof(f42,plain,(
% 19.31/3.03    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 19.31/3.03    inference(nnf_transformation,[],[f2])).
% 19.31/3.03  
% 19.31/3.03  fof(f43,plain,(
% 19.31/3.03    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 19.31/3.03    inference(rectify,[],[f42])).
% 19.31/3.03  
% 19.31/3.03  fof(f44,plain,(
% 19.31/3.03    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 19.31/3.03    introduced(choice_axiom,[])).
% 19.31/3.03  
% 19.31/3.03  fof(f45,plain,(
% 19.31/3.03    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 19.31/3.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).
% 19.31/3.03  
% 19.31/3.03  fof(f52,plain,(
% 19.31/3.03    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 19.31/3.03    inference(cnf_transformation,[],[f45])).
% 19.31/3.03  
% 19.31/3.03  fof(f78,plain,(
% 19.31/3.03    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_enumset1(X0,X0,X0) != X1) )),
% 19.31/3.03    inference(definition_unfolding,[],[f52,f75])).
% 19.31/3.03  
% 19.31/3.03  fof(f81,plain,(
% 19.31/3.03    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_enumset1(X3,X3,X3) != X1) )),
% 19.31/3.03    inference(equality_resolution,[],[f78])).
% 19.31/3.03  
% 19.31/3.03  fof(f82,plain,(
% 19.31/3.03    ( ! [X3] : (r2_hidden(X3,k1_enumset1(X3,X3,X3))) )),
% 19.31/3.03    inference(equality_resolution,[],[f81])).
% 19.31/3.03  
% 19.31/3.03  fof(f1,axiom,(
% 19.31/3.03    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 19.31/3.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.31/3.03  
% 19.31/3.03  fof(f38,plain,(
% 19.31/3.03    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 19.31/3.03    inference(nnf_transformation,[],[f1])).
% 19.31/3.03  
% 19.31/3.03  fof(f39,plain,(
% 19.31/3.03    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 19.31/3.03    inference(rectify,[],[f38])).
% 19.31/3.03  
% 19.31/3.03  fof(f40,plain,(
% 19.31/3.03    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 19.31/3.03    introduced(choice_axiom,[])).
% 19.31/3.03  
% 19.31/3.03  fof(f41,plain,(
% 19.31/3.03    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 19.31/3.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).
% 19.31/3.03  
% 19.31/3.03  fof(f49,plain,(
% 19.31/3.03    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 19.31/3.03    inference(cnf_transformation,[],[f41])).
% 19.31/3.03  
% 19.31/3.03  fof(f13,axiom,(
% 19.31/3.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 19.31/3.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.31/3.03  
% 19.31/3.03  fof(f29,plain,(
% 19.31/3.03    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 19.31/3.03    inference(ennf_transformation,[],[f13])).
% 19.31/3.03  
% 19.31/3.03  fof(f66,plain,(
% 19.31/3.03    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 19.31/3.03    inference(cnf_transformation,[],[f29])).
% 19.31/3.03  
% 19.31/3.03  fof(f8,axiom,(
% 19.31/3.03    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 19.31/3.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.31/3.03  
% 19.31/3.03  fof(f23,plain,(
% 19.31/3.03    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 19.31/3.03    inference(ennf_transformation,[],[f8])).
% 19.31/3.03  
% 19.31/3.03  fof(f24,plain,(
% 19.31/3.03    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 19.31/3.03    inference(flattening,[],[f23])).
% 19.31/3.03  
% 19.31/3.03  fof(f60,plain,(
% 19.31/3.03    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 19.31/3.03    inference(cnf_transformation,[],[f24])).
% 19.31/3.03  
% 19.31/3.03  fof(f11,axiom,(
% 19.31/3.03    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 19.31/3.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.31/3.03  
% 19.31/3.03  fof(f27,plain,(
% 19.31/3.03    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 19.31/3.03    inference(ennf_transformation,[],[f11])).
% 19.31/3.03  
% 19.31/3.03  fof(f64,plain,(
% 19.31/3.03    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 19.31/3.03    inference(cnf_transformation,[],[f27])).
% 19.31/3.03  
% 19.31/3.03  fof(f9,axiom,(
% 19.31/3.03    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 19.31/3.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.31/3.03  
% 19.31/3.03  fof(f25,plain,(
% 19.31/3.03    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 19.31/3.03    inference(ennf_transformation,[],[f9])).
% 19.31/3.03  
% 19.31/3.03  fof(f61,plain,(
% 19.31/3.03    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 19.31/3.03    inference(cnf_transformation,[],[f25])).
% 19.31/3.03  
% 19.31/3.03  fof(f12,axiom,(
% 19.31/3.03    ! [X0] : (l1_struct_0(X0) => ~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)))),
% 19.31/3.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.31/3.03  
% 19.31/3.03  fof(f28,plain,(
% 19.31/3.03    ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0))),
% 19.31/3.03    inference(ennf_transformation,[],[f12])).
% 19.31/3.03  
% 19.31/3.03  fof(f65,plain,(
% 19.31/3.03    ( ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 19.31/3.03    inference(cnf_transformation,[],[f28])).
% 19.31/3.03  
% 19.31/3.03  fof(f10,axiom,(
% 19.31/3.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 19.31/3.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.31/3.03  
% 19.31/3.03  fof(f26,plain,(
% 19.31/3.03    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 19.31/3.03    inference(ennf_transformation,[],[f10])).
% 19.31/3.03  
% 19.31/3.03  fof(f62,plain,(
% 19.31/3.03    ( ! [X0,X1] : (v1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 19.31/3.03    inference(cnf_transformation,[],[f26])).
% 19.31/3.03  
% 19.31/3.03  fof(f5,axiom,(
% 19.31/3.03    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 19.31/3.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.31/3.03  
% 19.31/3.03  fof(f57,plain,(
% 19.31/3.03    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 19.31/3.03    inference(cnf_transformation,[],[f5])).
% 19.31/3.03  
% 19.31/3.03  fof(f63,plain,(
% 19.31/3.03    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 19.31/3.03    inference(cnf_transformation,[],[f26])).
% 19.31/3.03  
% 19.31/3.03  fof(f73,plain,(
% 19.31/3.03    v1_subset_1(k6_domain_1(sK2,sK3),sK2)),
% 19.31/3.03    inference(cnf_transformation,[],[f48])).
% 19.31/3.03  
% 19.31/3.03  cnf(c_1161,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_95840,plain,
% 19.31/3.03      ( k6_domain_1(sK2,sK3) != X0
% 19.31/3.03      | k6_domain_1(sK2,sK3) = u1_struct_0(g1_pre_topc(X1,k1_xboole_0))
% 19.31/3.03      | u1_struct_0(g1_pre_topc(X1,k1_xboole_0)) != X0 ),
% 19.31/3.03      inference(instantiation,[status(thm)],[c_1161]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_95846,plain,
% 19.31/3.03      ( k6_domain_1(sK2,sK3) = u1_struct_0(g1_pre_topc(sK2,k1_xboole_0))
% 19.31/3.03      | k6_domain_1(sK2,sK3) != sK2
% 19.31/3.03      | u1_struct_0(g1_pre_topc(sK2,k1_xboole_0)) != sK2 ),
% 19.31/3.03      inference(instantiation,[status(thm)],[c_95840]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_4429,plain,
% 19.31/3.03      ( X0 != X1
% 19.31/3.03      | X0 = k6_domain_1(sK2,sK3)
% 19.31/3.03      | k6_domain_1(sK2,sK3) != X1 ),
% 19.31/3.03      inference(instantiation,[status(thm)],[c_1161]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_13092,plain,
% 19.31/3.03      ( k6_domain_1(sK2,sK3) != X0
% 19.31/3.03      | k2_struct_0(g1_pre_topc(X1,k1_xboole_0)) != X0
% 19.31/3.03      | k2_struct_0(g1_pre_topc(X1,k1_xboole_0)) = k6_domain_1(sK2,sK3) ),
% 19.31/3.03      inference(instantiation,[status(thm)],[c_4429]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_19346,plain,
% 19.31/3.03      ( k6_domain_1(sK2,sK3) != u1_struct_0(g1_pre_topc(X0,k1_xboole_0))
% 19.31/3.03      | k2_struct_0(g1_pre_topc(X0,k1_xboole_0)) = k6_domain_1(sK2,sK3)
% 19.31/3.03      | k2_struct_0(g1_pre_topc(X0,k1_xboole_0)) != u1_struct_0(g1_pre_topc(X0,k1_xboole_0)) ),
% 19.31/3.03      inference(instantiation,[status(thm)],[c_13092]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_19347,plain,
% 19.31/3.03      ( k6_domain_1(sK2,sK3) != u1_struct_0(g1_pre_topc(sK2,k1_xboole_0))
% 19.31/3.03      | k2_struct_0(g1_pre_topc(sK2,k1_xboole_0)) = k6_domain_1(sK2,sK3)
% 19.31/3.03      | k2_struct_0(g1_pre_topc(sK2,k1_xboole_0)) != u1_struct_0(g1_pre_topc(sK2,k1_xboole_0)) ),
% 19.31/3.03      inference(instantiation,[status(thm)],[c_19346]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_17,plain,
% 19.31/3.03      ( ~ m1_subset_1(X0,X1)
% 19.31/3.03      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 19.31/3.03      | v1_xboole_0(X1) ),
% 19.31/3.03      inference(cnf_transformation,[],[f68]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_1602,plain,
% 19.31/3.03      ( m1_subset_1(X0,X1) != iProver_top
% 19.31/3.03      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
% 19.31/3.03      | v1_xboole_0(X1) = iProver_top ),
% 19.31/3.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_7,plain,
% 19.31/3.03      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 19.31/3.03      inference(cnf_transformation,[],[f58]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_19,plain,
% 19.31/3.03      ( ~ r1_tarski(X0,X1)
% 19.31/3.03      | ~ v1_zfmisc_1(X1)
% 19.31/3.03      | v1_xboole_0(X0)
% 19.31/3.03      | v1_xboole_0(X1)
% 19.31/3.03      | X1 = X0 ),
% 19.31/3.03      inference(cnf_transformation,[],[f70]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_20,negated_conjecture,
% 19.31/3.03      ( v1_zfmisc_1(sK2) ),
% 19.31/3.03      inference(cnf_transformation,[],[f74]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_356,plain,
% 19.31/3.03      ( ~ r1_tarski(X0,X1)
% 19.31/3.03      | v1_xboole_0(X0)
% 19.31/3.03      | v1_xboole_0(X1)
% 19.31/3.03      | X1 = X0
% 19.31/3.03      | sK2 != X1 ),
% 19.31/3.03      inference(resolution_lifted,[status(thm)],[c_19,c_20]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_357,plain,
% 19.31/3.03      ( ~ r1_tarski(X0,sK2)
% 19.31/3.03      | v1_xboole_0(X0)
% 19.31/3.03      | v1_xboole_0(sK2)
% 19.31/3.03      | sK2 = X0 ),
% 19.31/3.03      inference(unflattening,[status(thm)],[c_356]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_23,negated_conjecture,
% 19.31/3.03      ( ~ v1_xboole_0(sK2) ),
% 19.31/3.03      inference(cnf_transformation,[],[f71]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_361,plain,
% 19.31/3.03      ( v1_xboole_0(X0) | ~ r1_tarski(X0,sK2) | sK2 = X0 ),
% 19.31/3.03      inference(global_propositional_subsumption,
% 19.31/3.03                [status(thm)],
% 19.31/3.03                [c_357,c_23]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_362,plain,
% 19.31/3.03      ( ~ r1_tarski(X0,sK2) | v1_xboole_0(X0) | sK2 = X0 ),
% 19.31/3.03      inference(renaming,[status(thm)],[c_361]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_379,plain,
% 19.31/3.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.31/3.03      | v1_xboole_0(X2)
% 19.31/3.03      | X2 != X0
% 19.31/3.03      | sK2 != X1
% 19.31/3.03      | sK2 = X2 ),
% 19.31/3.03      inference(resolution_lifted,[status(thm)],[c_7,c_362]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_380,plain,
% 19.31/3.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2)) | v1_xboole_0(X0) | sK2 = X0 ),
% 19.31/3.03      inference(unflattening,[status(thm)],[c_379]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_1595,plain,
% 19.31/3.03      ( sK2 = X0
% 19.31/3.03      | m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 19.31/3.03      | v1_xboole_0(X0) = iProver_top ),
% 19.31/3.03      inference(predicate_to_equality,[status(thm)],[c_380]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_3370,plain,
% 19.31/3.03      ( k6_domain_1(sK2,X0) = sK2
% 19.31/3.03      | m1_subset_1(X0,sK2) != iProver_top
% 19.31/3.03      | v1_xboole_0(k6_domain_1(sK2,X0)) = iProver_top
% 19.31/3.03      | v1_xboole_0(sK2) = iProver_top ),
% 19.31/3.03      inference(superposition,[status(thm)],[c_1602,c_1595]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_24,plain,
% 19.31/3.03      ( v1_xboole_0(sK2) != iProver_top ),
% 19.31/3.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_4167,plain,
% 19.31/3.03      ( v1_xboole_0(k6_domain_1(sK2,X0)) = iProver_top
% 19.31/3.03      | m1_subset_1(X0,sK2) != iProver_top
% 19.31/3.03      | k6_domain_1(sK2,X0) = sK2 ),
% 19.31/3.03      inference(global_propositional_subsumption,
% 19.31/3.03                [status(thm)],
% 19.31/3.03                [c_3370,c_24]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_4168,plain,
% 19.31/3.03      ( k6_domain_1(sK2,X0) = sK2
% 19.31/3.03      | m1_subset_1(X0,sK2) != iProver_top
% 19.31/3.03      | v1_xboole_0(k6_domain_1(sK2,X0)) = iProver_top ),
% 19.31/3.03      inference(renaming,[status(thm)],[c_4167]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_22,negated_conjecture,
% 19.31/3.03      ( m1_subset_1(sK3,sK2) ),
% 19.31/3.03      inference(cnf_transformation,[],[f72]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_1599,plain,
% 19.31/3.03      ( m1_subset_1(sK3,sK2) = iProver_top ),
% 19.31/3.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_18,plain,
% 19.31/3.03      ( ~ m1_subset_1(X0,X1)
% 19.31/3.03      | v1_xboole_0(X1)
% 19.31/3.03      | k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0) ),
% 19.31/3.03      inference(cnf_transformation,[],[f80]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_1601,plain,
% 19.31/3.03      ( k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0)
% 19.31/3.03      | m1_subset_1(X0,X1) != iProver_top
% 19.31/3.03      | v1_xboole_0(X1) = iProver_top ),
% 19.31/3.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_3184,plain,
% 19.31/3.03      ( k1_enumset1(sK3,sK3,sK3) = k6_domain_1(sK2,sK3)
% 19.31/3.03      | v1_xboole_0(sK2) = iProver_top ),
% 19.31/3.03      inference(superposition,[status(thm)],[c_1599,c_1601]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_1827,plain,
% 19.31/3.03      ( ~ m1_subset_1(sK3,sK2)
% 19.31/3.03      | v1_xboole_0(sK2)
% 19.31/3.03      | k1_enumset1(sK3,sK3,sK3) = k6_domain_1(sK2,sK3) ),
% 19.31/3.03      inference(instantiation,[status(thm)],[c_18]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_3872,plain,
% 19.31/3.03      ( k1_enumset1(sK3,sK3,sK3) = k6_domain_1(sK2,sK3) ),
% 19.31/3.03      inference(global_propositional_subsumption,
% 19.31/3.03                [status(thm)],
% 19.31/3.03                [c_3184,c_23,c_22,c_1827]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_4,plain,
% 19.31/3.03      ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
% 19.31/3.03      inference(cnf_transformation,[],[f82]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_1611,plain,
% 19.31/3.03      ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) = iProver_top ),
% 19.31/3.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_1,plain,
% 19.31/3.03      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 19.31/3.03      inference(cnf_transformation,[],[f49]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_1614,plain,
% 19.31/3.03      ( r2_hidden(X0,X1) != iProver_top
% 19.31/3.03      | v1_xboole_0(X1) != iProver_top ),
% 19.31/3.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_2265,plain,
% 19.31/3.03      ( v1_xboole_0(k1_enumset1(X0,X0,X0)) != iProver_top ),
% 19.31/3.03      inference(superposition,[status(thm)],[c_1611,c_1614]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_3875,plain,
% 19.31/3.03      ( v1_xboole_0(k6_domain_1(sK2,sK3)) != iProver_top ),
% 19.31/3.03      inference(superposition,[status(thm)],[c_3872,c_2265]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_4176,plain,
% 19.31/3.03      ( k6_domain_1(sK2,sK3) = sK2
% 19.31/3.03      | m1_subset_1(sK3,sK2) != iProver_top ),
% 19.31/3.03      inference(superposition,[status(thm)],[c_4168,c_3875]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_16,plain,
% 19.31/3.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 19.31/3.03      | X2 = X1
% 19.31/3.03      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 19.31/3.03      inference(cnf_transformation,[],[f66]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_2509,plain,
% 19.31/3.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK2)))
% 19.31/3.03      | g1_pre_topc(u1_struct_0(g1_pre_topc(X1,k1_xboole_0)),X2) != g1_pre_topc(sK2,X0)
% 19.31/3.03      | u1_struct_0(g1_pre_topc(X1,k1_xboole_0)) = sK2 ),
% 19.31/3.03      inference(instantiation,[status(thm)],[c_16]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_4107,plain,
% 19.31/3.03      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK2)))
% 19.31/3.03      | g1_pre_topc(u1_struct_0(g1_pre_topc(sK2,k1_xboole_0)),u1_pre_topc(g1_pre_topc(sK2,k1_xboole_0))) != g1_pre_topc(sK2,k1_xboole_0)
% 19.31/3.03      | u1_struct_0(g1_pre_topc(sK2,k1_xboole_0)) = sK2 ),
% 19.31/3.03      inference(instantiation,[status(thm)],[c_2509]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_1169,plain,
% 19.31/3.03      ( ~ v1_subset_1(X0,X1) | v1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.31/3.03      theory(equality) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_1840,plain,
% 19.31/3.03      ( v1_subset_1(X0,X1)
% 19.31/3.03      | ~ v1_subset_1(k6_domain_1(sK2,sK3),sK2)
% 19.31/3.03      | X0 != k6_domain_1(sK2,sK3)
% 19.31/3.03      | X1 != sK2 ),
% 19.31/3.03      inference(instantiation,[status(thm)],[c_1169]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_2251,plain,
% 19.31/3.03      ( ~ v1_subset_1(k6_domain_1(sK2,sK3),sK2)
% 19.31/3.03      | v1_subset_1(k2_struct_0(g1_pre_topc(X0,k1_xboole_0)),u1_struct_0(g1_pre_topc(X0,k1_xboole_0)))
% 19.31/3.03      | k2_struct_0(g1_pre_topc(X0,k1_xboole_0)) != k6_domain_1(sK2,sK3)
% 19.31/3.03      | u1_struct_0(g1_pre_topc(X0,k1_xboole_0)) != sK2 ),
% 19.31/3.03      inference(instantiation,[status(thm)],[c_1840]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_2253,plain,
% 19.31/3.03      ( ~ v1_subset_1(k6_domain_1(sK2,sK3),sK2)
% 19.31/3.03      | v1_subset_1(k2_struct_0(g1_pre_topc(sK2,k1_xboole_0)),u1_struct_0(g1_pre_topc(sK2,k1_xboole_0)))
% 19.31/3.03      | k2_struct_0(g1_pre_topc(sK2,k1_xboole_0)) != k6_domain_1(sK2,sK3)
% 19.31/3.03      | u1_struct_0(g1_pre_topc(sK2,k1_xboole_0)) != sK2 ),
% 19.31/3.03      inference(instantiation,[status(thm)],[c_2251]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_9,plain,
% 19.31/3.03      ( ~ l1_pre_topc(X0)
% 19.31/3.03      | ~ v1_pre_topc(X0)
% 19.31/3.03      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 19.31/3.03      inference(cnf_transformation,[],[f60]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_2241,plain,
% 19.31/3.03      ( ~ l1_pre_topc(g1_pre_topc(X0,k1_xboole_0))
% 19.31/3.03      | ~ v1_pre_topc(g1_pre_topc(X0,k1_xboole_0))
% 19.31/3.03      | g1_pre_topc(u1_struct_0(g1_pre_topc(X0,k1_xboole_0)),u1_pre_topc(g1_pre_topc(X0,k1_xboole_0))) = g1_pre_topc(X0,k1_xboole_0) ),
% 19.31/3.03      inference(instantiation,[status(thm)],[c_9]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_2248,plain,
% 19.31/3.03      ( ~ l1_pre_topc(g1_pre_topc(sK2,k1_xboole_0))
% 19.31/3.03      | ~ v1_pre_topc(g1_pre_topc(sK2,k1_xboole_0))
% 19.31/3.03      | g1_pre_topc(u1_struct_0(g1_pre_topc(sK2,k1_xboole_0)),u1_pre_topc(g1_pre_topc(sK2,k1_xboole_0))) = g1_pre_topc(sK2,k1_xboole_0) ),
% 19.31/3.03      inference(instantiation,[status(thm)],[c_2241]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_13,plain,
% 19.31/3.03      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 19.31/3.03      inference(cnf_transformation,[],[f64]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_10,plain,
% 19.31/3.03      ( ~ l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 19.31/3.03      inference(cnf_transformation,[],[f61]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_322,plain,
% 19.31/3.03      ( ~ l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 19.31/3.03      inference(resolution,[status(thm)],[c_13,c_10]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_2030,plain,
% 19.31/3.03      ( ~ l1_pre_topc(g1_pre_topc(X0,k1_xboole_0))
% 19.31/3.03      | k2_struct_0(g1_pre_topc(X0,k1_xboole_0)) = u1_struct_0(g1_pre_topc(X0,k1_xboole_0)) ),
% 19.31/3.03      inference(instantiation,[status(thm)],[c_322]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_2037,plain,
% 19.31/3.03      ( ~ l1_pre_topc(g1_pre_topc(sK2,k1_xboole_0))
% 19.31/3.03      | k2_struct_0(g1_pre_topc(sK2,k1_xboole_0)) = u1_struct_0(g1_pre_topc(sK2,k1_xboole_0)) ),
% 19.31/3.03      inference(instantiation,[status(thm)],[c_2030]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_14,plain,
% 19.31/3.03      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
% 19.31/3.03      | ~ l1_struct_0(X0) ),
% 19.31/3.03      inference(cnf_transformation,[],[f65]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_311,plain,
% 19.31/3.03      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
% 19.31/3.03      | ~ l1_pre_topc(X0) ),
% 19.31/3.03      inference(resolution,[status(thm)],[c_13,c_14]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_2031,plain,
% 19.31/3.03      ( ~ v1_subset_1(k2_struct_0(g1_pre_topc(X0,k1_xboole_0)),u1_struct_0(g1_pre_topc(X0,k1_xboole_0)))
% 19.31/3.03      | ~ l1_pre_topc(g1_pre_topc(X0,k1_xboole_0)) ),
% 19.31/3.03      inference(instantiation,[status(thm)],[c_311]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_2033,plain,
% 19.31/3.03      ( ~ v1_subset_1(k2_struct_0(g1_pre_topc(sK2,k1_xboole_0)),u1_struct_0(g1_pre_topc(sK2,k1_xboole_0)))
% 19.31/3.03      | ~ l1_pre_topc(g1_pre_topc(sK2,k1_xboole_0)) ),
% 19.31/3.03      inference(instantiation,[status(thm)],[c_2031]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_12,plain,
% 19.31/3.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 19.31/3.03      | v1_pre_topc(g1_pre_topc(X1,X0)) ),
% 19.31/3.03      inference(cnf_transformation,[],[f62]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_6,plain,
% 19.31/3.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 19.31/3.03      inference(cnf_transformation,[],[f57]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_1902,plain,
% 19.31/3.03      ( v1_pre_topc(g1_pre_topc(X0,k1_xboole_0)) ),
% 19.31/3.03      inference(resolution,[status(thm)],[c_12,c_6]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_1904,plain,
% 19.31/3.03      ( v1_pre_topc(g1_pre_topc(sK2,k1_xboole_0)) ),
% 19.31/3.03      inference(instantiation,[status(thm)],[c_1902]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_1775,plain,
% 19.31/3.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ),
% 19.31/3.03      inference(instantiation,[status(thm)],[c_6]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_1781,plain,
% 19.31/3.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
% 19.31/3.03      inference(instantiation,[status(thm)],[c_1775]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_11,plain,
% 19.31/3.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 19.31/3.03      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 19.31/3.03      inference(cnf_transformation,[],[f63]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_1774,plain,
% 19.31/3.03      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
% 19.31/3.03      | l1_pre_topc(g1_pre_topc(X0,k1_xboole_0)) ),
% 19.31/3.03      inference(instantiation,[status(thm)],[c_11]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_1777,plain,
% 19.31/3.03      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK2)))
% 19.31/3.03      | l1_pre_topc(g1_pre_topc(sK2,k1_xboole_0)) ),
% 19.31/3.03      inference(instantiation,[status(thm)],[c_1774]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_21,negated_conjecture,
% 19.31/3.03      ( v1_subset_1(k6_domain_1(sK2,sK3),sK2) ),
% 19.31/3.03      inference(cnf_transformation,[],[f73]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(c_25,plain,
% 19.31/3.03      ( m1_subset_1(sK3,sK2) = iProver_top ),
% 19.31/3.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 19.31/3.03  
% 19.31/3.03  cnf(contradiction,plain,
% 19.31/3.03      ( $false ),
% 19.31/3.03      inference(minisat,
% 19.31/3.03                [status(thm)],
% 19.31/3.03                [c_95846,c_19347,c_4176,c_4107,c_2253,c_2248,c_2037,
% 19.31/3.03                 c_2033,c_1904,c_1781,c_1777,c_21,c_25]) ).
% 19.31/3.03  
% 19.31/3.03  
% 19.31/3.03  % SZS output end CNFRefutation for theBenchmark.p
% 19.31/3.03  
% 19.31/3.03  ------                               Statistics
% 19.31/3.03  
% 19.31/3.03  ------ Selected
% 19.31/3.03  
% 19.31/3.03  total_time:                             2.348
% 19.31/3.03  
%------------------------------------------------------------------------------
