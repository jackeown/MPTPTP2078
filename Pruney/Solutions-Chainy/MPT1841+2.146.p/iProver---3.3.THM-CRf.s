%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:17 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 354 expanded)
%              Number of clauses        :   68 ( 107 expanded)
%              Number of leaves         :   24 (  89 expanded)
%              Depth                    :   17
%              Number of atoms          :  322 (1085 expanded)
%              Number of equality atoms :  112 ( 183 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
     => ( v1_zfmisc_1(X0)
        & v1_subset_1(k6_domain_1(X0,sK3),X0)
        & m1_subset_1(sK3,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
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

fof(f44,plain,
    ( v1_zfmisc_1(sK2)
    & v1_subset_1(k6_domain_1(sK2,sK3),sK2)
    & m1_subset_1(sK3,sK2)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f32,f43,f42])).

fof(f67,plain,(
    m1_subset_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f61,f53])).

fof(f66,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f16,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f65,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f69,plain,(
    v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    v1_subset_1(k6_domain_1(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f60,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f62,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f15,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f45,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f70,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f52,f50])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f70])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f72,plain,(
    ! [X0,X1] : k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,k2_tarski(X0,X0)))) != k1_xboole_0 ),
    inference(definition_unfolding,[],[f54,f70,f53])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1419,plain,
    ( m1_subset_1(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1421,plain,
    ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1792,plain,
    ( k6_domain_1(sK2,sK3) = k2_tarski(sK3,sK3)
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1419,c_1421])).

cnf(c_20,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1554,plain,
    ( ~ m1_subset_1(sK3,sK2)
    | v1_xboole_0(sK2)
    | k6_domain_1(sK2,sK3) = k2_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2005,plain,
    ( k6_domain_1(sK2,sK3) = k2_tarski(sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1792,c_20,c_19,c_1554])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1422,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2183,plain,
    ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK3,sK2) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2005,c_1422])).

cnf(c_21,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_22,plain,
    ( m1_subset_1(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2457,plain,
    ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2183,c_21,c_22])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1423,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2462,plain,
    ( r1_tarski(k2_tarski(sK3,sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2457,c_1423])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_17,negated_conjecture,
    ( v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_317,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_17])).

cnf(c_318,plain,
    ( ~ r1_tarski(X0,sK2)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | sK2 = X0 ),
    inference(unflattening,[status(thm)],[c_317])).

cnf(c_322,plain,
    ( v1_xboole_0(X0)
    | ~ r1_tarski(X0,sK2)
    | sK2 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_318,c_20])).

cnf(c_323,plain,
    ( ~ r1_tarski(X0,sK2)
    | v1_xboole_0(X0)
    | sK2 = X0 ),
    inference(renaming,[status(thm)],[c_322])).

cnf(c_1416,plain,
    ( sK2 = X0
    | r1_tarski(X0,sK2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_323])).

cnf(c_2555,plain,
    ( k2_tarski(sK3,sK3) = sK2
    | v1_xboole_0(k2_tarski(sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2462,c_1416])).

cnf(c_18,negated_conjecture,
    ( v1_subset_1(k6_domain_1(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1002,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1025,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1002])).

cnf(c_10,plain,
    ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_12,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_14,plain,
    ( l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_278,plain,
    ( l1_struct_0(X0)
    | k2_yellow_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_14])).

cnf(c_279,plain,
    ( l1_struct_0(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_278])).

cnf(c_289,plain,
    ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
    | k2_yellow_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_279])).

cnf(c_290,plain,
    ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(X0)),u1_struct_0(k2_yellow_1(X0))) ),
    inference(unflattening,[status(thm)],[c_289])).

cnf(c_1417,plain,
    ( v1_subset_1(k2_struct_0(k2_yellow_1(X0)),u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_290])).

cnf(c_15,plain,
    ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_9,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_298,plain,
    ( k2_yellow_1(X0) != X1
    | u1_struct_0(X1) = k2_struct_0(X1) ),
    inference(resolution_lifted,[status(thm)],[c_9,c_279])).

cnf(c_299,plain,
    ( u1_struct_0(k2_yellow_1(X0)) = k2_struct_0(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_298])).

cnf(c_1437,plain,
    ( k2_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_299,c_15])).

cnf(c_1442,plain,
    ( v1_subset_1(X0,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1417,c_15,c_1437])).

cnf(c_1511,plain,
    ( ~ v1_subset_1(X0,X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1442])).

cnf(c_1513,plain,
    ( ~ v1_subset_1(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1511])).

cnf(c_1012,plain,
    ( ~ v1_subset_1(X0,X1)
    | v1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1567,plain,
    ( v1_subset_1(X0,X1)
    | ~ v1_subset_1(k6_domain_1(sK2,sK3),sK2)
    | X0 != k6_domain_1(sK2,sK3)
    | X1 != sK2 ),
    inference(instantiation,[status(thm)],[c_1012])).

cnf(c_1569,plain,
    ( ~ v1_subset_1(k6_domain_1(sK2,sK3),sK2)
    | v1_subset_1(sK2,sK2)
    | sK2 != k6_domain_1(sK2,sK3)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1567])).

cnf(c_1003,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1644,plain,
    ( X0 != X1
    | X0 = k6_domain_1(sK2,sK3)
    | k6_domain_1(sK2,sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_1003])).

cnf(c_1801,plain,
    ( X0 = k6_domain_1(sK2,sK3)
    | X0 != k2_tarski(sK3,sK3)
    | k6_domain_1(sK2,sK3) != k2_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_1644])).

cnf(c_1802,plain,
    ( k6_domain_1(sK2,sK3) != k2_tarski(sK3,sK3)
    | sK2 = k6_domain_1(sK2,sK3)
    | sK2 != k2_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_1801])).

cnf(c_1948,plain,
    ( ~ r1_tarski(k2_tarski(sK3,sK3),sK2)
    | v1_xboole_0(k2_tarski(sK3,sK3))
    | sK2 = k2_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_323])).

cnf(c_1949,plain,
    ( sK2 = k2_tarski(sK3,sK3)
    | r1_tarski(k2_tarski(sK3,sK3),sK2) != iProver_top
    | v1_xboole_0(k2_tarski(sK3,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1948])).

cnf(c_1961,plain,
    ( ~ m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(sK2))
    | r1_tarski(k2_tarski(sK3,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1962,plain,
    ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(k2_tarski(sK3,sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1961])).

cnf(c_2571,plain,
    ( v1_xboole_0(k2_tarski(sK3,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2555,c_20,c_21,c_19,c_22,c_18,c_1025,c_1513,c_1554,c_1569,c_1802,c_1949,c_1962,c_2183])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1427,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1429,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2096,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1427,c_1429])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1425,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2376,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2096,c_1425])).

cnf(c_2576,plain,
    ( k5_xboole_0(k2_tarski(sK3,sK3),k5_xboole_0(X0,k3_xboole_0(X0,k2_tarski(sK3,sK3)))) = X0 ),
    inference(superposition,[status(thm)],[c_2571,c_2376])).

cnf(c_6,plain,
    ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,k2_tarski(X0,X0)))) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2647,plain,
    ( k1_xboole_0 != X0 ),
    inference(superposition,[status(thm)],[c_2576,c_6])).

cnf(c_2746,plain,
    ( $false ),
    inference(equality_resolution,[status(thm)],[c_2647])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:29:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.91/1.05  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.05  
% 1.91/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.91/1.05  
% 1.91/1.05  ------  iProver source info
% 1.91/1.05  
% 1.91/1.05  git: date: 2020-06-30 10:37:57 +0100
% 1.91/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.91/1.05  git: non_committed_changes: false
% 1.91/1.05  git: last_make_outside_of_git: false
% 1.91/1.05  
% 1.91/1.05  ------ 
% 1.91/1.05  
% 1.91/1.05  ------ Input Options
% 1.91/1.05  
% 1.91/1.05  --out_options                           all
% 1.91/1.05  --tptp_safe_out                         true
% 1.91/1.05  --problem_path                          ""
% 1.91/1.05  --include_path                          ""
% 1.91/1.05  --clausifier                            res/vclausify_rel
% 1.91/1.05  --clausifier_options                    --mode clausify
% 1.91/1.05  --stdin                                 false
% 1.91/1.05  --stats_out                             all
% 1.91/1.05  
% 1.91/1.05  ------ General Options
% 1.91/1.05  
% 1.91/1.05  --fof                                   false
% 1.91/1.05  --time_out_real                         305.
% 1.91/1.05  --time_out_virtual                      -1.
% 1.91/1.05  --symbol_type_check                     false
% 1.91/1.05  --clausify_out                          false
% 1.91/1.05  --sig_cnt_out                           false
% 1.91/1.05  --trig_cnt_out                          false
% 1.91/1.05  --trig_cnt_out_tolerance                1.
% 1.91/1.05  --trig_cnt_out_sk_spl                   false
% 1.91/1.05  --abstr_cl_out                          false
% 1.91/1.05  
% 1.91/1.05  ------ Global Options
% 1.91/1.05  
% 1.91/1.05  --schedule                              default
% 1.91/1.05  --add_important_lit                     false
% 1.91/1.05  --prop_solver_per_cl                    1000
% 1.91/1.05  --min_unsat_core                        false
% 1.91/1.05  --soft_assumptions                      false
% 1.91/1.05  --soft_lemma_size                       3
% 1.91/1.05  --prop_impl_unit_size                   0
% 1.91/1.05  --prop_impl_unit                        []
% 1.91/1.05  --share_sel_clauses                     true
% 1.91/1.05  --reset_solvers                         false
% 1.91/1.05  --bc_imp_inh                            [conj_cone]
% 1.91/1.05  --conj_cone_tolerance                   3.
% 1.91/1.05  --extra_neg_conj                        none
% 1.91/1.05  --large_theory_mode                     true
% 1.91/1.05  --prolific_symb_bound                   200
% 1.91/1.05  --lt_threshold                          2000
% 1.91/1.05  --clause_weak_htbl                      true
% 1.91/1.05  --gc_record_bc_elim                     false
% 1.91/1.05  
% 1.91/1.05  ------ Preprocessing Options
% 1.91/1.05  
% 1.91/1.05  --preprocessing_flag                    true
% 1.91/1.05  --time_out_prep_mult                    0.1
% 1.91/1.05  --splitting_mode                        input
% 1.91/1.05  --splitting_grd                         true
% 1.91/1.05  --splitting_cvd                         false
% 1.91/1.05  --splitting_cvd_svl                     false
% 1.91/1.05  --splitting_nvd                         32
% 1.91/1.05  --sub_typing                            true
% 1.91/1.05  --prep_gs_sim                           true
% 1.91/1.05  --prep_unflatten                        true
% 1.91/1.05  --prep_res_sim                          true
% 1.91/1.05  --prep_upred                            true
% 1.91/1.05  --prep_sem_filter                       exhaustive
% 1.91/1.05  --prep_sem_filter_out                   false
% 1.91/1.05  --pred_elim                             true
% 1.91/1.05  --res_sim_input                         true
% 1.91/1.05  --eq_ax_congr_red                       true
% 1.91/1.05  --pure_diseq_elim                       true
% 1.91/1.05  --brand_transform                       false
% 1.91/1.05  --non_eq_to_eq                          false
% 1.91/1.05  --prep_def_merge                        true
% 1.91/1.05  --prep_def_merge_prop_impl              false
% 1.91/1.05  --prep_def_merge_mbd                    true
% 1.91/1.05  --prep_def_merge_tr_red                 false
% 1.91/1.05  --prep_def_merge_tr_cl                  false
% 1.91/1.05  --smt_preprocessing                     true
% 1.91/1.05  --smt_ac_axioms                         fast
% 1.91/1.05  --preprocessed_out                      false
% 1.91/1.05  --preprocessed_stats                    false
% 1.91/1.05  
% 1.91/1.05  ------ Abstraction refinement Options
% 1.91/1.05  
% 1.91/1.05  --abstr_ref                             []
% 1.91/1.05  --abstr_ref_prep                        false
% 1.91/1.05  --abstr_ref_until_sat                   false
% 1.91/1.05  --abstr_ref_sig_restrict                funpre
% 1.91/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 1.91/1.05  --abstr_ref_under                       []
% 1.91/1.05  
% 1.91/1.05  ------ SAT Options
% 1.91/1.05  
% 1.91/1.05  --sat_mode                              false
% 1.91/1.05  --sat_fm_restart_options                ""
% 1.91/1.05  --sat_gr_def                            false
% 1.91/1.05  --sat_epr_types                         true
% 1.91/1.05  --sat_non_cyclic_types                  false
% 1.91/1.05  --sat_finite_models                     false
% 1.91/1.05  --sat_fm_lemmas                         false
% 1.91/1.05  --sat_fm_prep                           false
% 1.91/1.05  --sat_fm_uc_incr                        true
% 1.91/1.05  --sat_out_model                         small
% 1.91/1.05  --sat_out_clauses                       false
% 1.91/1.05  
% 1.91/1.05  ------ QBF Options
% 1.91/1.05  
% 1.91/1.05  --qbf_mode                              false
% 1.91/1.05  --qbf_elim_univ                         false
% 1.91/1.05  --qbf_dom_inst                          none
% 1.91/1.05  --qbf_dom_pre_inst                      false
% 1.91/1.05  --qbf_sk_in                             false
% 1.91/1.05  --qbf_pred_elim                         true
% 1.91/1.05  --qbf_split                             512
% 1.91/1.05  
% 1.91/1.05  ------ BMC1 Options
% 1.91/1.05  
% 1.91/1.05  --bmc1_incremental                      false
% 1.91/1.05  --bmc1_axioms                           reachable_all
% 1.91/1.05  --bmc1_min_bound                        0
% 1.91/1.05  --bmc1_max_bound                        -1
% 1.91/1.05  --bmc1_max_bound_default                -1
% 1.91/1.05  --bmc1_symbol_reachability              true
% 1.91/1.05  --bmc1_property_lemmas                  false
% 1.91/1.05  --bmc1_k_induction                      false
% 1.91/1.05  --bmc1_non_equiv_states                 false
% 1.91/1.05  --bmc1_deadlock                         false
% 1.91/1.05  --bmc1_ucm                              false
% 1.91/1.05  --bmc1_add_unsat_core                   none
% 1.91/1.05  --bmc1_unsat_core_children              false
% 1.91/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 1.91/1.05  --bmc1_out_stat                         full
% 1.91/1.05  --bmc1_ground_init                      false
% 1.91/1.05  --bmc1_pre_inst_next_state              false
% 1.91/1.05  --bmc1_pre_inst_state                   false
% 1.91/1.05  --bmc1_pre_inst_reach_state             false
% 1.91/1.05  --bmc1_out_unsat_core                   false
% 1.91/1.05  --bmc1_aig_witness_out                  false
% 1.91/1.05  --bmc1_verbose                          false
% 1.91/1.05  --bmc1_dump_clauses_tptp                false
% 1.91/1.05  --bmc1_dump_unsat_core_tptp             false
% 1.91/1.05  --bmc1_dump_file                        -
% 1.91/1.05  --bmc1_ucm_expand_uc_limit              128
% 1.91/1.05  --bmc1_ucm_n_expand_iterations          6
% 1.91/1.05  --bmc1_ucm_extend_mode                  1
% 1.91/1.05  --bmc1_ucm_init_mode                    2
% 1.91/1.05  --bmc1_ucm_cone_mode                    none
% 1.91/1.05  --bmc1_ucm_reduced_relation_type        0
% 1.91/1.05  --bmc1_ucm_relax_model                  4
% 1.91/1.05  --bmc1_ucm_full_tr_after_sat            true
% 1.91/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 1.91/1.05  --bmc1_ucm_layered_model                none
% 1.91/1.05  --bmc1_ucm_max_lemma_size               10
% 1.91/1.05  
% 1.91/1.05  ------ AIG Options
% 1.91/1.05  
% 1.91/1.05  --aig_mode                              false
% 1.91/1.05  
% 1.91/1.05  ------ Instantiation Options
% 1.91/1.05  
% 1.91/1.05  --instantiation_flag                    true
% 1.91/1.05  --inst_sos_flag                         false
% 1.91/1.05  --inst_sos_phase                        true
% 1.91/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.91/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.91/1.05  --inst_lit_sel_side                     num_symb
% 1.91/1.05  --inst_solver_per_active                1400
% 1.91/1.05  --inst_solver_calls_frac                1.
% 1.91/1.05  --inst_passive_queue_type               priority_queues
% 1.91/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.91/1.05  --inst_passive_queues_freq              [25;2]
% 1.91/1.05  --inst_dismatching                      true
% 1.91/1.05  --inst_eager_unprocessed_to_passive     true
% 1.91/1.05  --inst_prop_sim_given                   true
% 1.91/1.05  --inst_prop_sim_new                     false
% 1.91/1.05  --inst_subs_new                         false
% 1.91/1.05  --inst_eq_res_simp                      false
% 1.91/1.05  --inst_subs_given                       false
% 1.91/1.05  --inst_orphan_elimination               true
% 1.91/1.05  --inst_learning_loop_flag               true
% 1.91/1.05  --inst_learning_start                   3000
% 1.91/1.05  --inst_learning_factor                  2
% 1.91/1.05  --inst_start_prop_sim_after_learn       3
% 1.91/1.05  --inst_sel_renew                        solver
% 1.91/1.05  --inst_lit_activity_flag                true
% 1.91/1.05  --inst_restr_to_given                   false
% 1.91/1.05  --inst_activity_threshold               500
% 1.91/1.05  --inst_out_proof                        true
% 1.91/1.05  
% 1.91/1.05  ------ Resolution Options
% 1.91/1.05  
% 1.91/1.05  --resolution_flag                       true
% 1.91/1.05  --res_lit_sel                           adaptive
% 1.91/1.05  --res_lit_sel_side                      none
% 1.91/1.05  --res_ordering                          kbo
% 1.91/1.05  --res_to_prop_solver                    active
% 1.91/1.05  --res_prop_simpl_new                    false
% 1.91/1.05  --res_prop_simpl_given                  true
% 1.91/1.05  --res_passive_queue_type                priority_queues
% 1.91/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.91/1.05  --res_passive_queues_freq               [15;5]
% 1.91/1.05  --res_forward_subs                      full
% 1.91/1.05  --res_backward_subs                     full
% 1.91/1.05  --res_forward_subs_resolution           true
% 1.91/1.05  --res_backward_subs_resolution          true
% 1.91/1.05  --res_orphan_elimination                true
% 1.91/1.05  --res_time_limit                        2.
% 1.91/1.05  --res_out_proof                         true
% 1.91/1.05  
% 1.91/1.05  ------ Superposition Options
% 1.91/1.05  
% 1.91/1.05  --superposition_flag                    true
% 1.91/1.05  --sup_passive_queue_type                priority_queues
% 1.91/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.91/1.05  --sup_passive_queues_freq               [8;1;4]
% 1.91/1.05  --demod_completeness_check              fast
% 1.91/1.05  --demod_use_ground                      true
% 1.91/1.05  --sup_to_prop_solver                    passive
% 1.91/1.05  --sup_prop_simpl_new                    true
% 1.91/1.05  --sup_prop_simpl_given                  true
% 1.91/1.05  --sup_fun_splitting                     false
% 1.91/1.05  --sup_smt_interval                      50000
% 1.91/1.05  
% 1.91/1.05  ------ Superposition Simplification Setup
% 1.91/1.05  
% 1.91/1.05  --sup_indices_passive                   []
% 1.91/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 1.91/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/1.05  --sup_full_bw                           [BwDemod]
% 1.91/1.05  --sup_immed_triv                        [TrivRules]
% 1.91/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.91/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/1.05  --sup_immed_bw_main                     []
% 1.91/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.91/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 1.91/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.91/1.05  
% 1.91/1.05  ------ Combination Options
% 1.91/1.05  
% 1.91/1.05  --comb_res_mult                         3
% 1.91/1.05  --comb_sup_mult                         2
% 1.91/1.05  --comb_inst_mult                        10
% 1.91/1.05  
% 1.91/1.05  ------ Debug Options
% 1.91/1.05  
% 1.91/1.05  --dbg_backtrace                         false
% 1.91/1.05  --dbg_dump_prop_clauses                 false
% 1.91/1.05  --dbg_dump_prop_clauses_file            -
% 1.91/1.05  --dbg_out_stat                          false
% 1.91/1.05  ------ Parsing...
% 1.91/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.91/1.05  
% 1.91/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.91/1.05  
% 1.91/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.91/1.05  
% 1.91/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.91/1.05  ------ Proving...
% 1.91/1.05  ------ Problem Properties 
% 1.91/1.05  
% 1.91/1.05  
% 1.91/1.05  clauses                                 18
% 1.91/1.05  conjectures                             3
% 1.91/1.05  EPR                                     5
% 1.91/1.05  Horn                                    13
% 1.91/1.05  unary                                   7
% 1.91/1.05  binary                                  7
% 1.91/1.05  lits                                    33
% 1.91/1.05  lits eq                                 6
% 1.91/1.05  fd_pure                                 0
% 1.91/1.05  fd_pseudo                               0
% 1.91/1.05  fd_cond                                 1
% 1.91/1.05  fd_pseudo_cond                          0
% 1.91/1.05  AC symbols                              0
% 1.91/1.05  
% 1.91/1.05  ------ Schedule dynamic 5 is on 
% 1.91/1.05  
% 1.91/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.91/1.05  
% 1.91/1.05  
% 1.91/1.05  ------ 
% 1.91/1.05  Current options:
% 1.91/1.05  ------ 
% 1.91/1.05  
% 1.91/1.05  ------ Input Options
% 1.91/1.05  
% 1.91/1.05  --out_options                           all
% 1.91/1.05  --tptp_safe_out                         true
% 1.91/1.05  --problem_path                          ""
% 1.91/1.05  --include_path                          ""
% 1.91/1.05  --clausifier                            res/vclausify_rel
% 1.91/1.05  --clausifier_options                    --mode clausify
% 1.91/1.05  --stdin                                 false
% 1.91/1.05  --stats_out                             all
% 1.91/1.05  
% 1.91/1.05  ------ General Options
% 1.91/1.05  
% 1.91/1.05  --fof                                   false
% 1.91/1.05  --time_out_real                         305.
% 1.91/1.05  --time_out_virtual                      -1.
% 1.91/1.05  --symbol_type_check                     false
% 1.91/1.05  --clausify_out                          false
% 1.91/1.05  --sig_cnt_out                           false
% 1.91/1.05  --trig_cnt_out                          false
% 1.91/1.05  --trig_cnt_out_tolerance                1.
% 1.91/1.05  --trig_cnt_out_sk_spl                   false
% 1.91/1.05  --abstr_cl_out                          false
% 1.91/1.05  
% 1.91/1.05  ------ Global Options
% 1.91/1.05  
% 1.91/1.05  --schedule                              default
% 1.91/1.05  --add_important_lit                     false
% 1.91/1.05  --prop_solver_per_cl                    1000
% 1.91/1.05  --min_unsat_core                        false
% 1.91/1.05  --soft_assumptions                      false
% 1.91/1.05  --soft_lemma_size                       3
% 1.91/1.05  --prop_impl_unit_size                   0
% 1.91/1.05  --prop_impl_unit                        []
% 1.91/1.05  --share_sel_clauses                     true
% 1.91/1.05  --reset_solvers                         false
% 1.91/1.05  --bc_imp_inh                            [conj_cone]
% 1.91/1.05  --conj_cone_tolerance                   3.
% 1.91/1.05  --extra_neg_conj                        none
% 1.91/1.05  --large_theory_mode                     true
% 1.91/1.05  --prolific_symb_bound                   200
% 1.91/1.05  --lt_threshold                          2000
% 1.91/1.05  --clause_weak_htbl                      true
% 1.91/1.05  --gc_record_bc_elim                     false
% 1.91/1.05  
% 1.91/1.05  ------ Preprocessing Options
% 1.91/1.05  
% 1.91/1.05  --preprocessing_flag                    true
% 1.91/1.05  --time_out_prep_mult                    0.1
% 1.91/1.05  --splitting_mode                        input
% 1.91/1.05  --splitting_grd                         true
% 1.91/1.05  --splitting_cvd                         false
% 1.91/1.05  --splitting_cvd_svl                     false
% 1.91/1.05  --splitting_nvd                         32
% 1.91/1.05  --sub_typing                            true
% 1.91/1.05  --prep_gs_sim                           true
% 1.91/1.05  --prep_unflatten                        true
% 1.91/1.05  --prep_res_sim                          true
% 1.91/1.05  --prep_upred                            true
% 1.91/1.05  --prep_sem_filter                       exhaustive
% 1.91/1.05  --prep_sem_filter_out                   false
% 1.91/1.05  --pred_elim                             true
% 1.91/1.05  --res_sim_input                         true
% 1.91/1.05  --eq_ax_congr_red                       true
% 1.91/1.05  --pure_diseq_elim                       true
% 1.91/1.05  --brand_transform                       false
% 1.91/1.05  --non_eq_to_eq                          false
% 1.91/1.05  --prep_def_merge                        true
% 1.91/1.05  --prep_def_merge_prop_impl              false
% 1.91/1.05  --prep_def_merge_mbd                    true
% 1.91/1.05  --prep_def_merge_tr_red                 false
% 1.91/1.05  --prep_def_merge_tr_cl                  false
% 1.91/1.05  --smt_preprocessing                     true
% 1.91/1.05  --smt_ac_axioms                         fast
% 1.91/1.05  --preprocessed_out                      false
% 1.91/1.05  --preprocessed_stats                    false
% 1.91/1.05  
% 1.91/1.05  ------ Abstraction refinement Options
% 1.91/1.05  
% 1.91/1.05  --abstr_ref                             []
% 1.91/1.05  --abstr_ref_prep                        false
% 1.91/1.05  --abstr_ref_until_sat                   false
% 1.91/1.05  --abstr_ref_sig_restrict                funpre
% 1.91/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 1.91/1.05  --abstr_ref_under                       []
% 1.91/1.05  
% 1.91/1.05  ------ SAT Options
% 1.91/1.05  
% 1.91/1.05  --sat_mode                              false
% 1.91/1.05  --sat_fm_restart_options                ""
% 1.91/1.05  --sat_gr_def                            false
% 1.91/1.05  --sat_epr_types                         true
% 1.91/1.05  --sat_non_cyclic_types                  false
% 1.91/1.05  --sat_finite_models                     false
% 1.91/1.05  --sat_fm_lemmas                         false
% 1.91/1.05  --sat_fm_prep                           false
% 1.91/1.05  --sat_fm_uc_incr                        true
% 1.91/1.05  --sat_out_model                         small
% 1.91/1.05  --sat_out_clauses                       false
% 1.91/1.05  
% 1.91/1.05  ------ QBF Options
% 1.91/1.05  
% 1.91/1.05  --qbf_mode                              false
% 1.91/1.05  --qbf_elim_univ                         false
% 1.91/1.05  --qbf_dom_inst                          none
% 1.91/1.05  --qbf_dom_pre_inst                      false
% 1.91/1.05  --qbf_sk_in                             false
% 1.91/1.05  --qbf_pred_elim                         true
% 1.91/1.05  --qbf_split                             512
% 1.91/1.05  
% 1.91/1.05  ------ BMC1 Options
% 1.91/1.05  
% 1.91/1.05  --bmc1_incremental                      false
% 1.91/1.05  --bmc1_axioms                           reachable_all
% 1.91/1.05  --bmc1_min_bound                        0
% 1.91/1.05  --bmc1_max_bound                        -1
% 1.91/1.05  --bmc1_max_bound_default                -1
% 1.91/1.05  --bmc1_symbol_reachability              true
% 1.91/1.05  --bmc1_property_lemmas                  false
% 1.91/1.05  --bmc1_k_induction                      false
% 1.91/1.05  --bmc1_non_equiv_states                 false
% 1.91/1.05  --bmc1_deadlock                         false
% 1.91/1.05  --bmc1_ucm                              false
% 1.91/1.05  --bmc1_add_unsat_core                   none
% 1.91/1.05  --bmc1_unsat_core_children              false
% 1.91/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 1.91/1.05  --bmc1_out_stat                         full
% 1.91/1.05  --bmc1_ground_init                      false
% 1.91/1.05  --bmc1_pre_inst_next_state              false
% 1.91/1.05  --bmc1_pre_inst_state                   false
% 1.91/1.05  --bmc1_pre_inst_reach_state             false
% 1.91/1.05  --bmc1_out_unsat_core                   false
% 1.91/1.05  --bmc1_aig_witness_out                  false
% 1.91/1.05  --bmc1_verbose                          false
% 1.91/1.05  --bmc1_dump_clauses_tptp                false
% 1.91/1.05  --bmc1_dump_unsat_core_tptp             false
% 1.91/1.05  --bmc1_dump_file                        -
% 1.91/1.05  --bmc1_ucm_expand_uc_limit              128
% 1.91/1.05  --bmc1_ucm_n_expand_iterations          6
% 1.91/1.05  --bmc1_ucm_extend_mode                  1
% 1.91/1.05  --bmc1_ucm_init_mode                    2
% 1.91/1.05  --bmc1_ucm_cone_mode                    none
% 1.91/1.05  --bmc1_ucm_reduced_relation_type        0
% 1.91/1.05  --bmc1_ucm_relax_model                  4
% 1.91/1.05  --bmc1_ucm_full_tr_after_sat            true
% 1.91/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 1.91/1.05  --bmc1_ucm_layered_model                none
% 1.91/1.05  --bmc1_ucm_max_lemma_size               10
% 1.91/1.05  
% 1.91/1.05  ------ AIG Options
% 1.91/1.05  
% 1.91/1.05  --aig_mode                              false
% 1.91/1.05  
% 1.91/1.05  ------ Instantiation Options
% 1.91/1.05  
% 1.91/1.05  --instantiation_flag                    true
% 1.91/1.05  --inst_sos_flag                         false
% 1.91/1.05  --inst_sos_phase                        true
% 1.91/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.91/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.91/1.05  --inst_lit_sel_side                     none
% 1.91/1.05  --inst_solver_per_active                1400
% 1.91/1.05  --inst_solver_calls_frac                1.
% 1.91/1.05  --inst_passive_queue_type               priority_queues
% 1.91/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.91/1.05  --inst_passive_queues_freq              [25;2]
% 1.91/1.05  --inst_dismatching                      true
% 1.91/1.05  --inst_eager_unprocessed_to_passive     true
% 1.91/1.05  --inst_prop_sim_given                   true
% 1.91/1.05  --inst_prop_sim_new                     false
% 1.91/1.05  --inst_subs_new                         false
% 1.91/1.05  --inst_eq_res_simp                      false
% 1.91/1.05  --inst_subs_given                       false
% 1.91/1.05  --inst_orphan_elimination               true
% 1.91/1.05  --inst_learning_loop_flag               true
% 1.91/1.05  --inst_learning_start                   3000
% 1.91/1.05  --inst_learning_factor                  2
% 1.91/1.05  --inst_start_prop_sim_after_learn       3
% 1.91/1.05  --inst_sel_renew                        solver
% 1.91/1.05  --inst_lit_activity_flag                true
% 1.91/1.05  --inst_restr_to_given                   false
% 1.91/1.05  --inst_activity_threshold               500
% 1.91/1.05  --inst_out_proof                        true
% 1.91/1.05  
% 1.91/1.05  ------ Resolution Options
% 1.91/1.05  
% 1.91/1.05  --resolution_flag                       false
% 1.91/1.05  --res_lit_sel                           adaptive
% 1.91/1.05  --res_lit_sel_side                      none
% 1.91/1.05  --res_ordering                          kbo
% 1.91/1.05  --res_to_prop_solver                    active
% 1.91/1.05  --res_prop_simpl_new                    false
% 1.91/1.05  --res_prop_simpl_given                  true
% 1.91/1.05  --res_passive_queue_type                priority_queues
% 1.91/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.91/1.05  --res_passive_queues_freq               [15;5]
% 1.91/1.05  --res_forward_subs                      full
% 1.91/1.05  --res_backward_subs                     full
% 1.91/1.05  --res_forward_subs_resolution           true
% 1.91/1.05  --res_backward_subs_resolution          true
% 1.91/1.05  --res_orphan_elimination                true
% 1.91/1.05  --res_time_limit                        2.
% 1.91/1.05  --res_out_proof                         true
% 1.91/1.05  
% 1.91/1.05  ------ Superposition Options
% 1.91/1.05  
% 1.91/1.05  --superposition_flag                    true
% 1.91/1.05  --sup_passive_queue_type                priority_queues
% 1.91/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.91/1.05  --sup_passive_queues_freq               [8;1;4]
% 1.91/1.05  --demod_completeness_check              fast
% 1.91/1.05  --demod_use_ground                      true
% 1.91/1.05  --sup_to_prop_solver                    passive
% 1.91/1.05  --sup_prop_simpl_new                    true
% 1.91/1.05  --sup_prop_simpl_given                  true
% 1.91/1.05  --sup_fun_splitting                     false
% 1.91/1.05  --sup_smt_interval                      50000
% 1.91/1.05  
% 1.91/1.05  ------ Superposition Simplification Setup
% 1.91/1.05  
% 1.91/1.05  --sup_indices_passive                   []
% 1.91/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 1.91/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/1.05  --sup_full_bw                           [BwDemod]
% 1.91/1.05  --sup_immed_triv                        [TrivRules]
% 1.91/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.91/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/1.05  --sup_immed_bw_main                     []
% 1.91/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.91/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 1.91/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.91/1.05  
% 1.91/1.05  ------ Combination Options
% 1.91/1.05  
% 1.91/1.05  --comb_res_mult                         3
% 1.91/1.05  --comb_sup_mult                         2
% 1.91/1.05  --comb_inst_mult                        10
% 1.91/1.05  
% 1.91/1.05  ------ Debug Options
% 1.91/1.05  
% 1.91/1.05  --dbg_backtrace                         false
% 1.91/1.05  --dbg_dump_prop_clauses                 false
% 1.91/1.05  --dbg_dump_prop_clauses_file            -
% 1.91/1.05  --dbg_out_stat                          false
% 1.91/1.05  
% 1.91/1.05  
% 1.91/1.05  
% 1.91/1.05  
% 1.91/1.05  ------ Proving...
% 1.91/1.05  
% 1.91/1.05  
% 1.91/1.05  % SZS status Theorem for theBenchmark.p
% 1.91/1.05  
% 1.91/1.05   Resolution empty clause
% 1.91/1.05  
% 1.91/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 1.91/1.05  
% 1.91/1.05  fof(f17,conjecture,(
% 1.91/1.05    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 1.91/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.05  
% 1.91/1.05  fof(f18,negated_conjecture,(
% 1.91/1.05    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 1.91/1.05    inference(negated_conjecture,[],[f17])).
% 1.91/1.05  
% 1.91/1.05  fof(f31,plain,(
% 1.91/1.05    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 1.91/1.05    inference(ennf_transformation,[],[f18])).
% 1.91/1.05  
% 1.91/1.05  fof(f32,plain,(
% 1.91/1.05    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 1.91/1.05    inference(flattening,[],[f31])).
% 1.91/1.05  
% 1.91/1.05  fof(f43,plain,(
% 1.91/1.05    ( ! [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) => (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,sK3),X0) & m1_subset_1(sK3,X0))) )),
% 1.91/1.05    introduced(choice_axiom,[])).
% 1.91/1.05  
% 1.91/1.05  fof(f42,plain,(
% 1.91/1.05    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK2) & v1_subset_1(k6_domain_1(sK2,X1),sK2) & m1_subset_1(X1,sK2)) & ~v1_xboole_0(sK2))),
% 1.91/1.05    introduced(choice_axiom,[])).
% 1.91/1.05  
% 1.91/1.05  fof(f44,plain,(
% 1.91/1.05    (v1_zfmisc_1(sK2) & v1_subset_1(k6_domain_1(sK2,sK3),sK2) & m1_subset_1(sK3,sK2)) & ~v1_xboole_0(sK2)),
% 1.91/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f32,f43,f42])).
% 1.91/1.05  
% 1.91/1.05  fof(f67,plain,(
% 1.91/1.05    m1_subset_1(sK3,sK2)),
% 1.91/1.05    inference(cnf_transformation,[],[f44])).
% 1.91/1.05  
% 1.91/1.05  fof(f13,axiom,(
% 1.91/1.05    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 1.91/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.05  
% 1.91/1.05  fof(f27,plain,(
% 1.91/1.05    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.91/1.05    inference(ennf_transformation,[],[f13])).
% 1.91/1.05  
% 1.91/1.05  fof(f28,plain,(
% 1.91/1.05    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.91/1.05    inference(flattening,[],[f27])).
% 1.91/1.05  
% 1.91/1.05  fof(f61,plain,(
% 1.91/1.05    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.91/1.05    inference(cnf_transformation,[],[f28])).
% 1.91/1.05  
% 1.91/1.05  fof(f6,axiom,(
% 1.91/1.05    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.91/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.05  
% 1.91/1.05  fof(f53,plain,(
% 1.91/1.05    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.91/1.05    inference(cnf_transformation,[],[f6])).
% 1.91/1.05  
% 1.91/1.05  fof(f73,plain,(
% 1.91/1.05    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.91/1.05    inference(definition_unfolding,[],[f61,f53])).
% 1.91/1.05  
% 1.91/1.05  fof(f66,plain,(
% 1.91/1.05    ~v1_xboole_0(sK2)),
% 1.91/1.05    inference(cnf_transformation,[],[f44])).
% 1.91/1.05  
% 1.91/1.05  fof(f11,axiom,(
% 1.91/1.05    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.91/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.05  
% 1.91/1.05  fof(f24,plain,(
% 1.91/1.05    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.91/1.05    inference(ennf_transformation,[],[f11])).
% 1.91/1.05  
% 1.91/1.05  fof(f25,plain,(
% 1.91/1.05    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.91/1.05    inference(flattening,[],[f24])).
% 1.91/1.05  
% 1.91/1.05  fof(f59,plain,(
% 1.91/1.05    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.91/1.05    inference(cnf_transformation,[],[f25])).
% 1.91/1.05  
% 1.91/1.05  fof(f8,axiom,(
% 1.91/1.05    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.91/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.05  
% 1.91/1.05  fof(f41,plain,(
% 1.91/1.05    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.91/1.05    inference(nnf_transformation,[],[f8])).
% 1.91/1.05  
% 1.91/1.05  fof(f55,plain,(
% 1.91/1.05    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.91/1.05    inference(cnf_transformation,[],[f41])).
% 1.91/1.05  
% 1.91/1.05  fof(f16,axiom,(
% 1.91/1.05    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.91/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.05  
% 1.91/1.05  fof(f29,plain,(
% 1.91/1.05    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.91/1.05    inference(ennf_transformation,[],[f16])).
% 1.91/1.05  
% 1.91/1.05  fof(f30,plain,(
% 1.91/1.05    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.91/1.05    inference(flattening,[],[f29])).
% 1.91/1.05  
% 1.91/1.05  fof(f65,plain,(
% 1.91/1.05    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.91/1.05    inference(cnf_transformation,[],[f30])).
% 1.91/1.05  
% 1.91/1.05  fof(f69,plain,(
% 1.91/1.05    v1_zfmisc_1(sK2)),
% 1.91/1.05    inference(cnf_transformation,[],[f44])).
% 1.91/1.05  
% 1.91/1.05  fof(f68,plain,(
% 1.91/1.05    v1_subset_1(k6_domain_1(sK2,sK3),sK2)),
% 1.91/1.05    inference(cnf_transformation,[],[f44])).
% 1.91/1.05  
% 1.91/1.05  fof(f10,axiom,(
% 1.91/1.05    ! [X0] : (l1_struct_0(X0) => ~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)))),
% 1.91/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.05  
% 1.91/1.05  fof(f23,plain,(
% 1.91/1.05    ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0))),
% 1.91/1.05    inference(ennf_transformation,[],[f10])).
% 1.91/1.05  
% 1.91/1.05  fof(f58,plain,(
% 1.91/1.05    ( ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 1.91/1.05    inference(cnf_transformation,[],[f23])).
% 1.91/1.05  
% 1.91/1.05  fof(f12,axiom,(
% 1.91/1.05    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 1.91/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.05  
% 1.91/1.05  fof(f26,plain,(
% 1.91/1.05    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 1.91/1.05    inference(ennf_transformation,[],[f12])).
% 1.91/1.05  
% 1.91/1.05  fof(f60,plain,(
% 1.91/1.05    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 1.91/1.05    inference(cnf_transformation,[],[f26])).
% 1.91/1.05  
% 1.91/1.05  fof(f14,axiom,(
% 1.91/1.05    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 1.91/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.05  
% 1.91/1.05  fof(f19,plain,(
% 1.91/1.05    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 1.91/1.05    inference(pure_predicate_removal,[],[f14])).
% 1.91/1.05  
% 1.91/1.05  fof(f62,plain,(
% 1.91/1.05    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 1.91/1.05    inference(cnf_transformation,[],[f19])).
% 1.91/1.05  
% 1.91/1.05  fof(f15,axiom,(
% 1.91/1.05    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 1.91/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.05  
% 1.91/1.05  fof(f63,plain,(
% 1.91/1.05    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 1.91/1.05    inference(cnf_transformation,[],[f15])).
% 1.91/1.05  
% 1.91/1.05  fof(f9,axiom,(
% 1.91/1.05    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.91/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.05  
% 1.91/1.05  fof(f22,plain,(
% 1.91/1.05    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.91/1.05    inference(ennf_transformation,[],[f9])).
% 1.91/1.05  
% 1.91/1.05  fof(f57,plain,(
% 1.91/1.05    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.91/1.05    inference(cnf_transformation,[],[f22])).
% 1.91/1.05  
% 1.91/1.05  fof(f2,axiom,(
% 1.91/1.05    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.91/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.05  
% 1.91/1.05  fof(f20,plain,(
% 1.91/1.05    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.91/1.05    inference(ennf_transformation,[],[f2])).
% 1.91/1.05  
% 1.91/1.05  fof(f37,plain,(
% 1.91/1.05    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.91/1.05    inference(nnf_transformation,[],[f20])).
% 1.91/1.05  
% 1.91/1.05  fof(f38,plain,(
% 1.91/1.05    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.91/1.05    inference(rectify,[],[f37])).
% 1.91/1.05  
% 1.91/1.05  fof(f39,plain,(
% 1.91/1.05    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 1.91/1.05    introduced(choice_axiom,[])).
% 1.91/1.05  
% 1.91/1.05  fof(f40,plain,(
% 1.91/1.05    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.91/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).
% 1.91/1.05  
% 1.91/1.05  fof(f48,plain,(
% 1.91/1.05    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 1.91/1.05    inference(cnf_transformation,[],[f40])).
% 1.91/1.05  
% 1.91/1.05  fof(f1,axiom,(
% 1.91/1.05    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.91/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.05  
% 1.91/1.05  fof(f33,plain,(
% 1.91/1.05    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.91/1.05    inference(nnf_transformation,[],[f1])).
% 1.91/1.05  
% 1.91/1.05  fof(f34,plain,(
% 1.91/1.05    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.91/1.05    inference(rectify,[],[f33])).
% 1.91/1.05  
% 1.91/1.05  fof(f35,plain,(
% 1.91/1.05    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.91/1.05    introduced(choice_axiom,[])).
% 1.91/1.05  
% 1.91/1.05  fof(f36,plain,(
% 1.91/1.05    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.91/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 1.91/1.05  
% 1.91/1.05  fof(f45,plain,(
% 1.91/1.05    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.91/1.05    inference(cnf_transformation,[],[f36])).
% 1.91/1.05  
% 1.91/1.05  fof(f4,axiom,(
% 1.91/1.05    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.91/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.05  
% 1.91/1.05  fof(f21,plain,(
% 1.91/1.05    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.91/1.05    inference(ennf_transformation,[],[f4])).
% 1.91/1.05  
% 1.91/1.05  fof(f51,plain,(
% 1.91/1.05    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.91/1.05    inference(cnf_transformation,[],[f21])).
% 1.91/1.05  
% 1.91/1.05  fof(f5,axiom,(
% 1.91/1.05    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.91/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.05  
% 1.91/1.05  fof(f52,plain,(
% 1.91/1.05    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.91/1.05    inference(cnf_transformation,[],[f5])).
% 1.91/1.05  
% 1.91/1.05  fof(f3,axiom,(
% 1.91/1.05    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.91/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.05  
% 1.91/1.05  fof(f50,plain,(
% 1.91/1.05    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.91/1.05    inference(cnf_transformation,[],[f3])).
% 1.91/1.05  
% 1.91/1.05  fof(f70,plain,(
% 1.91/1.05    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 1.91/1.05    inference(definition_unfolding,[],[f52,f50])).
% 1.91/1.05  
% 1.91/1.05  fof(f71,plain,(
% 1.91/1.05    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 | ~r1_tarski(X0,X1)) )),
% 1.91/1.05    inference(definition_unfolding,[],[f51,f70])).
% 1.91/1.05  
% 1.91/1.05  fof(f7,axiom,(
% 1.91/1.05    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 1.91/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.05  
% 1.91/1.05  fof(f54,plain,(
% 1.91/1.05    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 1.91/1.05    inference(cnf_transformation,[],[f7])).
% 1.91/1.05  
% 1.91/1.05  fof(f72,plain,(
% 1.91/1.05    ( ! [X0,X1] : (k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,k2_tarski(X0,X0)))) != k1_xboole_0) )),
% 1.91/1.05    inference(definition_unfolding,[],[f54,f70,f53])).
% 1.91/1.05  
% 1.91/1.05  cnf(c_19,negated_conjecture,
% 1.91/1.05      ( m1_subset_1(sK3,sK2) ),
% 1.91/1.05      inference(cnf_transformation,[],[f67]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_1419,plain,
% 1.91/1.05      ( m1_subset_1(sK3,sK2) = iProver_top ),
% 1.91/1.05      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_13,plain,
% 1.91/1.05      ( ~ m1_subset_1(X0,X1)
% 1.91/1.05      | v1_xboole_0(X1)
% 1.91/1.05      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 1.91/1.05      inference(cnf_transformation,[],[f73]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_1421,plain,
% 1.91/1.05      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
% 1.91/1.05      | m1_subset_1(X1,X0) != iProver_top
% 1.91/1.05      | v1_xboole_0(X0) = iProver_top ),
% 1.91/1.05      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_1792,plain,
% 1.91/1.05      ( k6_domain_1(sK2,sK3) = k2_tarski(sK3,sK3)
% 1.91/1.05      | v1_xboole_0(sK2) = iProver_top ),
% 1.91/1.05      inference(superposition,[status(thm)],[c_1419,c_1421]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_20,negated_conjecture,
% 1.91/1.05      ( ~ v1_xboole_0(sK2) ),
% 1.91/1.05      inference(cnf_transformation,[],[f66]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_1554,plain,
% 1.91/1.05      ( ~ m1_subset_1(sK3,sK2)
% 1.91/1.05      | v1_xboole_0(sK2)
% 1.91/1.05      | k6_domain_1(sK2,sK3) = k2_tarski(sK3,sK3) ),
% 1.91/1.05      inference(instantiation,[status(thm)],[c_13]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_2005,plain,
% 1.91/1.05      ( k6_domain_1(sK2,sK3) = k2_tarski(sK3,sK3) ),
% 1.91/1.05      inference(global_propositional_subsumption,
% 1.91/1.05                [status(thm)],
% 1.91/1.05                [c_1792,c_20,c_19,c_1554]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_11,plain,
% 1.91/1.05      ( ~ m1_subset_1(X0,X1)
% 1.91/1.05      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 1.91/1.05      | v1_xboole_0(X1) ),
% 1.91/1.05      inference(cnf_transformation,[],[f59]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_1422,plain,
% 1.91/1.05      ( m1_subset_1(X0,X1) != iProver_top
% 1.91/1.05      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
% 1.91/1.05      | v1_xboole_0(X1) = iProver_top ),
% 1.91/1.05      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_2183,plain,
% 1.91/1.05      ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(sK2)) = iProver_top
% 1.91/1.05      | m1_subset_1(sK3,sK2) != iProver_top
% 1.91/1.05      | v1_xboole_0(sK2) = iProver_top ),
% 1.91/1.05      inference(superposition,[status(thm)],[c_2005,c_1422]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_21,plain,
% 1.91/1.05      ( v1_xboole_0(sK2) != iProver_top ),
% 1.91/1.05      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_22,plain,
% 1.91/1.05      ( m1_subset_1(sK3,sK2) = iProver_top ),
% 1.91/1.05      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_2457,plain,
% 1.91/1.05      ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(sK2)) = iProver_top ),
% 1.91/1.05      inference(global_propositional_subsumption,
% 1.91/1.05                [status(thm)],
% 1.91/1.05                [c_2183,c_21,c_22]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_8,plain,
% 1.91/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 1.91/1.05      inference(cnf_transformation,[],[f55]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_1423,plain,
% 1.91/1.05      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 1.91/1.05      | r1_tarski(X0,X1) = iProver_top ),
% 1.91/1.05      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_2462,plain,
% 1.91/1.05      ( r1_tarski(k2_tarski(sK3,sK3),sK2) = iProver_top ),
% 1.91/1.05      inference(superposition,[status(thm)],[c_2457,c_1423]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_16,plain,
% 1.91/1.05      ( ~ r1_tarski(X0,X1)
% 1.91/1.05      | ~ v1_zfmisc_1(X1)
% 1.91/1.05      | v1_xboole_0(X0)
% 1.91/1.05      | v1_xboole_0(X1)
% 1.91/1.05      | X1 = X0 ),
% 1.91/1.05      inference(cnf_transformation,[],[f65]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_17,negated_conjecture,
% 1.91/1.05      ( v1_zfmisc_1(sK2) ),
% 1.91/1.05      inference(cnf_transformation,[],[f69]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_317,plain,
% 1.91/1.05      ( ~ r1_tarski(X0,X1)
% 1.91/1.05      | v1_xboole_0(X0)
% 1.91/1.05      | v1_xboole_0(X1)
% 1.91/1.05      | X1 = X0
% 1.91/1.05      | sK2 != X1 ),
% 1.91/1.05      inference(resolution_lifted,[status(thm)],[c_16,c_17]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_318,plain,
% 1.91/1.05      ( ~ r1_tarski(X0,sK2) | v1_xboole_0(X0) | v1_xboole_0(sK2) | sK2 = X0 ),
% 1.91/1.05      inference(unflattening,[status(thm)],[c_317]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_322,plain,
% 1.91/1.05      ( v1_xboole_0(X0) | ~ r1_tarski(X0,sK2) | sK2 = X0 ),
% 1.91/1.05      inference(global_propositional_subsumption,[status(thm)],[c_318,c_20]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_323,plain,
% 1.91/1.05      ( ~ r1_tarski(X0,sK2) | v1_xboole_0(X0) | sK2 = X0 ),
% 1.91/1.05      inference(renaming,[status(thm)],[c_322]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_1416,plain,
% 1.91/1.05      ( sK2 = X0
% 1.91/1.05      | r1_tarski(X0,sK2) != iProver_top
% 1.91/1.05      | v1_xboole_0(X0) = iProver_top ),
% 1.91/1.05      inference(predicate_to_equality,[status(thm)],[c_323]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_2555,plain,
% 1.91/1.05      ( k2_tarski(sK3,sK3) = sK2
% 1.91/1.05      | v1_xboole_0(k2_tarski(sK3,sK3)) = iProver_top ),
% 1.91/1.05      inference(superposition,[status(thm)],[c_2462,c_1416]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_18,negated_conjecture,
% 1.91/1.05      ( v1_subset_1(k6_domain_1(sK2,sK3),sK2) ),
% 1.91/1.05      inference(cnf_transformation,[],[f68]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_1002,plain,( X0 = X0 ),theory(equality) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_1025,plain,
% 1.91/1.05      ( sK2 = sK2 ),
% 1.91/1.05      inference(instantiation,[status(thm)],[c_1002]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_10,plain,
% 1.91/1.05      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~ l1_struct_0(X0) ),
% 1.91/1.05      inference(cnf_transformation,[],[f58]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_12,plain,
% 1.91/1.05      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 1.91/1.05      inference(cnf_transformation,[],[f60]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_14,plain,
% 1.91/1.05      ( l1_orders_2(k2_yellow_1(X0)) ),
% 1.91/1.05      inference(cnf_transformation,[],[f62]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_278,plain,
% 1.91/1.05      ( l1_struct_0(X0) | k2_yellow_1(X1) != X0 ),
% 1.91/1.05      inference(resolution_lifted,[status(thm)],[c_12,c_14]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_279,plain,
% 1.91/1.05      ( l1_struct_0(k2_yellow_1(X0)) ),
% 1.91/1.05      inference(unflattening,[status(thm)],[c_278]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_289,plain,
% 1.91/1.05      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
% 1.91/1.05      | k2_yellow_1(X1) != X0 ),
% 1.91/1.05      inference(resolution_lifted,[status(thm)],[c_10,c_279]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_290,plain,
% 1.91/1.05      ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(X0)),u1_struct_0(k2_yellow_1(X0))) ),
% 1.91/1.05      inference(unflattening,[status(thm)],[c_289]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_1417,plain,
% 1.91/1.05      ( v1_subset_1(k2_struct_0(k2_yellow_1(X0)),u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
% 1.91/1.05      inference(predicate_to_equality,[status(thm)],[c_290]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_15,plain,
% 1.91/1.05      ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
% 1.91/1.05      inference(cnf_transformation,[],[f63]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_9,plain,
% 1.91/1.05      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.91/1.05      inference(cnf_transformation,[],[f57]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_298,plain,
% 1.91/1.05      ( k2_yellow_1(X0) != X1 | u1_struct_0(X1) = k2_struct_0(X1) ),
% 1.91/1.05      inference(resolution_lifted,[status(thm)],[c_9,c_279]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_299,plain,
% 1.91/1.05      ( u1_struct_0(k2_yellow_1(X0)) = k2_struct_0(k2_yellow_1(X0)) ),
% 1.91/1.05      inference(unflattening,[status(thm)],[c_298]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_1437,plain,
% 1.91/1.05      ( k2_struct_0(k2_yellow_1(X0)) = X0 ),
% 1.91/1.05      inference(light_normalisation,[status(thm)],[c_299,c_15]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_1442,plain,
% 1.91/1.05      ( v1_subset_1(X0,X0) != iProver_top ),
% 1.91/1.05      inference(light_normalisation,[status(thm)],[c_1417,c_15,c_1437]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_1511,plain,
% 1.91/1.05      ( ~ v1_subset_1(X0,X0) ),
% 1.91/1.05      inference(predicate_to_equality_rev,[status(thm)],[c_1442]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_1513,plain,
% 1.91/1.05      ( ~ v1_subset_1(sK2,sK2) ),
% 1.91/1.05      inference(instantiation,[status(thm)],[c_1511]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_1012,plain,
% 1.91/1.05      ( ~ v1_subset_1(X0,X1) | v1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.91/1.05      theory(equality) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_1567,plain,
% 1.91/1.05      ( v1_subset_1(X0,X1)
% 1.91/1.05      | ~ v1_subset_1(k6_domain_1(sK2,sK3),sK2)
% 1.91/1.05      | X0 != k6_domain_1(sK2,sK3)
% 1.91/1.05      | X1 != sK2 ),
% 1.91/1.05      inference(instantiation,[status(thm)],[c_1012]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_1569,plain,
% 1.91/1.05      ( ~ v1_subset_1(k6_domain_1(sK2,sK3),sK2)
% 1.91/1.05      | v1_subset_1(sK2,sK2)
% 1.91/1.05      | sK2 != k6_domain_1(sK2,sK3)
% 1.91/1.05      | sK2 != sK2 ),
% 1.91/1.05      inference(instantiation,[status(thm)],[c_1567]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_1003,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_1644,plain,
% 1.91/1.05      ( X0 != X1 | X0 = k6_domain_1(sK2,sK3) | k6_domain_1(sK2,sK3) != X1 ),
% 1.91/1.05      inference(instantiation,[status(thm)],[c_1003]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_1801,plain,
% 1.91/1.05      ( X0 = k6_domain_1(sK2,sK3)
% 1.91/1.05      | X0 != k2_tarski(sK3,sK3)
% 1.91/1.05      | k6_domain_1(sK2,sK3) != k2_tarski(sK3,sK3) ),
% 1.91/1.05      inference(instantiation,[status(thm)],[c_1644]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_1802,plain,
% 1.91/1.05      ( k6_domain_1(sK2,sK3) != k2_tarski(sK3,sK3)
% 1.91/1.05      | sK2 = k6_domain_1(sK2,sK3)
% 1.91/1.05      | sK2 != k2_tarski(sK3,sK3) ),
% 1.91/1.05      inference(instantiation,[status(thm)],[c_1801]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_1948,plain,
% 1.91/1.05      ( ~ r1_tarski(k2_tarski(sK3,sK3),sK2)
% 1.91/1.05      | v1_xboole_0(k2_tarski(sK3,sK3))
% 1.91/1.05      | sK2 = k2_tarski(sK3,sK3) ),
% 1.91/1.05      inference(instantiation,[status(thm)],[c_323]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_1949,plain,
% 1.91/1.05      ( sK2 = k2_tarski(sK3,sK3)
% 1.91/1.05      | r1_tarski(k2_tarski(sK3,sK3),sK2) != iProver_top
% 1.91/1.05      | v1_xboole_0(k2_tarski(sK3,sK3)) = iProver_top ),
% 1.91/1.05      inference(predicate_to_equality,[status(thm)],[c_1948]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_1961,plain,
% 1.91/1.05      ( ~ m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(sK2))
% 1.91/1.05      | r1_tarski(k2_tarski(sK3,sK3),sK2) ),
% 1.91/1.05      inference(instantiation,[status(thm)],[c_8]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_1962,plain,
% 1.91/1.05      ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(sK2)) != iProver_top
% 1.91/1.05      | r1_tarski(k2_tarski(sK3,sK3),sK2) = iProver_top ),
% 1.91/1.05      inference(predicate_to_equality,[status(thm)],[c_1961]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_2571,plain,
% 1.91/1.05      ( v1_xboole_0(k2_tarski(sK3,sK3)) = iProver_top ),
% 1.91/1.05      inference(global_propositional_subsumption,
% 1.91/1.05                [status(thm)],
% 1.91/1.05                [c_2555,c_20,c_21,c_19,c_22,c_18,c_1025,c_1513,c_1554,c_1569,
% 1.91/1.05                 c_1802,c_1949,c_1962,c_2183]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_3,plain,
% 1.91/1.05      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 1.91/1.05      inference(cnf_transformation,[],[f48]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_1427,plain,
% 1.91/1.05      ( r1_tarski(X0,X1) = iProver_top
% 1.91/1.05      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 1.91/1.05      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_1,plain,
% 1.91/1.05      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 1.91/1.05      inference(cnf_transformation,[],[f45]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_1429,plain,
% 1.91/1.05      ( r2_hidden(X0,X1) != iProver_top | v1_xboole_0(X1) != iProver_top ),
% 1.91/1.05      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_2096,plain,
% 1.91/1.05      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 1.91/1.05      inference(superposition,[status(thm)],[c_1427,c_1429]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_5,plain,
% 1.91/1.05      ( ~ r1_tarski(X0,X1)
% 1.91/1.05      | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 ),
% 1.91/1.05      inference(cnf_transformation,[],[f71]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_1425,plain,
% 1.91/1.05      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1
% 1.91/1.05      | r1_tarski(X0,X1) != iProver_top ),
% 1.91/1.05      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_2376,plain,
% 1.91/1.05      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1
% 1.91/1.05      | v1_xboole_0(X0) != iProver_top ),
% 1.91/1.05      inference(superposition,[status(thm)],[c_2096,c_1425]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_2576,plain,
% 1.91/1.05      ( k5_xboole_0(k2_tarski(sK3,sK3),k5_xboole_0(X0,k3_xboole_0(X0,k2_tarski(sK3,sK3)))) = X0 ),
% 1.91/1.05      inference(superposition,[status(thm)],[c_2571,c_2376]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_6,plain,
% 1.91/1.05      ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,k2_tarski(X0,X0)))) != k1_xboole_0 ),
% 1.91/1.05      inference(cnf_transformation,[],[f72]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_2647,plain,
% 1.91/1.05      ( k1_xboole_0 != X0 ),
% 1.91/1.05      inference(superposition,[status(thm)],[c_2576,c_6]) ).
% 1.91/1.05  
% 1.91/1.05  cnf(c_2746,plain,
% 1.91/1.05      ( $false ),
% 1.91/1.05      inference(equality_resolution,[status(thm)],[c_2647]) ).
% 1.91/1.05  
% 1.91/1.05  
% 1.91/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 1.91/1.05  
% 1.91/1.05  ------                               Statistics
% 1.91/1.05  
% 1.91/1.05  ------ General
% 1.91/1.05  
% 1.91/1.05  abstr_ref_over_cycles:                  0
% 1.91/1.05  abstr_ref_under_cycles:                 0
% 1.91/1.05  gc_basic_clause_elim:                   0
% 1.91/1.05  forced_gc_time:                         0
% 1.91/1.05  parsing_time:                           0.012
% 1.91/1.05  unif_index_cands_time:                  0.
% 1.91/1.05  unif_index_add_time:                    0.
% 1.91/1.05  orderings_time:                         0.
% 1.91/1.05  out_proof_time:                         0.011
% 1.91/1.05  total_time:                             0.139
% 1.91/1.05  num_of_symbols:                         52
% 1.91/1.05  num_of_terms:                           2243
% 1.91/1.05  
% 1.91/1.05  ------ Preprocessing
% 1.91/1.05  
% 1.91/1.05  num_of_splits:                          0
% 1.91/1.05  num_of_split_atoms:                     0
% 1.91/1.05  num_of_reused_defs:                     0
% 1.91/1.05  num_eq_ax_congr_red:                    33
% 1.91/1.05  num_of_sem_filtered_clauses:            1
% 1.91/1.05  num_of_subtypes:                        0
% 1.91/1.05  monotx_restored_types:                  0
% 1.91/1.05  sat_num_of_epr_types:                   0
% 1.91/1.05  sat_num_of_non_cyclic_types:            0
% 1.91/1.05  sat_guarded_non_collapsed_types:        0
% 1.91/1.05  num_pure_diseq_elim:                    0
% 1.91/1.05  simp_replaced_by:                       0
% 1.91/1.05  res_preprocessed:                       100
% 1.91/1.05  prep_upred:                             0
% 1.91/1.05  prep_unflattend:                        28
% 1.91/1.05  smt_new_axioms:                         0
% 1.91/1.05  pred_elim_cands:                        5
% 1.91/1.05  pred_elim:                              3
% 1.91/1.05  pred_elim_cl:                           3
% 1.91/1.05  pred_elim_cycles:                       10
% 1.91/1.05  merged_defs:                            8
% 1.91/1.05  merged_defs_ncl:                        0
% 1.91/1.05  bin_hyper_res:                          8
% 1.91/1.05  prep_cycles:                            4
% 1.91/1.05  pred_elim_time:                         0.007
% 1.91/1.05  splitting_time:                         0.
% 1.91/1.05  sem_filter_time:                        0.
% 1.91/1.05  monotx_time:                            0.
% 1.91/1.05  subtype_inf_time:                       0.
% 1.91/1.05  
% 1.91/1.05  ------ Problem properties
% 1.91/1.05  
% 1.91/1.05  clauses:                                18
% 1.91/1.05  conjectures:                            3
% 1.91/1.05  epr:                                    5
% 1.91/1.05  horn:                                   13
% 1.91/1.05  ground:                                 3
% 1.91/1.05  unary:                                  7
% 1.91/1.05  binary:                                 7
% 1.91/1.05  lits:                                   33
% 1.91/1.05  lits_eq:                                6
% 1.91/1.05  fd_pure:                                0
% 1.91/1.05  fd_pseudo:                              0
% 1.91/1.05  fd_cond:                                1
% 1.91/1.05  fd_pseudo_cond:                         0
% 1.91/1.05  ac_symbols:                             0
% 1.91/1.05  
% 1.91/1.05  ------ Propositional Solver
% 1.91/1.05  
% 1.91/1.05  prop_solver_calls:                      27
% 1.91/1.05  prop_fast_solver_calls:                 575
% 1.91/1.05  smt_solver_calls:                       0
% 1.91/1.05  smt_fast_solver_calls:                  0
% 1.91/1.05  prop_num_of_clauses:                    878
% 1.91/1.05  prop_preprocess_simplified:             3718
% 1.91/1.05  prop_fo_subsumed:                       5
% 1.91/1.05  prop_solver_time:                       0.
% 1.91/1.05  smt_solver_time:                        0.
% 1.91/1.05  smt_fast_solver_time:                   0.
% 1.91/1.05  prop_fast_solver_time:                  0.
% 1.91/1.05  prop_unsat_core_time:                   0.
% 1.91/1.05  
% 1.91/1.05  ------ QBF
% 1.91/1.05  
% 1.91/1.05  qbf_q_res:                              0
% 1.91/1.05  qbf_num_tautologies:                    0
% 1.91/1.05  qbf_prep_cycles:                        0
% 1.91/1.05  
% 1.91/1.05  ------ BMC1
% 1.91/1.05  
% 1.91/1.05  bmc1_current_bound:                     -1
% 1.91/1.05  bmc1_last_solved_bound:                 -1
% 1.91/1.05  bmc1_unsat_core_size:                   -1
% 1.91/1.05  bmc1_unsat_core_parents_size:           -1
% 1.91/1.05  bmc1_merge_next_fun:                    0
% 1.91/1.05  bmc1_unsat_core_clauses_time:           0.
% 1.91/1.05  
% 1.91/1.05  ------ Instantiation
% 1.91/1.05  
% 1.91/1.05  inst_num_of_clauses:                    261
% 1.91/1.05  inst_num_in_passive:                    82
% 1.91/1.05  inst_num_in_active:                     138
% 1.91/1.05  inst_num_in_unprocessed:                41
% 1.91/1.05  inst_num_of_loops:                      160
% 1.91/1.05  inst_num_of_learning_restarts:          0
% 1.91/1.05  inst_num_moves_active_passive:          19
% 1.91/1.05  inst_lit_activity:                      0
% 1.91/1.05  inst_lit_activity_moves:                0
% 1.91/1.05  inst_num_tautologies:                   0
% 1.91/1.05  inst_num_prop_implied:                  0
% 1.91/1.05  inst_num_existing_simplified:           0
% 1.91/1.05  inst_num_eq_res_simplified:             0
% 1.91/1.05  inst_num_child_elim:                    0
% 1.91/1.05  inst_num_of_dismatching_blockings:      26
% 1.91/1.05  inst_num_of_non_proper_insts:           175
% 1.91/1.05  inst_num_of_duplicates:                 0
% 1.91/1.05  inst_inst_num_from_inst_to_res:         0
% 1.91/1.05  inst_dismatching_checking_time:         0.
% 1.91/1.05  
% 1.91/1.05  ------ Resolution
% 1.91/1.05  
% 1.91/1.05  res_num_of_clauses:                     0
% 1.91/1.05  res_num_in_passive:                     0
% 1.91/1.05  res_num_in_active:                      0
% 1.91/1.05  res_num_of_loops:                       104
% 1.91/1.05  res_forward_subset_subsumed:            5
% 1.91/1.05  res_backward_subset_subsumed:           0
% 1.91/1.05  res_forward_subsumed:                   0
% 1.91/1.05  res_backward_subsumed:                  0
% 1.91/1.05  res_forward_subsumption_resolution:     0
% 1.91/1.05  res_backward_subsumption_resolution:    0
% 1.91/1.05  res_clause_to_clause_subsumption:       82
% 1.91/1.05  res_orphan_elimination:                 0
% 1.91/1.05  res_tautology_del:                      42
% 1.91/1.05  res_num_eq_res_simplified:              0
% 1.91/1.05  res_num_sel_changes:                    0
% 1.91/1.05  res_moves_from_active_to_pass:          0
% 1.91/1.05  
% 1.91/1.05  ------ Superposition
% 1.91/1.05  
% 1.91/1.05  sup_time_total:                         0.
% 1.91/1.05  sup_time_generating:                    0.
% 1.91/1.05  sup_time_sim_full:                      0.
% 1.91/1.05  sup_time_sim_immed:                     0.
% 1.91/1.05  
% 1.91/1.05  sup_num_of_clauses:                     37
% 1.91/1.05  sup_num_in_active:                      30
% 1.91/1.05  sup_num_in_passive:                     7
% 1.91/1.05  sup_num_of_loops:                       30
% 1.91/1.05  sup_fw_superposition:                   2
% 1.91/1.05  sup_bw_superposition:                   22
% 1.91/1.05  sup_immediate_simplified:               1
% 1.91/1.05  sup_given_eliminated:                   0
% 1.91/1.05  comparisons_done:                       0
% 1.91/1.05  comparisons_avoided:                    0
% 1.91/1.05  
% 1.91/1.05  ------ Simplifications
% 1.91/1.05  
% 1.91/1.05  
% 1.91/1.05  sim_fw_subset_subsumed:                 0
% 1.91/1.05  sim_bw_subset_subsumed:                 0
% 1.91/1.05  sim_fw_subsumed:                        1
% 1.91/1.05  sim_bw_subsumed:                        0
% 1.91/1.05  sim_fw_subsumption_res:                 0
% 1.91/1.05  sim_bw_subsumption_res:                 0
% 1.91/1.05  sim_tautology_del:                      4
% 1.91/1.05  sim_eq_tautology_del:                   1
% 1.91/1.05  sim_eq_res_simp:                        0
% 1.91/1.05  sim_fw_demodulated:                     0
% 1.91/1.05  sim_bw_demodulated:                     1
% 1.91/1.05  sim_light_normalised:                   2
% 1.91/1.05  sim_joinable_taut:                      0
% 1.91/1.05  sim_joinable_simp:                      0
% 1.91/1.05  sim_ac_normalised:                      0
% 1.91/1.05  sim_smt_subsumption:                    0
% 1.91/1.05  
%------------------------------------------------------------------------------
