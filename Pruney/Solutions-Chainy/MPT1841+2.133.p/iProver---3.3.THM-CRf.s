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
% DateTime   : Thu Dec  3 12:25:14 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 389 expanded)
%              Number of clauses        :   80 ( 121 expanded)
%              Number of leaves         :   23 (  94 expanded)
%              Depth                    :   16
%              Number of atoms          :  360 (1217 expanded)
%              Number of equality atoms :  125 ( 208 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
     => ( v1_zfmisc_1(X0)
        & v1_subset_1(k6_domain_1(X0,sK2),X0)
        & m1_subset_1(sK2,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_zfmisc_1(X0)
            & v1_subset_1(k6_domain_1(X0,X1),X0)
            & m1_subset_1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( v1_zfmisc_1(sK1)
          & v1_subset_1(k6_domain_1(sK1,X1),sK1)
          & m1_subset_1(X1,sK1) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( v1_zfmisc_1(sK1)
    & v1_subset_1(k6_domain_1(sK1,sK2),sK1)
    & m1_subset_1(sK2,sK1)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f33,f42,f41])).

fof(f68,plain,(
    m1_subset_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

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
    inference(definition_unfolding,[],[f62,f53])).

fof(f67,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

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

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f17,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f66,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f70,plain,(
    v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f69,plain,(
    v1_subset_1(k6_domain_1(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f75,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f61,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f63,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f16,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f58,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f74,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f71,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f50,f52])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f72,plain,(
    ! [X0,X1] : k1_xboole_0 != k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(X1,k2_tarski(X0,X0))) ),
    inference(definition_unfolding,[],[f54,f52,f53])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1122,plain,
    ( m1_subset_1(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1124,plain,
    ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1952,plain,
    ( k6_domain_1(sK1,sK2) = k2_tarski(sK2,sK2)
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1122,c_1124])).

cnf(c_23,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1265,plain,
    ( ~ m1_subset_1(sK2,sK1)
    | v1_xboole_0(sK1)
    | k6_domain_1(sK1,sK2) = k2_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2169,plain,
    ( k6_domain_1(sK1,sK2) = k2_tarski(sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1952,c_23,c_22,c_1265])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1125,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2174,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK2,sK1) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2169,c_1125])).

cnf(c_24,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_25,plain,
    ( m1_subset_1(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2357,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2174,c_24,c_25])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1126,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2362,plain,
    ( r1_tarski(k2_tarski(sK2,sK2),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2357,c_1126])).

cnf(c_19,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_20,negated_conjecture,
    ( v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_333,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | X1 = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_20])).

cnf(c_334,plain,
    ( ~ r1_tarski(X0,sK1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | sK1 = X0 ),
    inference(unflattening,[status(thm)],[c_333])).

cnf(c_336,plain,
    ( v1_xboole_0(X0)
    | ~ r1_tarski(X0,sK1)
    | sK1 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_334,c_23])).

cnf(c_337,plain,
    ( ~ r1_tarski(X0,sK1)
    | v1_xboole_0(X0)
    | sK1 = X0 ),
    inference(renaming,[status(thm)],[c_336])).

cnf(c_1118,plain,
    ( sK1 = X0
    | r1_tarski(X0,sK1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_337])).

cnf(c_2510,plain,
    ( k2_tarski(sK2,sK2) = sK1
    | v1_xboole_0(k2_tarski(sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2362,c_1118])).

cnf(c_21,negated_conjecture,
    ( v1_subset_1(k6_domain_1(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_29,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ v1_zfmisc_1(sK1)
    | v1_xboole_0(sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_63,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_13,plain,
    ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_15,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_17,plain,
    ( l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_294,plain,
    ( l1_struct_0(X0)
    | k2_yellow_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_17])).

cnf(c_295,plain,
    ( l1_struct_0(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_294])).

cnf(c_305,plain,
    ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
    | k2_yellow_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_295])).

cnf(c_306,plain,
    ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(X0)),u1_struct_0(k2_yellow_1(X0))) ),
    inference(unflattening,[status(thm)],[c_305])).

cnf(c_1119,plain,
    ( v1_subset_1(k2_struct_0(k2_yellow_1(X0)),u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_306])).

cnf(c_18,plain,
    ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_12,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_314,plain,
    ( k2_yellow_1(X0) != X1
    | u1_struct_0(X1) = k2_struct_0(X1) ),
    inference(resolution_lifted,[status(thm)],[c_12,c_295])).

cnf(c_315,plain,
    ( u1_struct_0(k2_yellow_1(X0)) = k2_struct_0(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_314])).

cnf(c_1144,plain,
    ( k2_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_315,c_18])).

cnf(c_1151,plain,
    ( v1_subset_1(X0,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1119,c_18,c_1144])).

cnf(c_1216,plain,
    ( ~ v1_subset_1(X0,X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1151])).

cnf(c_1218,plain,
    ( ~ v1_subset_1(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_1216])).

cnf(c_698,plain,
    ( ~ v1_subset_1(X0,X1)
    | v1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1278,plain,
    ( v1_subset_1(X0,X1)
    | ~ v1_subset_1(k6_domain_1(sK1,sK2),sK1)
    | X0 != k6_domain_1(sK1,sK2)
    | X1 != sK1 ),
    inference(instantiation,[status(thm)],[c_698])).

cnf(c_1280,plain,
    ( ~ v1_subset_1(k6_domain_1(sK1,sK2),sK1)
    | v1_subset_1(sK1,sK1)
    | sK1 != k6_domain_1(sK1,sK2)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1278])).

cnf(c_689,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1354,plain,
    ( X0 != X1
    | X0 = k6_domain_1(sK1,sK2)
    | k6_domain_1(sK1,sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_689])).

cnf(c_1646,plain,
    ( X0 = k6_domain_1(sK1,sK2)
    | X0 != k2_tarski(sK2,sK2)
    | k6_domain_1(sK1,sK2) != k2_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1354])).

cnf(c_1647,plain,
    ( k6_domain_1(sK1,sK2) != k2_tarski(sK2,sK2)
    | sK1 = k6_domain_1(sK1,sK2)
    | sK1 != k2_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1646])).

cnf(c_1784,plain,
    ( ~ r1_tarski(k2_tarski(sK2,sK2),sK1)
    | v1_xboole_0(k2_tarski(sK2,sK2))
    | sK1 = k2_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_337])).

cnf(c_1785,plain,
    ( sK1 = k2_tarski(sK2,sK2)
    | r1_tarski(k2_tarski(sK2,sK2),sK1) != iProver_top
    | v1_xboole_0(k2_tarski(sK2,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1784])).

cnf(c_1821,plain,
    ( ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(sK1))
    | r1_tarski(k2_tarski(sK2,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1822,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(sK1)) != iProver_top
    | r1_tarski(k2_tarski(sK2,sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1821])).

cnf(c_2522,plain,
    ( v1_xboole_0(k2_tarski(sK2,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2510,c_23,c_24,c_22,c_25,c_21,c_20,c_29,c_63,c_1218,c_1265,c_1280,c_1647,c_1785,c_1822,c_2174])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1129,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1132,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_164,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_165,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_164])).

cnf(c_202,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_11,c_165])).

cnf(c_1120,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_202])).

cnf(c_2046,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1132,c_1120])).

cnf(c_2857,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1129,c_2046])).

cnf(c_7,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1128,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1130,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1898,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1128,c_1130])).

cnf(c_2942,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2857,c_1898])).

cnf(c_3228,plain,
    ( k2_tarski(sK2,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2522,c_2942])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_8,plain,
    ( k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(X1,k2_tarski(X0,X0))) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1622,plain,
    ( k2_tarski(X0,X0) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_8])).

cnf(c_3243,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3228,c_1622])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:46:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.22/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.03  
% 2.22/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.22/1.03  
% 2.22/1.03  ------  iProver source info
% 2.22/1.03  
% 2.22/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.22/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.22/1.03  git: non_committed_changes: false
% 2.22/1.03  git: last_make_outside_of_git: false
% 2.22/1.03  
% 2.22/1.03  ------ 
% 2.22/1.03  
% 2.22/1.03  ------ Input Options
% 2.22/1.03  
% 2.22/1.03  --out_options                           all
% 2.22/1.03  --tptp_safe_out                         true
% 2.22/1.03  --problem_path                          ""
% 2.22/1.03  --include_path                          ""
% 2.22/1.03  --clausifier                            res/vclausify_rel
% 2.22/1.03  --clausifier_options                    --mode clausify
% 2.22/1.03  --stdin                                 false
% 2.22/1.03  --stats_out                             all
% 2.22/1.03  
% 2.22/1.03  ------ General Options
% 2.22/1.03  
% 2.22/1.03  --fof                                   false
% 2.22/1.03  --time_out_real                         305.
% 2.22/1.03  --time_out_virtual                      -1.
% 2.22/1.03  --symbol_type_check                     false
% 2.22/1.03  --clausify_out                          false
% 2.22/1.03  --sig_cnt_out                           false
% 2.22/1.03  --trig_cnt_out                          false
% 2.22/1.03  --trig_cnt_out_tolerance                1.
% 2.22/1.03  --trig_cnt_out_sk_spl                   false
% 2.22/1.03  --abstr_cl_out                          false
% 2.22/1.03  
% 2.22/1.03  ------ Global Options
% 2.22/1.03  
% 2.22/1.03  --schedule                              default
% 2.22/1.03  --add_important_lit                     false
% 2.22/1.03  --prop_solver_per_cl                    1000
% 2.22/1.03  --min_unsat_core                        false
% 2.22/1.03  --soft_assumptions                      false
% 2.22/1.03  --soft_lemma_size                       3
% 2.22/1.03  --prop_impl_unit_size                   0
% 2.22/1.03  --prop_impl_unit                        []
% 2.22/1.03  --share_sel_clauses                     true
% 2.22/1.03  --reset_solvers                         false
% 2.22/1.03  --bc_imp_inh                            [conj_cone]
% 2.22/1.03  --conj_cone_tolerance                   3.
% 2.22/1.03  --extra_neg_conj                        none
% 2.22/1.03  --large_theory_mode                     true
% 2.22/1.03  --prolific_symb_bound                   200
% 2.22/1.03  --lt_threshold                          2000
% 2.22/1.03  --clause_weak_htbl                      true
% 2.22/1.03  --gc_record_bc_elim                     false
% 2.22/1.03  
% 2.22/1.03  ------ Preprocessing Options
% 2.22/1.03  
% 2.22/1.03  --preprocessing_flag                    true
% 2.22/1.03  --time_out_prep_mult                    0.1
% 2.22/1.03  --splitting_mode                        input
% 2.22/1.03  --splitting_grd                         true
% 2.22/1.03  --splitting_cvd                         false
% 2.22/1.03  --splitting_cvd_svl                     false
% 2.22/1.03  --splitting_nvd                         32
% 2.22/1.03  --sub_typing                            true
% 2.22/1.03  --prep_gs_sim                           true
% 2.22/1.03  --prep_unflatten                        true
% 2.22/1.03  --prep_res_sim                          true
% 2.22/1.03  --prep_upred                            true
% 2.22/1.03  --prep_sem_filter                       exhaustive
% 2.22/1.03  --prep_sem_filter_out                   false
% 2.22/1.03  --pred_elim                             true
% 2.22/1.03  --res_sim_input                         true
% 2.22/1.03  --eq_ax_congr_red                       true
% 2.22/1.03  --pure_diseq_elim                       true
% 2.22/1.03  --brand_transform                       false
% 2.22/1.03  --non_eq_to_eq                          false
% 2.22/1.03  --prep_def_merge                        true
% 2.22/1.03  --prep_def_merge_prop_impl              false
% 2.22/1.03  --prep_def_merge_mbd                    true
% 2.22/1.03  --prep_def_merge_tr_red                 false
% 2.22/1.03  --prep_def_merge_tr_cl                  false
% 2.22/1.03  --smt_preprocessing                     true
% 2.22/1.03  --smt_ac_axioms                         fast
% 2.22/1.03  --preprocessed_out                      false
% 2.22/1.03  --preprocessed_stats                    false
% 2.22/1.03  
% 2.22/1.03  ------ Abstraction refinement Options
% 2.22/1.03  
% 2.22/1.03  --abstr_ref                             []
% 2.22/1.03  --abstr_ref_prep                        false
% 2.22/1.03  --abstr_ref_until_sat                   false
% 2.22/1.03  --abstr_ref_sig_restrict                funpre
% 2.22/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.22/1.03  --abstr_ref_under                       []
% 2.22/1.03  
% 2.22/1.03  ------ SAT Options
% 2.22/1.03  
% 2.22/1.03  --sat_mode                              false
% 2.22/1.03  --sat_fm_restart_options                ""
% 2.22/1.03  --sat_gr_def                            false
% 2.22/1.03  --sat_epr_types                         true
% 2.22/1.03  --sat_non_cyclic_types                  false
% 2.22/1.03  --sat_finite_models                     false
% 2.22/1.03  --sat_fm_lemmas                         false
% 2.22/1.03  --sat_fm_prep                           false
% 2.22/1.03  --sat_fm_uc_incr                        true
% 2.22/1.03  --sat_out_model                         small
% 2.22/1.03  --sat_out_clauses                       false
% 2.22/1.03  
% 2.22/1.03  ------ QBF Options
% 2.22/1.03  
% 2.22/1.03  --qbf_mode                              false
% 2.22/1.03  --qbf_elim_univ                         false
% 2.22/1.03  --qbf_dom_inst                          none
% 2.22/1.03  --qbf_dom_pre_inst                      false
% 2.22/1.03  --qbf_sk_in                             false
% 2.22/1.03  --qbf_pred_elim                         true
% 2.22/1.03  --qbf_split                             512
% 2.22/1.03  
% 2.22/1.03  ------ BMC1 Options
% 2.22/1.03  
% 2.22/1.03  --bmc1_incremental                      false
% 2.22/1.03  --bmc1_axioms                           reachable_all
% 2.22/1.03  --bmc1_min_bound                        0
% 2.22/1.03  --bmc1_max_bound                        -1
% 2.22/1.03  --bmc1_max_bound_default                -1
% 2.22/1.03  --bmc1_symbol_reachability              true
% 2.22/1.03  --bmc1_property_lemmas                  false
% 2.22/1.03  --bmc1_k_induction                      false
% 2.22/1.03  --bmc1_non_equiv_states                 false
% 2.22/1.03  --bmc1_deadlock                         false
% 2.22/1.03  --bmc1_ucm                              false
% 2.22/1.03  --bmc1_add_unsat_core                   none
% 2.22/1.03  --bmc1_unsat_core_children              false
% 2.22/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.22/1.03  --bmc1_out_stat                         full
% 2.22/1.03  --bmc1_ground_init                      false
% 2.22/1.03  --bmc1_pre_inst_next_state              false
% 2.22/1.03  --bmc1_pre_inst_state                   false
% 2.22/1.03  --bmc1_pre_inst_reach_state             false
% 2.22/1.03  --bmc1_out_unsat_core                   false
% 2.22/1.03  --bmc1_aig_witness_out                  false
% 2.22/1.03  --bmc1_verbose                          false
% 2.22/1.03  --bmc1_dump_clauses_tptp                false
% 2.22/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.22/1.03  --bmc1_dump_file                        -
% 2.22/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.22/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.22/1.03  --bmc1_ucm_extend_mode                  1
% 2.22/1.03  --bmc1_ucm_init_mode                    2
% 2.22/1.03  --bmc1_ucm_cone_mode                    none
% 2.22/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.22/1.03  --bmc1_ucm_relax_model                  4
% 2.22/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.22/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.22/1.03  --bmc1_ucm_layered_model                none
% 2.22/1.03  --bmc1_ucm_max_lemma_size               10
% 2.22/1.03  
% 2.22/1.03  ------ AIG Options
% 2.22/1.03  
% 2.22/1.03  --aig_mode                              false
% 2.22/1.03  
% 2.22/1.03  ------ Instantiation Options
% 2.22/1.03  
% 2.22/1.03  --instantiation_flag                    true
% 2.22/1.03  --inst_sos_flag                         false
% 2.22/1.03  --inst_sos_phase                        true
% 2.22/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.22/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.22/1.03  --inst_lit_sel_side                     num_symb
% 2.22/1.03  --inst_solver_per_active                1400
% 2.22/1.03  --inst_solver_calls_frac                1.
% 2.22/1.03  --inst_passive_queue_type               priority_queues
% 2.22/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.22/1.03  --inst_passive_queues_freq              [25;2]
% 2.22/1.03  --inst_dismatching                      true
% 2.22/1.03  --inst_eager_unprocessed_to_passive     true
% 2.22/1.03  --inst_prop_sim_given                   true
% 2.22/1.03  --inst_prop_sim_new                     false
% 2.22/1.03  --inst_subs_new                         false
% 2.22/1.03  --inst_eq_res_simp                      false
% 2.22/1.03  --inst_subs_given                       false
% 2.22/1.03  --inst_orphan_elimination               true
% 2.22/1.03  --inst_learning_loop_flag               true
% 2.22/1.03  --inst_learning_start                   3000
% 2.22/1.03  --inst_learning_factor                  2
% 2.22/1.03  --inst_start_prop_sim_after_learn       3
% 2.22/1.03  --inst_sel_renew                        solver
% 2.22/1.03  --inst_lit_activity_flag                true
% 2.22/1.03  --inst_restr_to_given                   false
% 2.22/1.03  --inst_activity_threshold               500
% 2.22/1.03  --inst_out_proof                        true
% 2.22/1.03  
% 2.22/1.03  ------ Resolution Options
% 2.22/1.03  
% 2.22/1.03  --resolution_flag                       true
% 2.22/1.03  --res_lit_sel                           adaptive
% 2.22/1.03  --res_lit_sel_side                      none
% 2.22/1.03  --res_ordering                          kbo
% 2.22/1.03  --res_to_prop_solver                    active
% 2.22/1.03  --res_prop_simpl_new                    false
% 2.22/1.03  --res_prop_simpl_given                  true
% 2.22/1.03  --res_passive_queue_type                priority_queues
% 2.22/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.22/1.03  --res_passive_queues_freq               [15;5]
% 2.22/1.03  --res_forward_subs                      full
% 2.22/1.03  --res_backward_subs                     full
% 2.22/1.03  --res_forward_subs_resolution           true
% 2.22/1.03  --res_backward_subs_resolution          true
% 2.22/1.03  --res_orphan_elimination                true
% 2.22/1.03  --res_time_limit                        2.
% 2.22/1.03  --res_out_proof                         true
% 2.22/1.03  
% 2.22/1.03  ------ Superposition Options
% 2.22/1.03  
% 2.22/1.03  --superposition_flag                    true
% 2.22/1.03  --sup_passive_queue_type                priority_queues
% 2.22/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.22/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.22/1.03  --demod_completeness_check              fast
% 2.22/1.03  --demod_use_ground                      true
% 2.22/1.03  --sup_to_prop_solver                    passive
% 2.22/1.03  --sup_prop_simpl_new                    true
% 2.22/1.03  --sup_prop_simpl_given                  true
% 2.22/1.03  --sup_fun_splitting                     false
% 2.22/1.03  --sup_smt_interval                      50000
% 2.22/1.03  
% 2.22/1.03  ------ Superposition Simplification Setup
% 2.22/1.03  
% 2.22/1.03  --sup_indices_passive                   []
% 2.22/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.22/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/1.03  --sup_full_bw                           [BwDemod]
% 2.22/1.03  --sup_immed_triv                        [TrivRules]
% 2.22/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.22/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/1.03  --sup_immed_bw_main                     []
% 2.22/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.22/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/1.03  
% 2.22/1.03  ------ Combination Options
% 2.22/1.03  
% 2.22/1.03  --comb_res_mult                         3
% 2.22/1.03  --comb_sup_mult                         2
% 2.22/1.03  --comb_inst_mult                        10
% 2.22/1.03  
% 2.22/1.03  ------ Debug Options
% 2.22/1.03  
% 2.22/1.03  --dbg_backtrace                         false
% 2.22/1.03  --dbg_dump_prop_clauses                 false
% 2.22/1.03  --dbg_dump_prop_clauses_file            -
% 2.22/1.03  --dbg_out_stat                          false
% 2.22/1.03  ------ Parsing...
% 2.22/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.22/1.03  
% 2.22/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.22/1.03  
% 2.22/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.22/1.03  
% 2.22/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.22/1.03  ------ Proving...
% 2.22/1.03  ------ Problem Properties 
% 2.22/1.03  
% 2.22/1.03  
% 2.22/1.03  clauses                                 20
% 2.22/1.03  conjectures                             3
% 2.22/1.03  EPR                                     8
% 2.22/1.03  Horn                                    16
% 2.22/1.03  unary                                   10
% 2.22/1.03  binary                                  4
% 2.22/1.03  lits                                    36
% 2.22/1.03  lits eq                                 7
% 2.22/1.03  fd_pure                                 0
% 2.22/1.03  fd_pseudo                               0
% 2.22/1.03  fd_cond                                 1
% 2.22/1.03  fd_pseudo_cond                          1
% 2.22/1.03  AC symbols                              0
% 2.22/1.03  
% 2.22/1.03  ------ Schedule dynamic 5 is on 
% 2.22/1.03  
% 2.22/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.22/1.03  
% 2.22/1.03  
% 2.22/1.03  ------ 
% 2.22/1.03  Current options:
% 2.22/1.03  ------ 
% 2.22/1.03  
% 2.22/1.03  ------ Input Options
% 2.22/1.03  
% 2.22/1.03  --out_options                           all
% 2.22/1.03  --tptp_safe_out                         true
% 2.22/1.03  --problem_path                          ""
% 2.22/1.03  --include_path                          ""
% 2.22/1.03  --clausifier                            res/vclausify_rel
% 2.22/1.03  --clausifier_options                    --mode clausify
% 2.22/1.03  --stdin                                 false
% 2.22/1.03  --stats_out                             all
% 2.22/1.03  
% 2.22/1.03  ------ General Options
% 2.22/1.03  
% 2.22/1.03  --fof                                   false
% 2.22/1.03  --time_out_real                         305.
% 2.22/1.03  --time_out_virtual                      -1.
% 2.22/1.03  --symbol_type_check                     false
% 2.22/1.03  --clausify_out                          false
% 2.22/1.03  --sig_cnt_out                           false
% 2.22/1.03  --trig_cnt_out                          false
% 2.22/1.03  --trig_cnt_out_tolerance                1.
% 2.22/1.03  --trig_cnt_out_sk_spl                   false
% 2.22/1.03  --abstr_cl_out                          false
% 2.22/1.03  
% 2.22/1.03  ------ Global Options
% 2.22/1.03  
% 2.22/1.03  --schedule                              default
% 2.22/1.03  --add_important_lit                     false
% 2.22/1.03  --prop_solver_per_cl                    1000
% 2.22/1.03  --min_unsat_core                        false
% 2.22/1.03  --soft_assumptions                      false
% 2.22/1.03  --soft_lemma_size                       3
% 2.22/1.03  --prop_impl_unit_size                   0
% 2.22/1.03  --prop_impl_unit                        []
% 2.22/1.03  --share_sel_clauses                     true
% 2.22/1.03  --reset_solvers                         false
% 2.22/1.03  --bc_imp_inh                            [conj_cone]
% 2.22/1.03  --conj_cone_tolerance                   3.
% 2.22/1.03  --extra_neg_conj                        none
% 2.22/1.03  --large_theory_mode                     true
% 2.22/1.03  --prolific_symb_bound                   200
% 2.22/1.03  --lt_threshold                          2000
% 2.22/1.03  --clause_weak_htbl                      true
% 2.22/1.03  --gc_record_bc_elim                     false
% 2.22/1.03  
% 2.22/1.03  ------ Preprocessing Options
% 2.22/1.03  
% 2.22/1.03  --preprocessing_flag                    true
% 2.22/1.03  --time_out_prep_mult                    0.1
% 2.22/1.03  --splitting_mode                        input
% 2.22/1.03  --splitting_grd                         true
% 2.22/1.03  --splitting_cvd                         false
% 2.22/1.03  --splitting_cvd_svl                     false
% 2.22/1.03  --splitting_nvd                         32
% 2.22/1.03  --sub_typing                            true
% 2.22/1.03  --prep_gs_sim                           true
% 2.22/1.03  --prep_unflatten                        true
% 2.22/1.03  --prep_res_sim                          true
% 2.22/1.03  --prep_upred                            true
% 2.22/1.03  --prep_sem_filter                       exhaustive
% 2.22/1.03  --prep_sem_filter_out                   false
% 2.22/1.03  --pred_elim                             true
% 2.22/1.03  --res_sim_input                         true
% 2.22/1.03  --eq_ax_congr_red                       true
% 2.22/1.03  --pure_diseq_elim                       true
% 2.22/1.03  --brand_transform                       false
% 2.22/1.03  --non_eq_to_eq                          false
% 2.22/1.03  --prep_def_merge                        true
% 2.22/1.03  --prep_def_merge_prop_impl              false
% 2.22/1.03  --prep_def_merge_mbd                    true
% 2.22/1.03  --prep_def_merge_tr_red                 false
% 2.22/1.03  --prep_def_merge_tr_cl                  false
% 2.22/1.03  --smt_preprocessing                     true
% 2.22/1.03  --smt_ac_axioms                         fast
% 2.22/1.03  --preprocessed_out                      false
% 2.22/1.03  --preprocessed_stats                    false
% 2.22/1.03  
% 2.22/1.03  ------ Abstraction refinement Options
% 2.22/1.03  
% 2.22/1.03  --abstr_ref                             []
% 2.22/1.03  --abstr_ref_prep                        false
% 2.22/1.03  --abstr_ref_until_sat                   false
% 2.22/1.03  --abstr_ref_sig_restrict                funpre
% 2.22/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.22/1.03  --abstr_ref_under                       []
% 2.22/1.03  
% 2.22/1.03  ------ SAT Options
% 2.22/1.03  
% 2.22/1.03  --sat_mode                              false
% 2.22/1.03  --sat_fm_restart_options                ""
% 2.22/1.03  --sat_gr_def                            false
% 2.22/1.03  --sat_epr_types                         true
% 2.22/1.03  --sat_non_cyclic_types                  false
% 2.22/1.03  --sat_finite_models                     false
% 2.22/1.03  --sat_fm_lemmas                         false
% 2.22/1.03  --sat_fm_prep                           false
% 2.22/1.03  --sat_fm_uc_incr                        true
% 2.22/1.03  --sat_out_model                         small
% 2.22/1.03  --sat_out_clauses                       false
% 2.22/1.03  
% 2.22/1.03  ------ QBF Options
% 2.22/1.03  
% 2.22/1.03  --qbf_mode                              false
% 2.22/1.03  --qbf_elim_univ                         false
% 2.22/1.03  --qbf_dom_inst                          none
% 2.22/1.03  --qbf_dom_pre_inst                      false
% 2.22/1.03  --qbf_sk_in                             false
% 2.22/1.03  --qbf_pred_elim                         true
% 2.22/1.03  --qbf_split                             512
% 2.22/1.03  
% 2.22/1.03  ------ BMC1 Options
% 2.22/1.03  
% 2.22/1.03  --bmc1_incremental                      false
% 2.22/1.03  --bmc1_axioms                           reachable_all
% 2.22/1.03  --bmc1_min_bound                        0
% 2.22/1.03  --bmc1_max_bound                        -1
% 2.22/1.03  --bmc1_max_bound_default                -1
% 2.22/1.03  --bmc1_symbol_reachability              true
% 2.22/1.03  --bmc1_property_lemmas                  false
% 2.22/1.03  --bmc1_k_induction                      false
% 2.22/1.03  --bmc1_non_equiv_states                 false
% 2.22/1.03  --bmc1_deadlock                         false
% 2.22/1.03  --bmc1_ucm                              false
% 2.22/1.03  --bmc1_add_unsat_core                   none
% 2.22/1.03  --bmc1_unsat_core_children              false
% 2.22/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.22/1.03  --bmc1_out_stat                         full
% 2.22/1.03  --bmc1_ground_init                      false
% 2.22/1.03  --bmc1_pre_inst_next_state              false
% 2.22/1.03  --bmc1_pre_inst_state                   false
% 2.22/1.03  --bmc1_pre_inst_reach_state             false
% 2.22/1.03  --bmc1_out_unsat_core                   false
% 2.22/1.03  --bmc1_aig_witness_out                  false
% 2.22/1.03  --bmc1_verbose                          false
% 2.22/1.03  --bmc1_dump_clauses_tptp                false
% 2.22/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.22/1.03  --bmc1_dump_file                        -
% 2.22/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.22/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.22/1.03  --bmc1_ucm_extend_mode                  1
% 2.22/1.03  --bmc1_ucm_init_mode                    2
% 2.22/1.03  --bmc1_ucm_cone_mode                    none
% 2.22/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.22/1.03  --bmc1_ucm_relax_model                  4
% 2.22/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.22/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.22/1.03  --bmc1_ucm_layered_model                none
% 2.22/1.03  --bmc1_ucm_max_lemma_size               10
% 2.22/1.03  
% 2.22/1.03  ------ AIG Options
% 2.22/1.03  
% 2.22/1.03  --aig_mode                              false
% 2.22/1.03  
% 2.22/1.03  ------ Instantiation Options
% 2.22/1.03  
% 2.22/1.03  --instantiation_flag                    true
% 2.22/1.03  --inst_sos_flag                         false
% 2.22/1.03  --inst_sos_phase                        true
% 2.22/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.22/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.22/1.03  --inst_lit_sel_side                     none
% 2.22/1.03  --inst_solver_per_active                1400
% 2.22/1.03  --inst_solver_calls_frac                1.
% 2.22/1.03  --inst_passive_queue_type               priority_queues
% 2.22/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.22/1.03  --inst_passive_queues_freq              [25;2]
% 2.22/1.03  --inst_dismatching                      true
% 2.22/1.03  --inst_eager_unprocessed_to_passive     true
% 2.22/1.03  --inst_prop_sim_given                   true
% 2.22/1.03  --inst_prop_sim_new                     false
% 2.22/1.03  --inst_subs_new                         false
% 2.22/1.03  --inst_eq_res_simp                      false
% 2.22/1.03  --inst_subs_given                       false
% 2.22/1.03  --inst_orphan_elimination               true
% 2.22/1.03  --inst_learning_loop_flag               true
% 2.22/1.03  --inst_learning_start                   3000
% 2.22/1.03  --inst_learning_factor                  2
% 2.22/1.03  --inst_start_prop_sim_after_learn       3
% 2.22/1.03  --inst_sel_renew                        solver
% 2.22/1.03  --inst_lit_activity_flag                true
% 2.22/1.03  --inst_restr_to_given                   false
% 2.22/1.03  --inst_activity_threshold               500
% 2.22/1.03  --inst_out_proof                        true
% 2.22/1.03  
% 2.22/1.03  ------ Resolution Options
% 2.22/1.03  
% 2.22/1.03  --resolution_flag                       false
% 2.22/1.03  --res_lit_sel                           adaptive
% 2.22/1.03  --res_lit_sel_side                      none
% 2.22/1.03  --res_ordering                          kbo
% 2.22/1.03  --res_to_prop_solver                    active
% 2.22/1.03  --res_prop_simpl_new                    false
% 2.22/1.03  --res_prop_simpl_given                  true
% 2.22/1.03  --res_passive_queue_type                priority_queues
% 2.22/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.22/1.03  --res_passive_queues_freq               [15;5]
% 2.22/1.03  --res_forward_subs                      full
% 2.22/1.03  --res_backward_subs                     full
% 2.22/1.03  --res_forward_subs_resolution           true
% 2.22/1.03  --res_backward_subs_resolution          true
% 2.22/1.03  --res_orphan_elimination                true
% 2.22/1.03  --res_time_limit                        2.
% 2.22/1.03  --res_out_proof                         true
% 2.22/1.03  
% 2.22/1.03  ------ Superposition Options
% 2.22/1.03  
% 2.22/1.03  --superposition_flag                    true
% 2.22/1.03  --sup_passive_queue_type                priority_queues
% 2.22/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.22/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.22/1.03  --demod_completeness_check              fast
% 2.22/1.03  --demod_use_ground                      true
% 2.22/1.03  --sup_to_prop_solver                    passive
% 2.22/1.03  --sup_prop_simpl_new                    true
% 2.22/1.03  --sup_prop_simpl_given                  true
% 2.22/1.03  --sup_fun_splitting                     false
% 2.22/1.03  --sup_smt_interval                      50000
% 2.22/1.03  
% 2.22/1.03  ------ Superposition Simplification Setup
% 2.22/1.03  
% 2.22/1.03  --sup_indices_passive                   []
% 2.22/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.22/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/1.03  --sup_full_bw                           [BwDemod]
% 2.22/1.03  --sup_immed_triv                        [TrivRules]
% 2.22/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.22/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/1.03  --sup_immed_bw_main                     []
% 2.22/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.22/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/1.03  
% 2.22/1.03  ------ Combination Options
% 2.22/1.03  
% 2.22/1.03  --comb_res_mult                         3
% 2.22/1.03  --comb_sup_mult                         2
% 2.22/1.03  --comb_inst_mult                        10
% 2.22/1.03  
% 2.22/1.03  ------ Debug Options
% 2.22/1.03  
% 2.22/1.03  --dbg_backtrace                         false
% 2.22/1.03  --dbg_dump_prop_clauses                 false
% 2.22/1.03  --dbg_dump_prop_clauses_file            -
% 2.22/1.03  --dbg_out_stat                          false
% 2.22/1.03  
% 2.22/1.03  
% 2.22/1.03  
% 2.22/1.03  
% 2.22/1.03  ------ Proving...
% 2.22/1.03  
% 2.22/1.03  
% 2.22/1.03  % SZS status Theorem for theBenchmark.p
% 2.22/1.03  
% 2.22/1.03   Resolution empty clause
% 2.22/1.03  
% 2.22/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.22/1.03  
% 2.22/1.03  fof(f18,conjecture,(
% 2.22/1.03    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 2.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.03  
% 2.22/1.03  fof(f19,negated_conjecture,(
% 2.22/1.03    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 2.22/1.03    inference(negated_conjecture,[],[f18])).
% 2.22/1.03  
% 2.22/1.03  fof(f32,plain,(
% 2.22/1.03    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 2.22/1.03    inference(ennf_transformation,[],[f19])).
% 2.22/1.03  
% 2.22/1.03  fof(f33,plain,(
% 2.22/1.03    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 2.22/1.03    inference(flattening,[],[f32])).
% 2.22/1.03  
% 2.22/1.03  fof(f42,plain,(
% 2.22/1.03    ( ! [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) => (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,sK2),X0) & m1_subset_1(sK2,X0))) )),
% 2.22/1.03    introduced(choice_axiom,[])).
% 2.22/1.03  
% 2.22/1.03  fof(f41,plain,(
% 2.22/1.03    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK1) & v1_subset_1(k6_domain_1(sK1,X1),sK1) & m1_subset_1(X1,sK1)) & ~v1_xboole_0(sK1))),
% 2.22/1.03    introduced(choice_axiom,[])).
% 2.22/1.03  
% 2.22/1.03  fof(f43,plain,(
% 2.22/1.03    (v1_zfmisc_1(sK1) & v1_subset_1(k6_domain_1(sK1,sK2),sK1) & m1_subset_1(sK2,sK1)) & ~v1_xboole_0(sK1)),
% 2.22/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f33,f42,f41])).
% 2.22/1.03  
% 2.22/1.03  fof(f68,plain,(
% 2.22/1.03    m1_subset_1(sK2,sK1)),
% 2.22/1.03    inference(cnf_transformation,[],[f43])).
% 2.22/1.03  
% 2.22/1.03  fof(f14,axiom,(
% 2.22/1.03    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.03  
% 2.22/1.03  fof(f28,plain,(
% 2.22/1.03    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.22/1.03    inference(ennf_transformation,[],[f14])).
% 2.22/1.03  
% 2.22/1.03  fof(f29,plain,(
% 2.22/1.03    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.22/1.03    inference(flattening,[],[f28])).
% 2.22/1.03  
% 2.22/1.03  fof(f62,plain,(
% 2.22/1.03    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.22/1.03    inference(cnf_transformation,[],[f29])).
% 2.22/1.03  
% 2.22/1.03  fof(f6,axiom,(
% 2.22/1.03    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.03  
% 2.22/1.03  fof(f53,plain,(
% 2.22/1.03    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.22/1.03    inference(cnf_transformation,[],[f6])).
% 2.22/1.03  
% 2.22/1.03  fof(f73,plain,(
% 2.22/1.03    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.22/1.03    inference(definition_unfolding,[],[f62,f53])).
% 2.22/1.03  
% 2.22/1.03  fof(f67,plain,(
% 2.22/1.03    ~v1_xboole_0(sK1)),
% 2.22/1.03    inference(cnf_transformation,[],[f43])).
% 2.22/1.03  
% 2.22/1.03  fof(f12,axiom,(
% 2.22/1.03    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.03  
% 2.22/1.03  fof(f25,plain,(
% 2.22/1.03    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.22/1.03    inference(ennf_transformation,[],[f12])).
% 2.22/1.03  
% 2.22/1.03  fof(f26,plain,(
% 2.22/1.03    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.22/1.03    inference(flattening,[],[f25])).
% 2.22/1.03  
% 2.22/1.03  fof(f60,plain,(
% 2.22/1.03    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.22/1.03    inference(cnf_transformation,[],[f26])).
% 2.22/1.03  
% 2.22/1.03  fof(f8,axiom,(
% 2.22/1.03    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.03  
% 2.22/1.03  fof(f40,plain,(
% 2.22/1.03    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.22/1.03    inference(nnf_transformation,[],[f8])).
% 2.22/1.03  
% 2.22/1.03  fof(f55,plain,(
% 2.22/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.22/1.03    inference(cnf_transformation,[],[f40])).
% 2.22/1.03  
% 2.22/1.03  fof(f17,axiom,(
% 2.22/1.03    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 2.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.03  
% 2.22/1.03  fof(f30,plain,(
% 2.22/1.03    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 2.22/1.03    inference(ennf_transformation,[],[f17])).
% 2.22/1.03  
% 2.22/1.03  fof(f31,plain,(
% 2.22/1.03    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.22/1.03    inference(flattening,[],[f30])).
% 2.22/1.03  
% 2.22/1.03  fof(f66,plain,(
% 2.22/1.03    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.22/1.03    inference(cnf_transformation,[],[f31])).
% 2.22/1.03  
% 2.22/1.03  fof(f70,plain,(
% 2.22/1.03    v1_zfmisc_1(sK1)),
% 2.22/1.03    inference(cnf_transformation,[],[f43])).
% 2.22/1.03  
% 2.22/1.03  fof(f69,plain,(
% 2.22/1.03    v1_subset_1(k6_domain_1(sK1,sK2),sK1)),
% 2.22/1.03    inference(cnf_transformation,[],[f43])).
% 2.22/1.03  
% 2.22/1.03  fof(f2,axiom,(
% 2.22/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.03  
% 2.22/1.03  fof(f38,plain,(
% 2.22/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.22/1.03    inference(nnf_transformation,[],[f2])).
% 2.22/1.03  
% 2.22/1.03  fof(f39,plain,(
% 2.22/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.22/1.03    inference(flattening,[],[f38])).
% 2.22/1.03  
% 2.22/1.03  fof(f47,plain,(
% 2.22/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.22/1.03    inference(cnf_transformation,[],[f39])).
% 2.22/1.03  
% 2.22/1.03  fof(f75,plain,(
% 2.22/1.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.22/1.03    inference(equality_resolution,[],[f47])).
% 2.22/1.03  
% 2.22/1.03  fof(f11,axiom,(
% 2.22/1.03    ! [X0] : (l1_struct_0(X0) => ~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)))),
% 2.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.03  
% 2.22/1.03  fof(f24,plain,(
% 2.22/1.03    ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0))),
% 2.22/1.03    inference(ennf_transformation,[],[f11])).
% 2.22/1.03  
% 2.22/1.03  fof(f59,plain,(
% 2.22/1.03    ( ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 2.22/1.03    inference(cnf_transformation,[],[f24])).
% 2.22/1.03  
% 2.22/1.03  fof(f13,axiom,(
% 2.22/1.03    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 2.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.03  
% 2.22/1.03  fof(f27,plain,(
% 2.22/1.03    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 2.22/1.03    inference(ennf_transformation,[],[f13])).
% 2.22/1.03  
% 2.22/1.03  fof(f61,plain,(
% 2.22/1.03    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 2.22/1.03    inference(cnf_transformation,[],[f27])).
% 2.22/1.03  
% 2.22/1.03  fof(f15,axiom,(
% 2.22/1.03    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 2.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.03  
% 2.22/1.03  fof(f20,plain,(
% 2.22/1.03    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 2.22/1.03    inference(pure_predicate_removal,[],[f15])).
% 2.22/1.03  
% 2.22/1.03  fof(f63,plain,(
% 2.22/1.03    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 2.22/1.03    inference(cnf_transformation,[],[f20])).
% 2.22/1.03  
% 2.22/1.03  fof(f16,axiom,(
% 2.22/1.03    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 2.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.03  
% 2.22/1.03  fof(f64,plain,(
% 2.22/1.03    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 2.22/1.03    inference(cnf_transformation,[],[f16])).
% 2.22/1.03  
% 2.22/1.03  fof(f10,axiom,(
% 2.22/1.03    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.03  
% 2.22/1.03  fof(f23,plain,(
% 2.22/1.03    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.22/1.03    inference(ennf_transformation,[],[f10])).
% 2.22/1.03  
% 2.22/1.03  fof(f58,plain,(
% 2.22/1.03    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.22/1.03    inference(cnf_transformation,[],[f23])).
% 2.22/1.03  
% 2.22/1.03  fof(f48,plain,(
% 2.22/1.03    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.22/1.03    inference(cnf_transformation,[],[f39])).
% 2.22/1.03  
% 2.22/1.03  fof(f74,plain,(
% 2.22/1.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.22/1.03    inference(equality_resolution,[],[f48])).
% 2.22/1.03  
% 2.22/1.03  fof(f1,axiom,(
% 2.22/1.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.03  
% 2.22/1.03  fof(f21,plain,(
% 2.22/1.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.22/1.03    inference(ennf_transformation,[],[f1])).
% 2.22/1.03  
% 2.22/1.03  fof(f34,plain,(
% 2.22/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.22/1.03    inference(nnf_transformation,[],[f21])).
% 2.22/1.03  
% 2.22/1.03  fof(f35,plain,(
% 2.22/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.22/1.03    inference(rectify,[],[f34])).
% 2.22/1.03  
% 2.22/1.03  fof(f36,plain,(
% 2.22/1.03    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.22/1.03    introduced(choice_axiom,[])).
% 2.22/1.03  
% 2.22/1.03  fof(f37,plain,(
% 2.22/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.22/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).
% 2.22/1.03  
% 2.22/1.03  fof(f45,plain,(
% 2.22/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.22/1.03    inference(cnf_transformation,[],[f37])).
% 2.22/1.03  
% 2.22/1.03  fof(f9,axiom,(
% 2.22/1.03    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.03  
% 2.22/1.03  fof(f22,plain,(
% 2.22/1.03    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.22/1.03    inference(ennf_transformation,[],[f9])).
% 2.22/1.03  
% 2.22/1.03  fof(f57,plain,(
% 2.22/1.03    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.22/1.03    inference(cnf_transformation,[],[f22])).
% 2.22/1.03  
% 2.22/1.03  fof(f56,plain,(
% 2.22/1.03    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.22/1.03    inference(cnf_transformation,[],[f40])).
% 2.22/1.03  
% 2.22/1.03  fof(f4,axiom,(
% 2.22/1.03    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.03  
% 2.22/1.03  fof(f51,plain,(
% 2.22/1.03    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.22/1.03    inference(cnf_transformation,[],[f4])).
% 2.22/1.03  
% 2.22/1.03  fof(f49,plain,(
% 2.22/1.03    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.22/1.03    inference(cnf_transformation,[],[f39])).
% 2.22/1.03  
% 2.22/1.03  fof(f3,axiom,(
% 2.22/1.03    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.03  
% 2.22/1.03  fof(f50,plain,(
% 2.22/1.03    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.22/1.03    inference(cnf_transformation,[],[f3])).
% 2.22/1.03  
% 2.22/1.03  fof(f5,axiom,(
% 2.22/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.03  
% 2.22/1.03  fof(f52,plain,(
% 2.22/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.22/1.03    inference(cnf_transformation,[],[f5])).
% 2.22/1.03  
% 2.22/1.03  fof(f71,plain,(
% 2.22/1.03    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 2.22/1.03    inference(definition_unfolding,[],[f50,f52])).
% 2.22/1.03  
% 2.22/1.03  fof(f7,axiom,(
% 2.22/1.03    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 2.22/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.22/1.03  
% 2.22/1.03  fof(f54,plain,(
% 2.22/1.03    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 2.22/1.03    inference(cnf_transformation,[],[f7])).
% 2.22/1.03  
% 2.22/1.03  fof(f72,plain,(
% 2.22/1.03    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(X1,k2_tarski(X0,X0)))) )),
% 2.22/1.03    inference(definition_unfolding,[],[f54,f52,f53])).
% 2.22/1.03  
% 2.22/1.03  cnf(c_22,negated_conjecture,
% 2.22/1.03      ( m1_subset_1(sK2,sK1) ),
% 2.22/1.03      inference(cnf_transformation,[],[f68]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1122,plain,
% 2.22/1.03      ( m1_subset_1(sK2,sK1) = iProver_top ),
% 2.22/1.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_16,plain,
% 2.22/1.03      ( ~ m1_subset_1(X0,X1)
% 2.22/1.03      | v1_xboole_0(X1)
% 2.22/1.03      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 2.22/1.03      inference(cnf_transformation,[],[f73]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1124,plain,
% 2.22/1.03      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
% 2.22/1.03      | m1_subset_1(X1,X0) != iProver_top
% 2.22/1.03      | v1_xboole_0(X0) = iProver_top ),
% 2.22/1.03      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1952,plain,
% 2.22/1.03      ( k6_domain_1(sK1,sK2) = k2_tarski(sK2,sK2)
% 2.22/1.03      | v1_xboole_0(sK1) = iProver_top ),
% 2.22/1.03      inference(superposition,[status(thm)],[c_1122,c_1124]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_23,negated_conjecture,
% 2.22/1.03      ( ~ v1_xboole_0(sK1) ),
% 2.22/1.03      inference(cnf_transformation,[],[f67]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1265,plain,
% 2.22/1.03      ( ~ m1_subset_1(sK2,sK1)
% 2.22/1.03      | v1_xboole_0(sK1)
% 2.22/1.03      | k6_domain_1(sK1,sK2) = k2_tarski(sK2,sK2) ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_16]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_2169,plain,
% 2.22/1.03      ( k6_domain_1(sK1,sK2) = k2_tarski(sK2,sK2) ),
% 2.22/1.03      inference(global_propositional_subsumption,
% 2.22/1.03                [status(thm)],
% 2.22/1.03                [c_1952,c_23,c_22,c_1265]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_14,plain,
% 2.22/1.03      ( ~ m1_subset_1(X0,X1)
% 2.22/1.03      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 2.22/1.03      | v1_xboole_0(X1) ),
% 2.22/1.03      inference(cnf_transformation,[],[f60]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1125,plain,
% 2.22/1.03      ( m1_subset_1(X0,X1) != iProver_top
% 2.22/1.03      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
% 2.22/1.03      | v1_xboole_0(X1) = iProver_top ),
% 2.22/1.03      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_2174,plain,
% 2.22/1.03      ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(sK1)) = iProver_top
% 2.22/1.03      | m1_subset_1(sK2,sK1) != iProver_top
% 2.22/1.03      | v1_xboole_0(sK1) = iProver_top ),
% 2.22/1.03      inference(superposition,[status(thm)],[c_2169,c_1125]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_24,plain,
% 2.22/1.03      ( v1_xboole_0(sK1) != iProver_top ),
% 2.22/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_25,plain,
% 2.22/1.03      ( m1_subset_1(sK2,sK1) = iProver_top ),
% 2.22/1.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_2357,plain,
% 2.22/1.03      ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(sK1)) = iProver_top ),
% 2.22/1.03      inference(global_propositional_subsumption,
% 2.22/1.03                [status(thm)],
% 2.22/1.03                [c_2174,c_24,c_25]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_10,plain,
% 2.22/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.22/1.03      inference(cnf_transformation,[],[f55]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1126,plain,
% 2.22/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.22/1.03      | r1_tarski(X0,X1) = iProver_top ),
% 2.22/1.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_2362,plain,
% 2.22/1.03      ( r1_tarski(k2_tarski(sK2,sK2),sK1) = iProver_top ),
% 2.22/1.03      inference(superposition,[status(thm)],[c_2357,c_1126]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_19,plain,
% 2.22/1.03      ( ~ r1_tarski(X0,X1)
% 2.22/1.03      | ~ v1_zfmisc_1(X1)
% 2.22/1.03      | v1_xboole_0(X1)
% 2.22/1.03      | v1_xboole_0(X0)
% 2.22/1.03      | X1 = X0 ),
% 2.22/1.03      inference(cnf_transformation,[],[f66]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_20,negated_conjecture,
% 2.22/1.03      ( v1_zfmisc_1(sK1) ),
% 2.22/1.03      inference(cnf_transformation,[],[f70]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_333,plain,
% 2.22/1.03      ( ~ r1_tarski(X0,X1)
% 2.22/1.03      | v1_xboole_0(X1)
% 2.22/1.03      | v1_xboole_0(X0)
% 2.22/1.03      | X1 = X0
% 2.22/1.03      | sK1 != X1 ),
% 2.22/1.03      inference(resolution_lifted,[status(thm)],[c_19,c_20]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_334,plain,
% 2.22/1.03      ( ~ r1_tarski(X0,sK1) | v1_xboole_0(X0) | v1_xboole_0(sK1) | sK1 = X0 ),
% 2.22/1.03      inference(unflattening,[status(thm)],[c_333]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_336,plain,
% 2.22/1.03      ( v1_xboole_0(X0) | ~ r1_tarski(X0,sK1) | sK1 = X0 ),
% 2.22/1.03      inference(global_propositional_subsumption,[status(thm)],[c_334,c_23]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_337,plain,
% 2.22/1.03      ( ~ r1_tarski(X0,sK1) | v1_xboole_0(X0) | sK1 = X0 ),
% 2.22/1.03      inference(renaming,[status(thm)],[c_336]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1118,plain,
% 2.22/1.03      ( sK1 = X0
% 2.22/1.03      | r1_tarski(X0,sK1) != iProver_top
% 2.22/1.03      | v1_xboole_0(X0) = iProver_top ),
% 2.22/1.03      inference(predicate_to_equality,[status(thm)],[c_337]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_2510,plain,
% 2.22/1.03      ( k2_tarski(sK2,sK2) = sK1
% 2.22/1.03      | v1_xboole_0(k2_tarski(sK2,sK2)) = iProver_top ),
% 2.22/1.03      inference(superposition,[status(thm)],[c_2362,c_1118]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_21,negated_conjecture,
% 2.22/1.03      ( v1_subset_1(k6_domain_1(sK1,sK2),sK1) ),
% 2.22/1.03      inference(cnf_transformation,[],[f69]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_29,plain,
% 2.22/1.03      ( ~ r1_tarski(sK1,sK1)
% 2.22/1.03      | ~ v1_zfmisc_1(sK1)
% 2.22/1.03      | v1_xboole_0(sK1)
% 2.22/1.03      | sK1 = sK1 ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_19]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_5,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f75]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_63,plain,
% 2.22/1.03      ( r1_tarski(sK1,sK1) ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_5]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_13,plain,
% 2.22/1.03      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~ l1_struct_0(X0) ),
% 2.22/1.03      inference(cnf_transformation,[],[f59]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_15,plain,
% 2.22/1.03      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 2.22/1.03      inference(cnf_transformation,[],[f61]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_17,plain,
% 2.22/1.03      ( l1_orders_2(k2_yellow_1(X0)) ),
% 2.22/1.03      inference(cnf_transformation,[],[f63]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_294,plain,
% 2.22/1.03      ( l1_struct_0(X0) | k2_yellow_1(X1) != X0 ),
% 2.22/1.03      inference(resolution_lifted,[status(thm)],[c_15,c_17]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_295,plain,
% 2.22/1.03      ( l1_struct_0(k2_yellow_1(X0)) ),
% 2.22/1.03      inference(unflattening,[status(thm)],[c_294]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_305,plain,
% 2.22/1.03      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
% 2.22/1.03      | k2_yellow_1(X1) != X0 ),
% 2.22/1.03      inference(resolution_lifted,[status(thm)],[c_13,c_295]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_306,plain,
% 2.22/1.03      ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(X0)),u1_struct_0(k2_yellow_1(X0))) ),
% 2.22/1.03      inference(unflattening,[status(thm)],[c_305]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1119,plain,
% 2.22/1.03      ( v1_subset_1(k2_struct_0(k2_yellow_1(X0)),u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
% 2.22/1.03      inference(predicate_to_equality,[status(thm)],[c_306]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_18,plain,
% 2.22/1.03      ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
% 2.22/1.03      inference(cnf_transformation,[],[f64]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_12,plain,
% 2.22/1.03      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.22/1.03      inference(cnf_transformation,[],[f58]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_314,plain,
% 2.22/1.03      ( k2_yellow_1(X0) != X1 | u1_struct_0(X1) = k2_struct_0(X1) ),
% 2.22/1.03      inference(resolution_lifted,[status(thm)],[c_12,c_295]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_315,plain,
% 2.22/1.03      ( u1_struct_0(k2_yellow_1(X0)) = k2_struct_0(k2_yellow_1(X0)) ),
% 2.22/1.03      inference(unflattening,[status(thm)],[c_314]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1144,plain,
% 2.22/1.03      ( k2_struct_0(k2_yellow_1(X0)) = X0 ),
% 2.22/1.03      inference(light_normalisation,[status(thm)],[c_315,c_18]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1151,plain,
% 2.22/1.03      ( v1_subset_1(X0,X0) != iProver_top ),
% 2.22/1.03      inference(light_normalisation,[status(thm)],[c_1119,c_18,c_1144]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1216,plain,
% 2.22/1.03      ( ~ v1_subset_1(X0,X0) ),
% 2.22/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_1151]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1218,plain,
% 2.22/1.03      ( ~ v1_subset_1(sK1,sK1) ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_1216]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_698,plain,
% 2.22/1.03      ( ~ v1_subset_1(X0,X1) | v1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.22/1.03      theory(equality) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1278,plain,
% 2.22/1.03      ( v1_subset_1(X0,X1)
% 2.22/1.03      | ~ v1_subset_1(k6_domain_1(sK1,sK2),sK1)
% 2.22/1.03      | X0 != k6_domain_1(sK1,sK2)
% 2.22/1.03      | X1 != sK1 ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_698]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1280,plain,
% 2.22/1.03      ( ~ v1_subset_1(k6_domain_1(sK1,sK2),sK1)
% 2.22/1.03      | v1_subset_1(sK1,sK1)
% 2.22/1.03      | sK1 != k6_domain_1(sK1,sK2)
% 2.22/1.03      | sK1 != sK1 ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_1278]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_689,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1354,plain,
% 2.22/1.03      ( X0 != X1 | X0 = k6_domain_1(sK1,sK2) | k6_domain_1(sK1,sK2) != X1 ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_689]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1646,plain,
% 2.22/1.03      ( X0 = k6_domain_1(sK1,sK2)
% 2.22/1.03      | X0 != k2_tarski(sK2,sK2)
% 2.22/1.03      | k6_domain_1(sK1,sK2) != k2_tarski(sK2,sK2) ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_1354]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1647,plain,
% 2.22/1.03      ( k6_domain_1(sK1,sK2) != k2_tarski(sK2,sK2)
% 2.22/1.03      | sK1 = k6_domain_1(sK1,sK2)
% 2.22/1.03      | sK1 != k2_tarski(sK2,sK2) ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_1646]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1784,plain,
% 2.22/1.03      ( ~ r1_tarski(k2_tarski(sK2,sK2),sK1)
% 2.22/1.03      | v1_xboole_0(k2_tarski(sK2,sK2))
% 2.22/1.03      | sK1 = k2_tarski(sK2,sK2) ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_337]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1785,plain,
% 2.22/1.03      ( sK1 = k2_tarski(sK2,sK2)
% 2.22/1.03      | r1_tarski(k2_tarski(sK2,sK2),sK1) != iProver_top
% 2.22/1.03      | v1_xboole_0(k2_tarski(sK2,sK2)) = iProver_top ),
% 2.22/1.03      inference(predicate_to_equality,[status(thm)],[c_1784]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1821,plain,
% 2.22/1.03      ( ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(sK1))
% 2.22/1.03      | r1_tarski(k2_tarski(sK2,sK2),sK1) ),
% 2.22/1.03      inference(instantiation,[status(thm)],[c_10]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1822,plain,
% 2.22/1.03      ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(sK1)) != iProver_top
% 2.22/1.03      | r1_tarski(k2_tarski(sK2,sK2),sK1) = iProver_top ),
% 2.22/1.03      inference(predicate_to_equality,[status(thm)],[c_1821]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_2522,plain,
% 2.22/1.03      ( v1_xboole_0(k2_tarski(sK2,sK2)) = iProver_top ),
% 2.22/1.03      inference(global_propositional_subsumption,
% 2.22/1.03                [status(thm)],
% 2.22/1.03                [c_2510,c_23,c_24,c_22,c_25,c_21,c_20,c_29,c_63,c_1218,
% 2.22/1.03                 c_1265,c_1280,c_1647,c_1785,c_1822,c_2174]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_4,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f74]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1129,plain,
% 2.22/1.03      ( r1_tarski(X0,X0) = iProver_top ),
% 2.22/1.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1,plain,
% 2.22/1.03      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.22/1.03      inference(cnf_transformation,[],[f45]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1132,plain,
% 2.22/1.03      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.22/1.03      | r1_tarski(X0,X1) = iProver_top ),
% 2.22/1.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_11,plain,
% 2.22/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.22/1.03      | ~ r2_hidden(X2,X0)
% 2.22/1.03      | ~ v1_xboole_0(X1) ),
% 2.22/1.03      inference(cnf_transformation,[],[f57]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_9,plain,
% 2.22/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.22/1.03      inference(cnf_transformation,[],[f56]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_164,plain,
% 2.22/1.03      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.22/1.03      inference(prop_impl,[status(thm)],[c_9]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_165,plain,
% 2.22/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.22/1.03      inference(renaming,[status(thm)],[c_164]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_202,plain,
% 2.22/1.03      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 2.22/1.03      inference(bin_hyper_res,[status(thm)],[c_11,c_165]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1120,plain,
% 2.22/1.03      ( r2_hidden(X0,X1) != iProver_top
% 2.22/1.03      | r1_tarski(X1,X2) != iProver_top
% 2.22/1.03      | v1_xboole_0(X2) != iProver_top ),
% 2.22/1.03      inference(predicate_to_equality,[status(thm)],[c_202]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_2046,plain,
% 2.22/1.03      ( r1_tarski(X0,X1) != iProver_top
% 2.22/1.03      | r1_tarski(X0,X2) = iProver_top
% 2.22/1.03      | v1_xboole_0(X1) != iProver_top ),
% 2.22/1.03      inference(superposition,[status(thm)],[c_1132,c_1120]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_2857,plain,
% 2.22/1.03      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 2.22/1.03      inference(superposition,[status(thm)],[c_1129,c_2046]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_7,plain,
% 2.22/1.03      ( r1_tarski(k1_xboole_0,X0) ),
% 2.22/1.03      inference(cnf_transformation,[],[f51]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1128,plain,
% 2.22/1.03      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.22/1.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_3,plain,
% 2.22/1.03      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.22/1.03      inference(cnf_transformation,[],[f49]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1130,plain,
% 2.22/1.03      ( X0 = X1
% 2.22/1.03      | r1_tarski(X1,X0) != iProver_top
% 2.22/1.03      | r1_tarski(X0,X1) != iProver_top ),
% 2.22/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1898,plain,
% 2.22/1.03      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.22/1.03      inference(superposition,[status(thm)],[c_1128,c_1130]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_2942,plain,
% 2.22/1.03      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.22/1.03      inference(superposition,[status(thm)],[c_2857,c_1898]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_3228,plain,
% 2.22/1.03      ( k2_tarski(sK2,sK2) = k1_xboole_0 ),
% 2.22/1.03      inference(superposition,[status(thm)],[c_2522,c_2942]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_6,plain,
% 2.22/1.03      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
% 2.22/1.03      inference(cnf_transformation,[],[f71]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_8,plain,
% 2.22/1.03      ( k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(X1,k2_tarski(X0,X0))) != k1_xboole_0 ),
% 2.22/1.03      inference(cnf_transformation,[],[f72]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_1622,plain,
% 2.22/1.03      ( k2_tarski(X0,X0) != k1_xboole_0 ),
% 2.22/1.03      inference(superposition,[status(thm)],[c_6,c_8]) ).
% 2.22/1.03  
% 2.22/1.03  cnf(c_3243,plain,
% 2.22/1.03      ( $false ),
% 2.22/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_3228,c_1622]) ).
% 2.22/1.03  
% 2.22/1.03  
% 2.22/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.22/1.03  
% 2.22/1.03  ------                               Statistics
% 2.22/1.03  
% 2.22/1.03  ------ General
% 2.22/1.03  
% 2.22/1.03  abstr_ref_over_cycles:                  0
% 2.22/1.03  abstr_ref_under_cycles:                 0
% 2.22/1.03  gc_basic_clause_elim:                   0
% 2.22/1.03  forced_gc_time:                         0
% 2.22/1.03  parsing_time:                           0.009
% 2.22/1.03  unif_index_cands_time:                  0.
% 2.22/1.03  unif_index_add_time:                    0.
% 2.22/1.03  orderings_time:                         0.
% 2.22/1.03  out_proof_time:                         0.009
% 2.22/1.03  total_time:                             0.127
% 2.22/1.03  num_of_symbols:                         51
% 2.22/1.03  num_of_terms:                           2841
% 2.22/1.03  
% 2.22/1.03  ------ Preprocessing
% 2.22/1.03  
% 2.22/1.03  num_of_splits:                          0
% 2.22/1.03  num_of_split_atoms:                     0
% 2.22/1.03  num_of_reused_defs:                     0
% 2.22/1.03  num_eq_ax_congr_red:                    24
% 2.22/1.03  num_of_sem_filtered_clauses:            1
% 2.22/1.03  num_of_subtypes:                        0
% 2.22/1.03  monotx_restored_types:                  0
% 2.22/1.03  sat_num_of_epr_types:                   0
% 2.22/1.03  sat_num_of_non_cyclic_types:            0
% 2.22/1.03  sat_guarded_non_collapsed_types:        0
% 2.22/1.03  num_pure_diseq_elim:                    0
% 2.22/1.03  simp_replaced_by:                       0
% 2.22/1.03  res_preprocessed:                       108
% 2.22/1.03  prep_upred:                             0
% 2.22/1.03  prep_unflattend:                        16
% 2.22/1.03  smt_new_axioms:                         0
% 2.22/1.03  pred_elim_cands:                        5
% 2.22/1.03  pred_elim:                              3
% 2.22/1.03  pred_elim_cl:                           3
% 2.22/1.03  pred_elim_cycles:                       8
% 2.22/1.03  merged_defs:                            8
% 2.22/1.03  merged_defs_ncl:                        0
% 2.22/1.03  bin_hyper_res:                          9
% 2.22/1.03  prep_cycles:                            4
% 2.22/1.03  pred_elim_time:                         0.003
% 2.22/1.03  splitting_time:                         0.
% 2.22/1.03  sem_filter_time:                        0.
% 2.22/1.03  monotx_time:                            0.001
% 2.22/1.03  subtype_inf_time:                       0.
% 2.22/1.03  
% 2.22/1.03  ------ Problem properties
% 2.22/1.03  
% 2.22/1.03  clauses:                                20
% 2.22/1.03  conjectures:                            3
% 2.22/1.03  epr:                                    8
% 2.22/1.03  horn:                                   16
% 2.22/1.03  ground:                                 3
% 2.22/1.03  unary:                                  10
% 2.22/1.03  binary:                                 4
% 2.22/1.03  lits:                                   36
% 2.22/1.03  lits_eq:                                7
% 2.22/1.03  fd_pure:                                0
% 2.22/1.03  fd_pseudo:                              0
% 2.22/1.03  fd_cond:                                1
% 2.22/1.03  fd_pseudo_cond:                         1
% 2.22/1.03  ac_symbols:                             0
% 2.22/1.03  
% 2.22/1.03  ------ Propositional Solver
% 2.22/1.03  
% 2.22/1.03  prop_solver_calls:                      27
% 2.22/1.03  prop_fast_solver_calls:                 572
% 2.22/1.03  smt_solver_calls:                       0
% 2.22/1.03  smt_fast_solver_calls:                  0
% 2.22/1.03  prop_num_of_clauses:                    1166
% 2.22/1.03  prop_preprocess_simplified:             4631
% 2.22/1.03  prop_fo_subsumed:                       6
% 2.22/1.03  prop_solver_time:                       0.
% 2.22/1.03  smt_solver_time:                        0.
% 2.22/1.03  smt_fast_solver_time:                   0.
% 2.22/1.03  prop_fast_solver_time:                  0.
% 2.22/1.03  prop_unsat_core_time:                   0.
% 2.22/1.03  
% 2.22/1.03  ------ QBF
% 2.22/1.03  
% 2.22/1.03  qbf_q_res:                              0
% 2.22/1.03  qbf_num_tautologies:                    0
% 2.22/1.03  qbf_prep_cycles:                        0
% 2.22/1.03  
% 2.22/1.03  ------ BMC1
% 2.22/1.03  
% 2.22/1.03  bmc1_current_bound:                     -1
% 2.22/1.03  bmc1_last_solved_bound:                 -1
% 2.22/1.03  bmc1_unsat_core_size:                   -1
% 2.22/1.03  bmc1_unsat_core_parents_size:           -1
% 2.22/1.03  bmc1_merge_next_fun:                    0
% 2.22/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.22/1.03  
% 2.22/1.03  ------ Instantiation
% 2.22/1.03  
% 2.22/1.03  inst_num_of_clauses:                    396
% 2.22/1.03  inst_num_in_passive:                    144
% 2.22/1.03  inst_num_in_active:                     166
% 2.22/1.03  inst_num_in_unprocessed:                86
% 2.22/1.03  inst_num_of_loops:                      190
% 2.22/1.03  inst_num_of_learning_restarts:          0
% 2.22/1.03  inst_num_moves_active_passive:          22
% 2.22/1.03  inst_lit_activity:                      0
% 2.22/1.03  inst_lit_activity_moves:                0
% 2.22/1.03  inst_num_tautologies:                   0
% 2.22/1.03  inst_num_prop_implied:                  0
% 2.22/1.03  inst_num_existing_simplified:           0
% 2.22/1.03  inst_num_eq_res_simplified:             0
% 2.22/1.03  inst_num_child_elim:                    0
% 2.22/1.03  inst_num_of_dismatching_blockings:      64
% 2.22/1.03  inst_num_of_non_proper_insts:           294
% 2.22/1.03  inst_num_of_duplicates:                 0
% 2.22/1.03  inst_inst_num_from_inst_to_res:         0
% 2.22/1.03  inst_dismatching_checking_time:         0.
% 2.22/1.03  
% 2.22/1.03  ------ Resolution
% 2.22/1.03  
% 2.22/1.03  res_num_of_clauses:                     0
% 2.22/1.03  res_num_in_passive:                     0
% 2.22/1.03  res_num_in_active:                      0
% 2.22/1.03  res_num_of_loops:                       112
% 2.22/1.03  res_forward_subset_subsumed:            25
% 2.22/1.03  res_backward_subset_subsumed:           0
% 2.22/1.03  res_forward_subsumed:                   0
% 2.22/1.03  res_backward_subsumed:                  0
% 2.22/1.03  res_forward_subsumption_resolution:     0
% 2.22/1.03  res_backward_subsumption_resolution:    0
% 2.22/1.03  res_clause_to_clause_subsumption:       131
% 2.22/1.03  res_orphan_elimination:                 0
% 2.22/1.03  res_tautology_del:                      39
% 2.22/1.03  res_num_eq_res_simplified:              0
% 2.22/1.03  res_num_sel_changes:                    0
% 2.22/1.03  res_moves_from_active_to_pass:          0
% 2.22/1.03  
% 2.22/1.03  ------ Superposition
% 2.22/1.03  
% 2.22/1.03  sup_time_total:                         0.
% 2.22/1.03  sup_time_generating:                    0.
% 2.22/1.03  sup_time_sim_full:                      0.
% 2.22/1.03  sup_time_sim_immed:                     0.
% 2.22/1.03  
% 2.22/1.03  sup_num_of_clauses:                     47
% 2.22/1.03  sup_num_in_active:                      36
% 2.22/1.03  sup_num_in_passive:                     11
% 2.22/1.03  sup_num_of_loops:                       37
% 2.22/1.03  sup_fw_superposition:                   23
% 2.22/1.03  sup_bw_superposition:                   18
% 2.22/1.03  sup_immediate_simplified:               5
% 2.22/1.03  sup_given_eliminated:                   0
% 2.22/1.03  comparisons_done:                       0
% 2.22/1.03  comparisons_avoided:                    0
% 2.22/1.03  
% 2.22/1.03  ------ Simplifications
% 2.22/1.03  
% 2.22/1.03  
% 2.22/1.03  sim_fw_subset_subsumed:                 4
% 2.22/1.03  sim_bw_subset_subsumed:                 0
% 2.22/1.03  sim_fw_subsumed:                        1
% 2.22/1.03  sim_bw_subsumed:                        0
% 2.22/1.03  sim_fw_subsumption_res:                 1
% 2.22/1.03  sim_bw_subsumption_res:                 0
% 2.22/1.03  sim_tautology_del:                      2
% 2.22/1.03  sim_eq_tautology_del:                   5
% 2.22/1.03  sim_eq_res_simp:                        0
% 2.22/1.03  sim_fw_demodulated:                     0
% 2.22/1.03  sim_bw_demodulated:                     1
% 2.22/1.03  sim_light_normalised:                   3
% 2.22/1.03  sim_joinable_taut:                      0
% 2.22/1.03  sim_joinable_simp:                      0
% 2.22/1.03  sim_ac_normalised:                      0
% 2.22/1.03  sim_smt_subsumption:                    0
% 2.22/1.03  
%------------------------------------------------------------------------------
