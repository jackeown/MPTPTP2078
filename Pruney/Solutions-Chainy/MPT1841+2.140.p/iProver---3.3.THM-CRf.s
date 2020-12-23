%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:15 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 332 expanded)
%              Number of clauses        :   81 ( 113 expanded)
%              Number of leaves         :   23 (  79 expanded)
%              Depth                    :   18
%              Number of atoms          :  367 (1069 expanded)
%              Number of equality atoms :  147 ( 244 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
     => ( v1_zfmisc_1(X0)
        & v1_subset_1(k6_domain_1(X0,sK2),X0)
        & m1_subset_1(sK2,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
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

fof(f39,plain,
    ( v1_zfmisc_1(sK1)
    & v1_subset_1(k6_domain_1(sK1,sK2),sK1)
    & m1_subset_1(sK2,sK1)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f31,f38,f37])).

fof(f61,plain,(
    m1_subset_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f55,f47])).

fof(f60,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

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

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f59,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f63,plain,(
    v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,(
    v1_subset_1(k6_domain_1(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f43,f47])).

fof(f71,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_tarski(X0,X0)) ) ),
    inference(equality_resolution,[],[f67])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f44,f47])).

fof(f69,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f66])).

fof(f70,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f69])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f54,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f56,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f14,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1011,plain,
    ( m1_subset_1(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1013,plain,
    ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1780,plain,
    ( k6_domain_1(sK1,sK2) = k2_tarski(sK2,sK2)
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1011,c_1013])).

cnf(c_21,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1143,plain,
    ( ~ m1_subset_1(sK2,sK1)
    | v1_xboole_0(sK1)
    | k6_domain_1(sK1,sK2) = k2_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1795,plain,
    ( k6_domain_1(sK1,sK2) = k2_tarski(sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1780,c_21,c_20,c_1143])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1014,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1851,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK2,sK1) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1795,c_1014])).

cnf(c_22,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_23,plain,
    ( m1_subset_1(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2402,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1851,c_22,c_23])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_165,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_166,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_165])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_18,negated_conjecture,
    ( v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_338,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | X1 = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_18])).

cnf(c_339,plain,
    ( ~ r1_tarski(X0,sK1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | sK1 = X0 ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_343,plain,
    ( v1_xboole_0(X0)
    | ~ r1_tarski(X0,sK1)
    | sK1 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_339,c_21])).

cnf(c_344,plain,
    ( ~ r1_tarski(X0,sK1)
    | v1_xboole_0(X0)
    | sK1 = X0 ),
    inference(renaming,[status(thm)],[c_343])).

cnf(c_394,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(X2)
    | X2 != X0
    | sK1 != X1
    | sK1 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_166,c_344])).

cnf(c_395,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
    | v1_xboole_0(X0)
    | sK1 = X0 ),
    inference(unflattening,[status(thm)],[c_394])).

cnf(c_1005,plain,
    ( sK1 = X0
    | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_395])).

cnf(c_2409,plain,
    ( k2_tarski(sK2,sK2) = sK1
    | v1_xboole_0(k2_tarski(sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2402,c_1005])).

cnf(c_19,negated_conjecture,
    ( v1_subset_1(k6_domain_1(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_58,plain,
    ( ~ r2_hidden(sK1,k2_tarski(sK1,sK1))
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( r2_hidden(X0,k2_tarski(X0,X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_61,plain,
    ( r2_hidden(sK1,k2_tarski(sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_11,plain,
    ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_13,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_15,plain,
    ( l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_299,plain,
    ( l1_struct_0(X0)
    | k2_yellow_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_15])).

cnf(c_300,plain,
    ( l1_struct_0(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_299])).

cnf(c_310,plain,
    ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
    | k2_yellow_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_300])).

cnf(c_311,plain,
    ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(X0)),u1_struct_0(k2_yellow_1(X0))) ),
    inference(unflattening,[status(thm)],[c_310])).

cnf(c_1009,plain,
    ( v1_subset_1(k2_struct_0(k2_yellow_1(X0)),u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_311])).

cnf(c_16,plain,
    ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_10,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_319,plain,
    ( k2_yellow_1(X0) != X1
    | u1_struct_0(X1) = k2_struct_0(X1) ),
    inference(resolution_lifted,[status(thm)],[c_10,c_300])).

cnf(c_320,plain,
    ( u1_struct_0(k2_yellow_1(X0)) = k2_struct_0(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_319])).

cnf(c_1033,plain,
    ( k2_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_320,c_16])).

cnf(c_1040,plain,
    ( v1_subset_1(X0,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1009,c_16,c_1033])).

cnf(c_1100,plain,
    ( ~ v1_subset_1(X0,X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1040])).

cnf(c_1102,plain,
    ( ~ v1_subset_1(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_1100])).

cnf(c_1135,plain,
    ( m1_subset_1(k6_domain_1(sK1,sK2),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,sK1)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1136,plain,
    ( m1_subset_1(k6_domain_1(sK1,sK2),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK2,sK1) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1135])).

cnf(c_713,plain,
    ( ~ v1_subset_1(X0,X1)
    | v1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1161,plain,
    ( v1_subset_1(X0,X1)
    | ~ v1_subset_1(k6_domain_1(sK1,sK2),sK1)
    | X0 != k6_domain_1(sK1,sK2)
    | X1 != sK1 ),
    inference(instantiation,[status(thm)],[c_713])).

cnf(c_1163,plain,
    ( ~ v1_subset_1(k6_domain_1(sK1,sK2),sK1)
    | v1_subset_1(sK1,sK1)
    | sK1 != k6_domain_1(sK1,sK2)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1161])).

cnf(c_1268,plain,
    ( ~ m1_subset_1(k6_domain_1(sK1,sK2),k1_zfmisc_1(sK1))
    | v1_xboole_0(k6_domain_1(sK1,sK2))
    | sK1 = k6_domain_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_395])).

cnf(c_1271,plain,
    ( sK1 = k6_domain_1(sK1,sK2)
    | m1_subset_1(k6_domain_1(sK1,sK2),k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(k6_domain_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1268])).

cnf(c_705,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1480,plain,
    ( k2_tarski(X0,X0) = k2_tarski(X0,X0) ),
    inference(instantiation,[status(thm)],[c_705])).

cnf(c_1693,plain,
    ( k2_tarski(sK2,sK2) = k2_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1480])).

cnf(c_706,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1248,plain,
    ( X0 != X1
    | X0 = k6_domain_1(sK1,sK2)
    | k6_domain_1(sK1,sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_706])).

cnf(c_1527,plain,
    ( X0 = k6_domain_1(sK1,sK2)
    | X0 != k2_tarski(sK2,sK2)
    | k6_domain_1(sK1,sK2) != k2_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1248])).

cnf(c_1694,plain,
    ( k6_domain_1(sK1,sK2) != k2_tarski(sK2,sK2)
    | k2_tarski(sK2,sK2) = k6_domain_1(sK1,sK2)
    | k2_tarski(sK2,sK2) != k2_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1527])).

cnf(c_707,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1306,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k6_domain_1(sK1,sK2))
    | X0 != k6_domain_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_707])).

cnf(c_2078,plain,
    ( ~ v1_xboole_0(k6_domain_1(sK1,sK2))
    | v1_xboole_0(k2_tarski(sK2,sK2))
    | k2_tarski(sK2,sK2) != k6_domain_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1306])).

cnf(c_2084,plain,
    ( k2_tarski(sK2,sK2) != k6_domain_1(sK1,sK2)
    | v1_xboole_0(k6_domain_1(sK1,sK2)) != iProver_top
    | v1_xboole_0(k2_tarski(sK2,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2078])).

cnf(c_2636,plain,
    ( v1_xboole_0(k2_tarski(sK2,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2409,c_21,c_22,c_20,c_23,c_19,c_58,c_61,c_1102,c_1136,c_1143,c_1163,c_1271,c_1693,c_1694,c_2084])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1020,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1019,plain,
    ( X0 = X1
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1626,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1020,c_1019])).

cnf(c_2642,plain,
    ( k2_tarski(sK2,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2636,c_1626])).

cnf(c_1016,plain,
    ( r2_hidden(X0,k2_tarski(X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2866,plain,
    ( r2_hidden(sK2,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2642,c_1016])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_371,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_9])).

cnf(c_372,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_371])).

cnf(c_1007,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_372])).

cnf(c_3150,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2866,c_1007])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:38:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.66/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.00  
% 2.66/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.66/1.00  
% 2.66/1.00  ------  iProver source info
% 2.66/1.00  
% 2.66/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.66/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.66/1.00  git: non_committed_changes: false
% 2.66/1.00  git: last_make_outside_of_git: false
% 2.66/1.00  
% 2.66/1.00  ------ 
% 2.66/1.00  
% 2.66/1.00  ------ Input Options
% 2.66/1.00  
% 2.66/1.00  --out_options                           all
% 2.66/1.00  --tptp_safe_out                         true
% 2.66/1.00  --problem_path                          ""
% 2.66/1.00  --include_path                          ""
% 2.66/1.00  --clausifier                            res/vclausify_rel
% 2.66/1.00  --clausifier_options                    --mode clausify
% 2.66/1.00  --stdin                                 false
% 2.66/1.00  --stats_out                             all
% 2.66/1.00  
% 2.66/1.00  ------ General Options
% 2.66/1.00  
% 2.66/1.00  --fof                                   false
% 2.66/1.00  --time_out_real                         305.
% 2.66/1.00  --time_out_virtual                      -1.
% 2.66/1.00  --symbol_type_check                     false
% 2.66/1.00  --clausify_out                          false
% 2.66/1.00  --sig_cnt_out                           false
% 2.66/1.00  --trig_cnt_out                          false
% 2.66/1.00  --trig_cnt_out_tolerance                1.
% 2.66/1.00  --trig_cnt_out_sk_spl                   false
% 2.66/1.00  --abstr_cl_out                          false
% 2.66/1.00  
% 2.66/1.00  ------ Global Options
% 2.66/1.00  
% 2.66/1.00  --schedule                              default
% 2.66/1.00  --add_important_lit                     false
% 2.66/1.00  --prop_solver_per_cl                    1000
% 2.66/1.00  --min_unsat_core                        false
% 2.66/1.00  --soft_assumptions                      false
% 2.66/1.00  --soft_lemma_size                       3
% 2.66/1.00  --prop_impl_unit_size                   0
% 2.66/1.00  --prop_impl_unit                        []
% 2.66/1.00  --share_sel_clauses                     true
% 2.66/1.00  --reset_solvers                         false
% 2.66/1.00  --bc_imp_inh                            [conj_cone]
% 2.66/1.00  --conj_cone_tolerance                   3.
% 2.66/1.00  --extra_neg_conj                        none
% 2.66/1.00  --large_theory_mode                     true
% 2.66/1.00  --prolific_symb_bound                   200
% 2.66/1.00  --lt_threshold                          2000
% 2.66/1.00  --clause_weak_htbl                      true
% 2.66/1.00  --gc_record_bc_elim                     false
% 2.66/1.00  
% 2.66/1.00  ------ Preprocessing Options
% 2.66/1.00  
% 2.66/1.00  --preprocessing_flag                    true
% 2.66/1.00  --time_out_prep_mult                    0.1
% 2.66/1.00  --splitting_mode                        input
% 2.66/1.00  --splitting_grd                         true
% 2.66/1.00  --splitting_cvd                         false
% 2.66/1.00  --splitting_cvd_svl                     false
% 2.66/1.00  --splitting_nvd                         32
% 2.66/1.00  --sub_typing                            true
% 2.66/1.00  --prep_gs_sim                           true
% 2.66/1.00  --prep_unflatten                        true
% 2.66/1.00  --prep_res_sim                          true
% 2.66/1.00  --prep_upred                            true
% 2.66/1.00  --prep_sem_filter                       exhaustive
% 2.66/1.00  --prep_sem_filter_out                   false
% 2.66/1.00  --pred_elim                             true
% 2.66/1.00  --res_sim_input                         true
% 2.66/1.00  --eq_ax_congr_red                       true
% 2.66/1.00  --pure_diseq_elim                       true
% 2.66/1.00  --brand_transform                       false
% 2.66/1.00  --non_eq_to_eq                          false
% 2.66/1.00  --prep_def_merge                        true
% 2.66/1.00  --prep_def_merge_prop_impl              false
% 2.66/1.00  --prep_def_merge_mbd                    true
% 2.66/1.00  --prep_def_merge_tr_red                 false
% 2.66/1.00  --prep_def_merge_tr_cl                  false
% 2.66/1.00  --smt_preprocessing                     true
% 2.66/1.00  --smt_ac_axioms                         fast
% 2.66/1.00  --preprocessed_out                      false
% 2.66/1.00  --preprocessed_stats                    false
% 2.66/1.00  
% 2.66/1.00  ------ Abstraction refinement Options
% 2.66/1.00  
% 2.66/1.00  --abstr_ref                             []
% 2.66/1.00  --abstr_ref_prep                        false
% 2.66/1.00  --abstr_ref_until_sat                   false
% 2.66/1.00  --abstr_ref_sig_restrict                funpre
% 2.66/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.66/1.00  --abstr_ref_under                       []
% 2.66/1.00  
% 2.66/1.00  ------ SAT Options
% 2.66/1.00  
% 2.66/1.00  --sat_mode                              false
% 2.66/1.00  --sat_fm_restart_options                ""
% 2.66/1.00  --sat_gr_def                            false
% 2.66/1.00  --sat_epr_types                         true
% 2.66/1.00  --sat_non_cyclic_types                  false
% 2.66/1.00  --sat_finite_models                     false
% 2.66/1.00  --sat_fm_lemmas                         false
% 2.66/1.00  --sat_fm_prep                           false
% 2.66/1.00  --sat_fm_uc_incr                        true
% 2.66/1.00  --sat_out_model                         small
% 2.66/1.00  --sat_out_clauses                       false
% 2.66/1.00  
% 2.66/1.00  ------ QBF Options
% 2.66/1.00  
% 2.66/1.00  --qbf_mode                              false
% 2.66/1.00  --qbf_elim_univ                         false
% 2.66/1.00  --qbf_dom_inst                          none
% 2.66/1.00  --qbf_dom_pre_inst                      false
% 2.66/1.00  --qbf_sk_in                             false
% 2.66/1.00  --qbf_pred_elim                         true
% 2.66/1.00  --qbf_split                             512
% 2.66/1.00  
% 2.66/1.00  ------ BMC1 Options
% 2.66/1.00  
% 2.66/1.00  --bmc1_incremental                      false
% 2.66/1.00  --bmc1_axioms                           reachable_all
% 2.66/1.00  --bmc1_min_bound                        0
% 2.66/1.00  --bmc1_max_bound                        -1
% 2.66/1.00  --bmc1_max_bound_default                -1
% 2.66/1.00  --bmc1_symbol_reachability              true
% 2.66/1.00  --bmc1_property_lemmas                  false
% 2.66/1.00  --bmc1_k_induction                      false
% 2.66/1.00  --bmc1_non_equiv_states                 false
% 2.66/1.00  --bmc1_deadlock                         false
% 2.66/1.00  --bmc1_ucm                              false
% 2.66/1.00  --bmc1_add_unsat_core                   none
% 2.66/1.00  --bmc1_unsat_core_children              false
% 2.66/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.66/1.00  --bmc1_out_stat                         full
% 2.66/1.00  --bmc1_ground_init                      false
% 2.66/1.00  --bmc1_pre_inst_next_state              false
% 2.66/1.00  --bmc1_pre_inst_state                   false
% 2.66/1.00  --bmc1_pre_inst_reach_state             false
% 2.66/1.00  --bmc1_out_unsat_core                   false
% 2.66/1.00  --bmc1_aig_witness_out                  false
% 2.66/1.00  --bmc1_verbose                          false
% 2.66/1.00  --bmc1_dump_clauses_tptp                false
% 2.66/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.66/1.00  --bmc1_dump_file                        -
% 2.66/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.66/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.66/1.00  --bmc1_ucm_extend_mode                  1
% 2.66/1.00  --bmc1_ucm_init_mode                    2
% 2.66/1.00  --bmc1_ucm_cone_mode                    none
% 2.66/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.66/1.00  --bmc1_ucm_relax_model                  4
% 2.66/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.66/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.66/1.00  --bmc1_ucm_layered_model                none
% 2.66/1.00  --bmc1_ucm_max_lemma_size               10
% 2.66/1.00  
% 2.66/1.00  ------ AIG Options
% 2.66/1.00  
% 2.66/1.00  --aig_mode                              false
% 2.66/1.00  
% 2.66/1.00  ------ Instantiation Options
% 2.66/1.00  
% 2.66/1.00  --instantiation_flag                    true
% 2.66/1.00  --inst_sos_flag                         false
% 2.66/1.00  --inst_sos_phase                        true
% 2.66/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.66/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.66/1.00  --inst_lit_sel_side                     num_symb
% 2.66/1.00  --inst_solver_per_active                1400
% 2.66/1.00  --inst_solver_calls_frac                1.
% 2.66/1.00  --inst_passive_queue_type               priority_queues
% 2.66/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.66/1.00  --inst_passive_queues_freq              [25;2]
% 2.66/1.00  --inst_dismatching                      true
% 2.66/1.00  --inst_eager_unprocessed_to_passive     true
% 2.66/1.00  --inst_prop_sim_given                   true
% 2.66/1.00  --inst_prop_sim_new                     false
% 2.66/1.00  --inst_subs_new                         false
% 2.66/1.00  --inst_eq_res_simp                      false
% 2.66/1.00  --inst_subs_given                       false
% 2.66/1.00  --inst_orphan_elimination               true
% 2.66/1.00  --inst_learning_loop_flag               true
% 2.66/1.00  --inst_learning_start                   3000
% 2.66/1.00  --inst_learning_factor                  2
% 2.66/1.00  --inst_start_prop_sim_after_learn       3
% 2.66/1.00  --inst_sel_renew                        solver
% 2.66/1.00  --inst_lit_activity_flag                true
% 2.66/1.00  --inst_restr_to_given                   false
% 2.66/1.00  --inst_activity_threshold               500
% 2.66/1.00  --inst_out_proof                        true
% 2.66/1.00  
% 2.66/1.00  ------ Resolution Options
% 2.66/1.00  
% 2.66/1.00  --resolution_flag                       true
% 2.66/1.00  --res_lit_sel                           adaptive
% 2.66/1.00  --res_lit_sel_side                      none
% 2.66/1.00  --res_ordering                          kbo
% 2.66/1.00  --res_to_prop_solver                    active
% 2.66/1.00  --res_prop_simpl_new                    false
% 2.66/1.00  --res_prop_simpl_given                  true
% 2.66/1.00  --res_passive_queue_type                priority_queues
% 2.66/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.66/1.00  --res_passive_queues_freq               [15;5]
% 2.66/1.00  --res_forward_subs                      full
% 2.66/1.00  --res_backward_subs                     full
% 2.66/1.00  --res_forward_subs_resolution           true
% 2.66/1.00  --res_backward_subs_resolution          true
% 2.66/1.00  --res_orphan_elimination                true
% 2.66/1.00  --res_time_limit                        2.
% 2.66/1.00  --res_out_proof                         true
% 2.66/1.00  
% 2.66/1.00  ------ Superposition Options
% 2.66/1.00  
% 2.66/1.00  --superposition_flag                    true
% 2.66/1.00  --sup_passive_queue_type                priority_queues
% 2.66/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.66/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.66/1.00  --demod_completeness_check              fast
% 2.66/1.00  --demod_use_ground                      true
% 2.66/1.00  --sup_to_prop_solver                    passive
% 2.66/1.00  --sup_prop_simpl_new                    true
% 2.66/1.00  --sup_prop_simpl_given                  true
% 2.66/1.00  --sup_fun_splitting                     false
% 2.66/1.00  --sup_smt_interval                      50000
% 2.66/1.00  
% 2.66/1.00  ------ Superposition Simplification Setup
% 2.66/1.00  
% 2.66/1.00  --sup_indices_passive                   []
% 2.66/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.66/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/1.00  --sup_full_bw                           [BwDemod]
% 2.66/1.00  --sup_immed_triv                        [TrivRules]
% 2.66/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.66/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/1.00  --sup_immed_bw_main                     []
% 2.66/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.66/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/1.00  
% 2.66/1.00  ------ Combination Options
% 2.66/1.00  
% 2.66/1.00  --comb_res_mult                         3
% 2.66/1.00  --comb_sup_mult                         2
% 2.66/1.00  --comb_inst_mult                        10
% 2.66/1.00  
% 2.66/1.00  ------ Debug Options
% 2.66/1.00  
% 2.66/1.00  --dbg_backtrace                         false
% 2.66/1.00  --dbg_dump_prop_clauses                 false
% 2.66/1.00  --dbg_dump_prop_clauses_file            -
% 2.66/1.00  --dbg_out_stat                          false
% 2.66/1.00  ------ Parsing...
% 2.66/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.66/1.00  
% 2.66/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.66/1.00  
% 2.66/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.66/1.00  
% 2.66/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.66/1.00  ------ Proving...
% 2.66/1.00  ------ Problem Properties 
% 2.66/1.00  
% 2.66/1.00  
% 2.66/1.00  clauses                                 18
% 2.66/1.00  conjectures                             3
% 2.66/1.00  EPR                                     5
% 2.66/1.00  Horn                                    14
% 2.66/1.00  unary                                   10
% 2.66/1.00  binary                                  2
% 2.66/1.00  lits                                    32
% 2.66/1.00  lits eq                                 10
% 2.66/1.00  fd_pure                                 0
% 2.66/1.00  fd_pseudo                               0
% 2.66/1.00  fd_cond                                 1
% 2.66/1.00  fd_pseudo_cond                          3
% 2.66/1.00  AC symbols                              0
% 2.66/1.00  
% 2.66/1.00  ------ Schedule dynamic 5 is on 
% 2.66/1.00  
% 2.66/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.66/1.00  
% 2.66/1.00  
% 2.66/1.00  ------ 
% 2.66/1.00  Current options:
% 2.66/1.00  ------ 
% 2.66/1.00  
% 2.66/1.00  ------ Input Options
% 2.66/1.00  
% 2.66/1.00  --out_options                           all
% 2.66/1.00  --tptp_safe_out                         true
% 2.66/1.00  --problem_path                          ""
% 2.66/1.00  --include_path                          ""
% 2.66/1.00  --clausifier                            res/vclausify_rel
% 2.66/1.00  --clausifier_options                    --mode clausify
% 2.66/1.00  --stdin                                 false
% 2.66/1.00  --stats_out                             all
% 2.66/1.00  
% 2.66/1.00  ------ General Options
% 2.66/1.00  
% 2.66/1.00  --fof                                   false
% 2.66/1.00  --time_out_real                         305.
% 2.66/1.00  --time_out_virtual                      -1.
% 2.66/1.00  --symbol_type_check                     false
% 2.66/1.00  --clausify_out                          false
% 2.66/1.00  --sig_cnt_out                           false
% 2.66/1.00  --trig_cnt_out                          false
% 2.66/1.00  --trig_cnt_out_tolerance                1.
% 2.66/1.00  --trig_cnt_out_sk_spl                   false
% 2.66/1.00  --abstr_cl_out                          false
% 2.66/1.00  
% 2.66/1.00  ------ Global Options
% 2.66/1.00  
% 2.66/1.00  --schedule                              default
% 2.66/1.00  --add_important_lit                     false
% 2.66/1.00  --prop_solver_per_cl                    1000
% 2.66/1.00  --min_unsat_core                        false
% 2.66/1.00  --soft_assumptions                      false
% 2.66/1.00  --soft_lemma_size                       3
% 2.66/1.00  --prop_impl_unit_size                   0
% 2.66/1.00  --prop_impl_unit                        []
% 2.66/1.00  --share_sel_clauses                     true
% 2.66/1.00  --reset_solvers                         false
% 2.66/1.00  --bc_imp_inh                            [conj_cone]
% 2.66/1.00  --conj_cone_tolerance                   3.
% 2.66/1.00  --extra_neg_conj                        none
% 2.66/1.00  --large_theory_mode                     true
% 2.66/1.00  --prolific_symb_bound                   200
% 2.66/1.00  --lt_threshold                          2000
% 2.66/1.00  --clause_weak_htbl                      true
% 2.66/1.00  --gc_record_bc_elim                     false
% 2.66/1.00  
% 2.66/1.00  ------ Preprocessing Options
% 2.66/1.00  
% 2.66/1.00  --preprocessing_flag                    true
% 2.66/1.00  --time_out_prep_mult                    0.1
% 2.66/1.00  --splitting_mode                        input
% 2.66/1.00  --splitting_grd                         true
% 2.66/1.00  --splitting_cvd                         false
% 2.66/1.00  --splitting_cvd_svl                     false
% 2.66/1.00  --splitting_nvd                         32
% 2.66/1.00  --sub_typing                            true
% 2.66/1.00  --prep_gs_sim                           true
% 2.66/1.00  --prep_unflatten                        true
% 2.66/1.00  --prep_res_sim                          true
% 2.66/1.00  --prep_upred                            true
% 2.66/1.00  --prep_sem_filter                       exhaustive
% 2.66/1.00  --prep_sem_filter_out                   false
% 2.66/1.00  --pred_elim                             true
% 2.66/1.00  --res_sim_input                         true
% 2.66/1.00  --eq_ax_congr_red                       true
% 2.66/1.00  --pure_diseq_elim                       true
% 2.66/1.00  --brand_transform                       false
% 2.66/1.00  --non_eq_to_eq                          false
% 2.66/1.00  --prep_def_merge                        true
% 2.66/1.00  --prep_def_merge_prop_impl              false
% 2.66/1.00  --prep_def_merge_mbd                    true
% 2.66/1.00  --prep_def_merge_tr_red                 false
% 2.66/1.00  --prep_def_merge_tr_cl                  false
% 2.66/1.00  --smt_preprocessing                     true
% 2.66/1.00  --smt_ac_axioms                         fast
% 2.66/1.00  --preprocessed_out                      false
% 2.66/1.00  --preprocessed_stats                    false
% 2.66/1.00  
% 2.66/1.00  ------ Abstraction refinement Options
% 2.66/1.00  
% 2.66/1.00  --abstr_ref                             []
% 2.66/1.00  --abstr_ref_prep                        false
% 2.66/1.00  --abstr_ref_until_sat                   false
% 2.66/1.00  --abstr_ref_sig_restrict                funpre
% 2.66/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.66/1.00  --abstr_ref_under                       []
% 2.66/1.00  
% 2.66/1.00  ------ SAT Options
% 2.66/1.00  
% 2.66/1.00  --sat_mode                              false
% 2.66/1.00  --sat_fm_restart_options                ""
% 2.66/1.00  --sat_gr_def                            false
% 2.66/1.00  --sat_epr_types                         true
% 2.66/1.00  --sat_non_cyclic_types                  false
% 2.66/1.00  --sat_finite_models                     false
% 2.66/1.00  --sat_fm_lemmas                         false
% 2.66/1.00  --sat_fm_prep                           false
% 2.66/1.00  --sat_fm_uc_incr                        true
% 2.66/1.00  --sat_out_model                         small
% 2.66/1.00  --sat_out_clauses                       false
% 2.66/1.00  
% 2.66/1.00  ------ QBF Options
% 2.66/1.00  
% 2.66/1.00  --qbf_mode                              false
% 2.66/1.00  --qbf_elim_univ                         false
% 2.66/1.00  --qbf_dom_inst                          none
% 2.66/1.00  --qbf_dom_pre_inst                      false
% 2.66/1.00  --qbf_sk_in                             false
% 2.66/1.00  --qbf_pred_elim                         true
% 2.66/1.00  --qbf_split                             512
% 2.66/1.00  
% 2.66/1.00  ------ BMC1 Options
% 2.66/1.00  
% 2.66/1.00  --bmc1_incremental                      false
% 2.66/1.00  --bmc1_axioms                           reachable_all
% 2.66/1.00  --bmc1_min_bound                        0
% 2.66/1.00  --bmc1_max_bound                        -1
% 2.66/1.00  --bmc1_max_bound_default                -1
% 2.66/1.00  --bmc1_symbol_reachability              true
% 2.66/1.00  --bmc1_property_lemmas                  false
% 2.66/1.00  --bmc1_k_induction                      false
% 2.66/1.00  --bmc1_non_equiv_states                 false
% 2.66/1.00  --bmc1_deadlock                         false
% 2.66/1.00  --bmc1_ucm                              false
% 2.66/1.00  --bmc1_add_unsat_core                   none
% 2.66/1.00  --bmc1_unsat_core_children              false
% 2.66/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.66/1.00  --bmc1_out_stat                         full
% 2.66/1.00  --bmc1_ground_init                      false
% 2.66/1.00  --bmc1_pre_inst_next_state              false
% 2.66/1.00  --bmc1_pre_inst_state                   false
% 2.66/1.00  --bmc1_pre_inst_reach_state             false
% 2.66/1.00  --bmc1_out_unsat_core                   false
% 2.66/1.00  --bmc1_aig_witness_out                  false
% 2.66/1.00  --bmc1_verbose                          false
% 2.66/1.00  --bmc1_dump_clauses_tptp                false
% 2.66/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.66/1.00  --bmc1_dump_file                        -
% 2.66/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.66/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.66/1.00  --bmc1_ucm_extend_mode                  1
% 2.66/1.00  --bmc1_ucm_init_mode                    2
% 2.66/1.00  --bmc1_ucm_cone_mode                    none
% 2.66/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.66/1.00  --bmc1_ucm_relax_model                  4
% 2.66/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.66/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.66/1.00  --bmc1_ucm_layered_model                none
% 2.66/1.00  --bmc1_ucm_max_lemma_size               10
% 2.66/1.00  
% 2.66/1.00  ------ AIG Options
% 2.66/1.00  
% 2.66/1.00  --aig_mode                              false
% 2.66/1.00  
% 2.66/1.00  ------ Instantiation Options
% 2.66/1.00  
% 2.66/1.00  --instantiation_flag                    true
% 2.66/1.00  --inst_sos_flag                         false
% 2.66/1.00  --inst_sos_phase                        true
% 2.66/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.66/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.66/1.00  --inst_lit_sel_side                     none
% 2.66/1.00  --inst_solver_per_active                1400
% 2.66/1.00  --inst_solver_calls_frac                1.
% 2.66/1.00  --inst_passive_queue_type               priority_queues
% 2.66/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.66/1.00  --inst_passive_queues_freq              [25;2]
% 2.66/1.00  --inst_dismatching                      true
% 2.66/1.00  --inst_eager_unprocessed_to_passive     true
% 2.66/1.00  --inst_prop_sim_given                   true
% 2.66/1.00  --inst_prop_sim_new                     false
% 2.66/1.00  --inst_subs_new                         false
% 2.66/1.00  --inst_eq_res_simp                      false
% 2.66/1.00  --inst_subs_given                       false
% 2.66/1.00  --inst_orphan_elimination               true
% 2.66/1.00  --inst_learning_loop_flag               true
% 2.66/1.00  --inst_learning_start                   3000
% 2.66/1.00  --inst_learning_factor                  2
% 2.66/1.00  --inst_start_prop_sim_after_learn       3
% 2.66/1.00  --inst_sel_renew                        solver
% 2.66/1.00  --inst_lit_activity_flag                true
% 2.66/1.00  --inst_restr_to_given                   false
% 2.66/1.00  --inst_activity_threshold               500
% 2.66/1.00  --inst_out_proof                        true
% 2.66/1.00  
% 2.66/1.00  ------ Resolution Options
% 2.66/1.00  
% 2.66/1.00  --resolution_flag                       false
% 2.66/1.00  --res_lit_sel                           adaptive
% 2.66/1.00  --res_lit_sel_side                      none
% 2.66/1.00  --res_ordering                          kbo
% 2.66/1.00  --res_to_prop_solver                    active
% 2.66/1.00  --res_prop_simpl_new                    false
% 2.66/1.00  --res_prop_simpl_given                  true
% 2.66/1.00  --res_passive_queue_type                priority_queues
% 2.66/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.66/1.00  --res_passive_queues_freq               [15;5]
% 2.66/1.00  --res_forward_subs                      full
% 2.66/1.00  --res_backward_subs                     full
% 2.66/1.00  --res_forward_subs_resolution           true
% 2.66/1.00  --res_backward_subs_resolution          true
% 2.66/1.00  --res_orphan_elimination                true
% 2.66/1.00  --res_time_limit                        2.
% 2.66/1.00  --res_out_proof                         true
% 2.66/1.00  
% 2.66/1.00  ------ Superposition Options
% 2.66/1.00  
% 2.66/1.00  --superposition_flag                    true
% 2.66/1.00  --sup_passive_queue_type                priority_queues
% 2.66/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.66/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.66/1.00  --demod_completeness_check              fast
% 2.66/1.00  --demod_use_ground                      true
% 2.66/1.00  --sup_to_prop_solver                    passive
% 2.66/1.00  --sup_prop_simpl_new                    true
% 2.66/1.00  --sup_prop_simpl_given                  true
% 2.66/1.00  --sup_fun_splitting                     false
% 2.66/1.00  --sup_smt_interval                      50000
% 2.66/1.00  
% 2.66/1.00  ------ Superposition Simplification Setup
% 2.66/1.00  
% 2.66/1.00  --sup_indices_passive                   []
% 2.66/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.66/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/1.00  --sup_full_bw                           [BwDemod]
% 2.66/1.00  --sup_immed_triv                        [TrivRules]
% 2.66/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.66/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/1.00  --sup_immed_bw_main                     []
% 2.66/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.66/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/1.00  
% 2.66/1.00  ------ Combination Options
% 2.66/1.00  
% 2.66/1.00  --comb_res_mult                         3
% 2.66/1.00  --comb_sup_mult                         2
% 2.66/1.00  --comb_inst_mult                        10
% 2.66/1.00  
% 2.66/1.00  ------ Debug Options
% 2.66/1.00  
% 2.66/1.00  --dbg_backtrace                         false
% 2.66/1.00  --dbg_dump_prop_clauses                 false
% 2.66/1.00  --dbg_dump_prop_clauses_file            -
% 2.66/1.00  --dbg_out_stat                          false
% 2.66/1.00  
% 2.66/1.00  
% 2.66/1.00  
% 2.66/1.00  
% 2.66/1.00  ------ Proving...
% 2.66/1.00  
% 2.66/1.00  
% 2.66/1.00  % SZS status Theorem for theBenchmark.p
% 2.66/1.00  
% 2.66/1.00   Resolution empty clause
% 2.66/1.00  
% 2.66/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.66/1.00  
% 2.66/1.00  fof(f16,conjecture,(
% 2.66/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 2.66/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/1.00  
% 2.66/1.00  fof(f17,negated_conjecture,(
% 2.66/1.00    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 2.66/1.00    inference(negated_conjecture,[],[f16])).
% 2.66/1.00  
% 2.66/1.00  fof(f30,plain,(
% 2.66/1.00    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 2.66/1.00    inference(ennf_transformation,[],[f17])).
% 2.66/1.00  
% 2.66/1.00  fof(f31,plain,(
% 2.66/1.00    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 2.66/1.00    inference(flattening,[],[f30])).
% 2.66/1.00  
% 2.66/1.00  fof(f38,plain,(
% 2.66/1.00    ( ! [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) => (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,sK2),X0) & m1_subset_1(sK2,X0))) )),
% 2.66/1.00    introduced(choice_axiom,[])).
% 2.66/1.00  
% 2.66/1.00  fof(f37,plain,(
% 2.66/1.00    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK1) & v1_subset_1(k6_domain_1(sK1,X1),sK1) & m1_subset_1(X1,sK1)) & ~v1_xboole_0(sK1))),
% 2.66/1.00    introduced(choice_axiom,[])).
% 2.66/1.00  
% 2.66/1.00  fof(f39,plain,(
% 2.66/1.00    (v1_zfmisc_1(sK1) & v1_subset_1(k6_domain_1(sK1,sK2),sK1) & m1_subset_1(sK2,sK1)) & ~v1_xboole_0(sK1)),
% 2.66/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f31,f38,f37])).
% 2.66/1.00  
% 2.66/1.00  fof(f61,plain,(
% 2.66/1.00    m1_subset_1(sK2,sK1)),
% 2.66/1.00    inference(cnf_transformation,[],[f39])).
% 2.66/1.00  
% 2.66/1.00  fof(f12,axiom,(
% 2.66/1.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.66/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/1.00  
% 2.66/1.00  fof(f26,plain,(
% 2.66/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.66/1.00    inference(ennf_transformation,[],[f12])).
% 2.66/1.00  
% 2.66/1.00  fof(f27,plain,(
% 2.66/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.66/1.00    inference(flattening,[],[f26])).
% 2.66/1.00  
% 2.66/1.00  fof(f55,plain,(
% 2.66/1.00    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.66/1.00    inference(cnf_transformation,[],[f27])).
% 2.66/1.00  
% 2.66/1.00  fof(f5,axiom,(
% 2.66/1.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.66/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/1.00  
% 2.66/1.00  fof(f47,plain,(
% 2.66/1.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.66/1.00    inference(cnf_transformation,[],[f5])).
% 2.66/1.00  
% 2.66/1.00  fof(f68,plain,(
% 2.66/1.00    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.66/1.00    inference(definition_unfolding,[],[f55,f47])).
% 2.66/1.00  
% 2.66/1.00  fof(f60,plain,(
% 2.66/1.00    ~v1_xboole_0(sK1)),
% 2.66/1.00    inference(cnf_transformation,[],[f39])).
% 2.66/1.00  
% 2.66/1.00  fof(f10,axiom,(
% 2.66/1.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.66/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/1.00  
% 2.66/1.00  fof(f23,plain,(
% 2.66/1.00    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.66/1.00    inference(ennf_transformation,[],[f10])).
% 2.66/1.00  
% 2.66/1.00  fof(f24,plain,(
% 2.66/1.00    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.66/1.00    inference(flattening,[],[f23])).
% 2.66/1.00  
% 2.66/1.00  fof(f53,plain,(
% 2.66/1.00    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.66/1.00    inference(cnf_transformation,[],[f24])).
% 2.66/1.00  
% 2.66/1.00  fof(f6,axiom,(
% 2.66/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.66/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/1.00  
% 2.66/1.00  fof(f36,plain,(
% 2.66/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.66/1.00    inference(nnf_transformation,[],[f6])).
% 2.66/1.00  
% 2.66/1.00  fof(f48,plain,(
% 2.66/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.66/1.00    inference(cnf_transformation,[],[f36])).
% 2.66/1.00  
% 2.66/1.00  fof(f15,axiom,(
% 2.66/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 2.66/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/1.00  
% 2.66/1.00  fof(f28,plain,(
% 2.66/1.00    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 2.66/1.00    inference(ennf_transformation,[],[f15])).
% 2.66/1.00  
% 2.66/1.00  fof(f29,plain,(
% 2.66/1.00    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.66/1.00    inference(flattening,[],[f28])).
% 2.66/1.00  
% 2.66/1.00  fof(f59,plain,(
% 2.66/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.66/1.00    inference(cnf_transformation,[],[f29])).
% 2.66/1.00  
% 2.66/1.00  fof(f63,plain,(
% 2.66/1.00    v1_zfmisc_1(sK1)),
% 2.66/1.00    inference(cnf_transformation,[],[f39])).
% 2.66/1.00  
% 2.66/1.00  fof(f62,plain,(
% 2.66/1.00    v1_subset_1(k6_domain_1(sK1,sK2),sK1)),
% 2.66/1.00    inference(cnf_transformation,[],[f39])).
% 2.66/1.00  
% 2.66/1.00  fof(f4,axiom,(
% 2.66/1.00    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.66/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/1.00  
% 2.66/1.00  fof(f32,plain,(
% 2.66/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.66/1.00    inference(nnf_transformation,[],[f4])).
% 2.66/1.00  
% 2.66/1.00  fof(f33,plain,(
% 2.66/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.66/1.00    inference(rectify,[],[f32])).
% 2.66/1.00  
% 2.66/1.00  fof(f34,plain,(
% 2.66/1.00    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 2.66/1.00    introduced(choice_axiom,[])).
% 2.66/1.00  
% 2.66/1.00  fof(f35,plain,(
% 2.66/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.66/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 2.66/1.00  
% 2.66/1.00  fof(f43,plain,(
% 2.66/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.66/1.00    inference(cnf_transformation,[],[f35])).
% 2.66/1.00  
% 2.66/1.00  fof(f67,plain,(
% 2.66/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 2.66/1.00    inference(definition_unfolding,[],[f43,f47])).
% 2.66/1.00  
% 2.66/1.00  fof(f71,plain,(
% 2.66/1.00    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_tarski(X0,X0))) )),
% 2.66/1.00    inference(equality_resolution,[],[f67])).
% 2.66/1.00  
% 2.66/1.00  fof(f44,plain,(
% 2.66/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.66/1.00    inference(cnf_transformation,[],[f35])).
% 2.66/1.00  
% 2.66/1.00  fof(f66,plain,(
% 2.66/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 2.66/1.00    inference(definition_unfolding,[],[f44,f47])).
% 2.66/1.00  
% 2.66/1.00  fof(f69,plain,(
% 2.66/1.00    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 2.66/1.00    inference(equality_resolution,[],[f66])).
% 2.66/1.00  
% 2.66/1.00  fof(f70,plain,(
% 2.66/1.00    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 2.66/1.00    inference(equality_resolution,[],[f69])).
% 2.66/1.00  
% 2.66/1.00  fof(f9,axiom,(
% 2.66/1.00    ! [X0] : (l1_struct_0(X0) => ~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)))),
% 2.66/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/1.00  
% 2.66/1.00  fof(f22,plain,(
% 2.66/1.00    ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0))),
% 2.66/1.00    inference(ennf_transformation,[],[f9])).
% 2.66/1.00  
% 2.66/1.00  fof(f52,plain,(
% 2.66/1.00    ( ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 2.66/1.00    inference(cnf_transformation,[],[f22])).
% 2.66/1.00  
% 2.66/1.00  fof(f11,axiom,(
% 2.66/1.00    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 2.66/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/1.00  
% 2.66/1.00  fof(f25,plain,(
% 2.66/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 2.66/1.00    inference(ennf_transformation,[],[f11])).
% 2.66/1.00  
% 2.66/1.00  fof(f54,plain,(
% 2.66/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 2.66/1.00    inference(cnf_transformation,[],[f25])).
% 2.66/1.00  
% 2.66/1.00  fof(f13,axiom,(
% 2.66/1.00    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 2.66/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/1.00  
% 2.66/1.00  fof(f18,plain,(
% 2.66/1.00    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 2.66/1.00    inference(pure_predicate_removal,[],[f13])).
% 2.66/1.00  
% 2.66/1.00  fof(f56,plain,(
% 2.66/1.00    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 2.66/1.00    inference(cnf_transformation,[],[f18])).
% 2.66/1.00  
% 2.66/1.00  fof(f14,axiom,(
% 2.66/1.00    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 2.66/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/1.00  
% 2.66/1.00  fof(f57,plain,(
% 2.66/1.00    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 2.66/1.00    inference(cnf_transformation,[],[f14])).
% 2.66/1.00  
% 2.66/1.00  fof(f8,axiom,(
% 2.66/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.66/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/1.00  
% 2.66/1.00  fof(f21,plain,(
% 2.66/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.66/1.00    inference(ennf_transformation,[],[f8])).
% 2.66/1.00  
% 2.66/1.00  fof(f51,plain,(
% 2.66/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.66/1.00    inference(cnf_transformation,[],[f21])).
% 2.66/1.00  
% 2.66/1.00  fof(f1,axiom,(
% 2.66/1.00    v1_xboole_0(k1_xboole_0)),
% 2.66/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/1.00  
% 2.66/1.00  fof(f40,plain,(
% 2.66/1.00    v1_xboole_0(k1_xboole_0)),
% 2.66/1.00    inference(cnf_transformation,[],[f1])).
% 2.66/1.00  
% 2.66/1.00  fof(f3,axiom,(
% 2.66/1.00    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.66/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/1.00  
% 2.66/1.00  fof(f19,plain,(
% 2.66/1.00    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.66/1.00    inference(ennf_transformation,[],[f3])).
% 2.66/1.00  
% 2.66/1.00  fof(f42,plain,(
% 2.66/1.00    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 2.66/1.00    inference(cnf_transformation,[],[f19])).
% 2.66/1.00  
% 2.66/1.00  fof(f2,axiom,(
% 2.66/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.66/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/1.00  
% 2.66/1.00  fof(f41,plain,(
% 2.66/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.66/1.00    inference(cnf_transformation,[],[f2])).
% 2.66/1.00  
% 2.66/1.00  fof(f7,axiom,(
% 2.66/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.66/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/1.00  
% 2.66/1.00  fof(f20,plain,(
% 2.66/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.66/1.00    inference(ennf_transformation,[],[f7])).
% 2.66/1.00  
% 2.66/1.00  fof(f50,plain,(
% 2.66/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.66/1.00    inference(cnf_transformation,[],[f20])).
% 2.66/1.00  
% 2.66/1.00  cnf(c_20,negated_conjecture,
% 2.66/1.00      ( m1_subset_1(sK2,sK1) ),
% 2.66/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1011,plain,
% 2.66/1.00      ( m1_subset_1(sK2,sK1) = iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_14,plain,
% 2.66/1.00      ( ~ m1_subset_1(X0,X1)
% 2.66/1.00      | v1_xboole_0(X1)
% 2.66/1.00      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 2.66/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1013,plain,
% 2.66/1.00      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
% 2.66/1.00      | m1_subset_1(X1,X0) != iProver_top
% 2.66/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1780,plain,
% 2.66/1.00      ( k6_domain_1(sK1,sK2) = k2_tarski(sK2,sK2)
% 2.66/1.00      | v1_xboole_0(sK1) = iProver_top ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_1011,c_1013]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_21,negated_conjecture,
% 2.66/1.00      ( ~ v1_xboole_0(sK1) ),
% 2.66/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1143,plain,
% 2.66/1.00      ( ~ m1_subset_1(sK2,sK1)
% 2.66/1.00      | v1_xboole_0(sK1)
% 2.66/1.00      | k6_domain_1(sK1,sK2) = k2_tarski(sK2,sK2) ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1795,plain,
% 2.66/1.00      ( k6_domain_1(sK1,sK2) = k2_tarski(sK2,sK2) ),
% 2.66/1.00      inference(global_propositional_subsumption,
% 2.66/1.00                [status(thm)],
% 2.66/1.00                [c_1780,c_21,c_20,c_1143]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_12,plain,
% 2.66/1.00      ( ~ m1_subset_1(X0,X1)
% 2.66/1.00      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 2.66/1.00      | v1_xboole_0(X1) ),
% 2.66/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1014,plain,
% 2.66/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 2.66/1.00      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
% 2.66/1.00      | v1_xboole_0(X1) = iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1851,plain,
% 2.66/1.00      ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(sK1)) = iProver_top
% 2.66/1.00      | m1_subset_1(sK2,sK1) != iProver_top
% 2.66/1.00      | v1_xboole_0(sK1) = iProver_top ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_1795,c_1014]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_22,plain,
% 2.66/1.00      ( v1_xboole_0(sK1) != iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_23,plain,
% 2.66/1.00      ( m1_subset_1(sK2,sK1) = iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2402,plain,
% 2.66/1.00      ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(sK1)) = iProver_top ),
% 2.66/1.00      inference(global_propositional_subsumption,
% 2.66/1.00                [status(thm)],
% 2.66/1.00                [c_1851,c_22,c_23]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_8,plain,
% 2.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.66/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_165,plain,
% 2.66/1.00      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.66/1.00      inference(prop_impl,[status(thm)],[c_8]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_166,plain,
% 2.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.66/1.00      inference(renaming,[status(thm)],[c_165]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_17,plain,
% 2.66/1.00      ( ~ r1_tarski(X0,X1)
% 2.66/1.00      | ~ v1_zfmisc_1(X1)
% 2.66/1.00      | v1_xboole_0(X1)
% 2.66/1.00      | v1_xboole_0(X0)
% 2.66/1.00      | X1 = X0 ),
% 2.66/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_18,negated_conjecture,
% 2.66/1.00      ( v1_zfmisc_1(sK1) ),
% 2.66/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_338,plain,
% 2.66/1.00      ( ~ r1_tarski(X0,X1)
% 2.66/1.00      | v1_xboole_0(X1)
% 2.66/1.00      | v1_xboole_0(X0)
% 2.66/1.00      | X1 = X0
% 2.66/1.00      | sK1 != X1 ),
% 2.66/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_18]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_339,plain,
% 2.66/1.00      ( ~ r1_tarski(X0,sK1) | v1_xboole_0(X0) | v1_xboole_0(sK1) | sK1 = X0 ),
% 2.66/1.00      inference(unflattening,[status(thm)],[c_338]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_343,plain,
% 2.66/1.00      ( v1_xboole_0(X0) | ~ r1_tarski(X0,sK1) | sK1 = X0 ),
% 2.66/1.00      inference(global_propositional_subsumption,[status(thm)],[c_339,c_21]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_344,plain,
% 2.66/1.00      ( ~ r1_tarski(X0,sK1) | v1_xboole_0(X0) | sK1 = X0 ),
% 2.66/1.00      inference(renaming,[status(thm)],[c_343]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_394,plain,
% 2.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.66/1.00      | v1_xboole_0(X2)
% 2.66/1.00      | X2 != X0
% 2.66/1.00      | sK1 != X1
% 2.66/1.00      | sK1 = X2 ),
% 2.66/1.00      inference(resolution_lifted,[status(thm)],[c_166,c_344]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_395,plain,
% 2.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1)) | v1_xboole_0(X0) | sK1 = X0 ),
% 2.66/1.00      inference(unflattening,[status(thm)],[c_394]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1005,plain,
% 2.66/1.00      ( sK1 = X0
% 2.66/1.00      | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
% 2.66/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_395]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2409,plain,
% 2.66/1.00      ( k2_tarski(sK2,sK2) = sK1
% 2.66/1.00      | v1_xboole_0(k2_tarski(sK2,sK2)) = iProver_top ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_2402,c_1005]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_19,negated_conjecture,
% 2.66/1.00      ( v1_subset_1(k6_domain_1(sK1,sK2),sK1) ),
% 2.66/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_6,plain,
% 2.66/1.00      ( ~ r2_hidden(X0,k2_tarski(X1,X1)) | X0 = X1 ),
% 2.66/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_58,plain,
% 2.66/1.00      ( ~ r2_hidden(sK1,k2_tarski(sK1,sK1)) | sK1 = sK1 ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_5,plain,
% 2.66/1.00      ( r2_hidden(X0,k2_tarski(X0,X0)) ),
% 2.66/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_61,plain,
% 2.66/1.00      ( r2_hidden(sK1,k2_tarski(sK1,sK1)) ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_11,plain,
% 2.66/1.00      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~ l1_struct_0(X0) ),
% 2.66/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_13,plain,
% 2.66/1.00      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 2.66/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_15,plain,
% 2.66/1.00      ( l1_orders_2(k2_yellow_1(X0)) ),
% 2.66/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_299,plain,
% 2.66/1.00      ( l1_struct_0(X0) | k2_yellow_1(X1) != X0 ),
% 2.66/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_15]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_300,plain,
% 2.66/1.00      ( l1_struct_0(k2_yellow_1(X0)) ),
% 2.66/1.00      inference(unflattening,[status(thm)],[c_299]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_310,plain,
% 2.66/1.00      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
% 2.66/1.00      | k2_yellow_1(X1) != X0 ),
% 2.66/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_300]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_311,plain,
% 2.66/1.00      ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(X0)),u1_struct_0(k2_yellow_1(X0))) ),
% 2.66/1.00      inference(unflattening,[status(thm)],[c_310]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1009,plain,
% 2.66/1.00      ( v1_subset_1(k2_struct_0(k2_yellow_1(X0)),u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_311]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_16,plain,
% 2.66/1.00      ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
% 2.66/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_10,plain,
% 2.66/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.66/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_319,plain,
% 2.66/1.00      ( k2_yellow_1(X0) != X1 | u1_struct_0(X1) = k2_struct_0(X1) ),
% 2.66/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_300]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_320,plain,
% 2.66/1.00      ( u1_struct_0(k2_yellow_1(X0)) = k2_struct_0(k2_yellow_1(X0)) ),
% 2.66/1.00      inference(unflattening,[status(thm)],[c_319]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1033,plain,
% 2.66/1.00      ( k2_struct_0(k2_yellow_1(X0)) = X0 ),
% 2.66/1.00      inference(light_normalisation,[status(thm)],[c_320,c_16]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1040,plain,
% 2.66/1.00      ( v1_subset_1(X0,X0) != iProver_top ),
% 2.66/1.00      inference(light_normalisation,[status(thm)],[c_1009,c_16,c_1033]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1100,plain,
% 2.66/1.00      ( ~ v1_subset_1(X0,X0) ),
% 2.66/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1040]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1102,plain,
% 2.66/1.00      ( ~ v1_subset_1(sK1,sK1) ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_1100]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1135,plain,
% 2.66/1.00      ( m1_subset_1(k6_domain_1(sK1,sK2),k1_zfmisc_1(sK1))
% 2.66/1.00      | ~ m1_subset_1(sK2,sK1)
% 2.66/1.00      | v1_xboole_0(sK1) ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1136,plain,
% 2.66/1.00      ( m1_subset_1(k6_domain_1(sK1,sK2),k1_zfmisc_1(sK1)) = iProver_top
% 2.66/1.00      | m1_subset_1(sK2,sK1) != iProver_top
% 2.66/1.00      | v1_xboole_0(sK1) = iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_1135]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_713,plain,
% 2.66/1.00      ( ~ v1_subset_1(X0,X1) | v1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.66/1.00      theory(equality) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1161,plain,
% 2.66/1.00      ( v1_subset_1(X0,X1)
% 2.66/1.00      | ~ v1_subset_1(k6_domain_1(sK1,sK2),sK1)
% 2.66/1.00      | X0 != k6_domain_1(sK1,sK2)
% 2.66/1.00      | X1 != sK1 ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_713]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1163,plain,
% 2.66/1.00      ( ~ v1_subset_1(k6_domain_1(sK1,sK2),sK1)
% 2.66/1.00      | v1_subset_1(sK1,sK1)
% 2.66/1.00      | sK1 != k6_domain_1(sK1,sK2)
% 2.66/1.00      | sK1 != sK1 ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_1161]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1268,plain,
% 2.66/1.00      ( ~ m1_subset_1(k6_domain_1(sK1,sK2),k1_zfmisc_1(sK1))
% 2.66/1.00      | v1_xboole_0(k6_domain_1(sK1,sK2))
% 2.66/1.00      | sK1 = k6_domain_1(sK1,sK2) ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_395]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1271,plain,
% 2.66/1.00      ( sK1 = k6_domain_1(sK1,sK2)
% 2.66/1.00      | m1_subset_1(k6_domain_1(sK1,sK2),k1_zfmisc_1(sK1)) != iProver_top
% 2.66/1.00      | v1_xboole_0(k6_domain_1(sK1,sK2)) = iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_1268]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_705,plain,( X0 = X0 ),theory(equality) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1480,plain,
% 2.66/1.00      ( k2_tarski(X0,X0) = k2_tarski(X0,X0) ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_705]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1693,plain,
% 2.66/1.00      ( k2_tarski(sK2,sK2) = k2_tarski(sK2,sK2) ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_1480]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_706,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1248,plain,
% 2.66/1.00      ( X0 != X1 | X0 = k6_domain_1(sK1,sK2) | k6_domain_1(sK1,sK2) != X1 ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_706]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1527,plain,
% 2.66/1.00      ( X0 = k6_domain_1(sK1,sK2)
% 2.66/1.00      | X0 != k2_tarski(sK2,sK2)
% 2.66/1.00      | k6_domain_1(sK1,sK2) != k2_tarski(sK2,sK2) ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_1248]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1694,plain,
% 2.66/1.00      ( k6_domain_1(sK1,sK2) != k2_tarski(sK2,sK2)
% 2.66/1.00      | k2_tarski(sK2,sK2) = k6_domain_1(sK1,sK2)
% 2.66/1.00      | k2_tarski(sK2,sK2) != k2_tarski(sK2,sK2) ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_1527]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_707,plain,
% 2.66/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.66/1.00      theory(equality) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1306,plain,
% 2.66/1.00      ( v1_xboole_0(X0)
% 2.66/1.00      | ~ v1_xboole_0(k6_domain_1(sK1,sK2))
% 2.66/1.00      | X0 != k6_domain_1(sK1,sK2) ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_707]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2078,plain,
% 2.66/1.00      ( ~ v1_xboole_0(k6_domain_1(sK1,sK2))
% 2.66/1.00      | v1_xboole_0(k2_tarski(sK2,sK2))
% 2.66/1.00      | k2_tarski(sK2,sK2) != k6_domain_1(sK1,sK2) ),
% 2.66/1.00      inference(instantiation,[status(thm)],[c_1306]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2084,plain,
% 2.66/1.00      ( k2_tarski(sK2,sK2) != k6_domain_1(sK1,sK2)
% 2.66/1.00      | v1_xboole_0(k6_domain_1(sK1,sK2)) != iProver_top
% 2.66/1.00      | v1_xboole_0(k2_tarski(sK2,sK2)) = iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_2078]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2636,plain,
% 2.66/1.00      ( v1_xboole_0(k2_tarski(sK2,sK2)) = iProver_top ),
% 2.66/1.00      inference(global_propositional_subsumption,
% 2.66/1.00                [status(thm)],
% 2.66/1.00                [c_2409,c_21,c_22,c_20,c_23,c_19,c_58,c_61,c_1102,c_1136,
% 2.66/1.00                 c_1143,c_1163,c_1271,c_1693,c_1694,c_2084]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_0,plain,
% 2.66/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.66/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1020,plain,
% 2.66/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2,plain,
% 2.66/1.00      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 2.66/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1019,plain,
% 2.66/1.00      ( X0 = X1
% 2.66/1.00      | v1_xboole_0(X0) != iProver_top
% 2.66/1.00      | v1_xboole_0(X1) != iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1626,plain,
% 2.66/1.00      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_1020,c_1019]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2642,plain,
% 2.66/1.00      ( k2_tarski(sK2,sK2) = k1_xboole_0 ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_2636,c_1626]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1016,plain,
% 2.66/1.00      ( r2_hidden(X0,k2_tarski(X0,X0)) = iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_2866,plain,
% 2.66/1.00      ( r2_hidden(sK2,k1_xboole_0) = iProver_top ),
% 2.66/1.00      inference(superposition,[status(thm)],[c_2642,c_1016]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1,plain,
% 2.66/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 2.66/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_9,plain,
% 2.66/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 2.66/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_371,plain,
% 2.66/1.00      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 2.66/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_9]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_372,plain,
% 2.66/1.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.66/1.00      inference(unflattening,[status(thm)],[c_371]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_1007,plain,
% 2.66/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.66/1.00      inference(predicate_to_equality,[status(thm)],[c_372]) ).
% 2.66/1.00  
% 2.66/1.00  cnf(c_3150,plain,
% 2.66/1.00      ( $false ),
% 2.66/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_2866,c_1007]) ).
% 2.66/1.00  
% 2.66/1.00  
% 2.66/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.66/1.00  
% 2.66/1.00  ------                               Statistics
% 2.66/1.00  
% 2.66/1.00  ------ General
% 2.66/1.00  
% 2.66/1.00  abstr_ref_over_cycles:                  0
% 2.66/1.00  abstr_ref_under_cycles:                 0
% 2.66/1.00  gc_basic_clause_elim:                   0
% 2.66/1.00  forced_gc_time:                         0
% 2.66/1.00  parsing_time:                           0.007
% 2.66/1.00  unif_index_cands_time:                  0.
% 2.66/1.00  unif_index_add_time:                    0.
% 2.66/1.00  orderings_time:                         0.
% 2.66/1.00  out_proof_time:                         0.006
% 2.66/1.00  total_time:                             0.119
% 2.66/1.00  num_of_symbols:                         49
% 2.66/1.00  num_of_terms:                           2716
% 2.66/1.00  
% 2.66/1.00  ------ Preprocessing
% 2.66/1.00  
% 2.66/1.00  num_of_splits:                          0
% 2.66/1.00  num_of_split_atoms:                     0
% 2.66/1.00  num_of_reused_defs:                     0
% 2.66/1.00  num_eq_ax_congr_red:                    19
% 2.66/1.00  num_of_sem_filtered_clauses:            1
% 2.66/1.00  num_of_subtypes:                        0
% 2.66/1.00  monotx_restored_types:                  0
% 2.66/1.00  sat_num_of_epr_types:                   0
% 2.66/1.00  sat_num_of_non_cyclic_types:            0
% 2.66/1.00  sat_guarded_non_collapsed_types:        0
% 2.66/1.00  num_pure_diseq_elim:                    0
% 2.66/1.00  simp_replaced_by:                       0
% 2.66/1.00  res_preprocessed:                       97
% 2.66/1.00  prep_upred:                             0
% 2.66/1.00  prep_unflattend:                        36
% 2.66/1.00  smt_new_axioms:                         0
% 2.66/1.00  pred_elim_cands:                        4
% 2.66/1.00  pred_elim:                              4
% 2.66/1.00  pred_elim_cl:                           4
% 2.66/1.00  pred_elim_cycles:                       9
% 2.66/1.00  merged_defs:                            2
% 2.66/1.00  merged_defs_ncl:                        0
% 2.66/1.00  bin_hyper_res:                          2
% 2.66/1.00  prep_cycles:                            4
% 2.66/1.00  pred_elim_time:                         0.005
% 2.66/1.00  splitting_time:                         0.
% 2.66/1.00  sem_filter_time:                        0.
% 2.66/1.00  monotx_time:                            0.001
% 2.66/1.00  subtype_inf_time:                       0.
% 2.66/1.00  
% 2.66/1.00  ------ Problem properties
% 2.66/1.00  
% 2.66/1.00  clauses:                                18
% 2.66/1.00  conjectures:                            3
% 2.66/1.00  epr:                                    5
% 2.66/1.00  horn:                                   14
% 2.66/1.00  ground:                                 4
% 2.66/1.00  unary:                                  10
% 2.66/1.00  binary:                                 2
% 2.66/1.00  lits:                                   32
% 2.66/1.00  lits_eq:                                10
% 2.66/1.00  fd_pure:                                0
% 2.66/1.00  fd_pseudo:                              0
% 2.66/1.00  fd_cond:                                1
% 2.66/1.00  fd_pseudo_cond:                         3
% 2.66/1.00  ac_symbols:                             0
% 2.66/1.00  
% 2.66/1.00  ------ Propositional Solver
% 2.66/1.00  
% 2.66/1.00  prop_solver_calls:                      26
% 2.66/1.00  prop_fast_solver_calls:                 520
% 2.66/1.00  smt_solver_calls:                       0
% 2.66/1.00  smt_fast_solver_calls:                  0
% 2.66/1.00  prop_num_of_clauses:                    1155
% 2.66/1.00  prop_preprocess_simplified:             4430
% 2.66/1.00  prop_fo_subsumed:                       10
% 2.66/1.00  prop_solver_time:                       0.
% 2.66/1.00  smt_solver_time:                        0.
% 2.66/1.00  smt_fast_solver_time:                   0.
% 2.66/1.00  prop_fast_solver_time:                  0.
% 2.66/1.00  prop_unsat_core_time:                   0.
% 2.66/1.00  
% 2.66/1.00  ------ QBF
% 2.66/1.00  
% 2.66/1.00  qbf_q_res:                              0
% 2.66/1.00  qbf_num_tautologies:                    0
% 2.66/1.00  qbf_prep_cycles:                        0
% 2.66/1.00  
% 2.66/1.00  ------ BMC1
% 2.66/1.00  
% 2.66/1.00  bmc1_current_bound:                     -1
% 2.66/1.00  bmc1_last_solved_bound:                 -1
% 2.66/1.00  bmc1_unsat_core_size:                   -1
% 2.66/1.00  bmc1_unsat_core_parents_size:           -1
% 2.66/1.00  bmc1_merge_next_fun:                    0
% 2.66/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.66/1.00  
% 2.66/1.00  ------ Instantiation
% 2.66/1.00  
% 2.66/1.00  inst_num_of_clauses:                    377
% 2.66/1.00  inst_num_in_passive:                    118
% 2.66/1.00  inst_num_in_active:                     153
% 2.66/1.00  inst_num_in_unprocessed:                106
% 2.66/1.00  inst_num_of_loops:                      170
% 2.66/1.00  inst_num_of_learning_restarts:          0
% 2.66/1.00  inst_num_moves_active_passive:          15
% 2.66/1.00  inst_lit_activity:                      0
% 2.66/1.00  inst_lit_activity_moves:                0
% 2.66/1.00  inst_num_tautologies:                   0
% 2.66/1.00  inst_num_prop_implied:                  0
% 2.66/1.00  inst_num_existing_simplified:           0
% 2.66/1.00  inst_num_eq_res_simplified:             0
% 2.66/1.00  inst_num_child_elim:                    0
% 2.66/1.00  inst_num_of_dismatching_blockings:      60
% 2.66/1.00  inst_num_of_non_proper_insts:           239
% 2.66/1.00  inst_num_of_duplicates:                 0
% 2.66/1.00  inst_inst_num_from_inst_to_res:         0
% 2.66/1.00  inst_dismatching_checking_time:         0.
% 2.66/1.00  
% 2.66/1.00  ------ Resolution
% 2.66/1.00  
% 2.66/1.00  res_num_of_clauses:                     0
% 2.66/1.00  res_num_in_passive:                     0
% 2.66/1.00  res_num_in_active:                      0
% 2.66/1.00  res_num_of_loops:                       101
% 2.66/1.00  res_forward_subset_subsumed:            30
% 2.66/1.00  res_backward_subset_subsumed:           0
% 2.66/1.00  res_forward_subsumed:                   0
% 2.66/1.00  res_backward_subsumed:                  0
% 2.66/1.00  res_forward_subsumption_resolution:     0
% 2.66/1.00  res_backward_subsumption_resolution:    1
% 2.66/1.00  res_clause_to_clause_subsumption:       73
% 2.66/1.00  res_orphan_elimination:                 0
% 2.66/1.00  res_tautology_del:                      28
% 2.66/1.00  res_num_eq_res_simplified:              0
% 2.66/1.00  res_num_sel_changes:                    0
% 2.66/1.00  res_moves_from_active_to_pass:          0
% 2.66/1.00  
% 2.66/1.00  ------ Superposition
% 2.66/1.00  
% 2.66/1.00  sup_time_total:                         0.
% 2.66/1.00  sup_time_generating:                    0.
% 2.66/1.00  sup_time_sim_full:                      0.
% 2.66/1.00  sup_time_sim_immed:                     0.
% 2.66/1.00  
% 2.66/1.00  sup_num_of_clauses:                     41
% 2.66/1.00  sup_num_in_active:                      25
% 2.66/1.00  sup_num_in_passive:                     16
% 2.66/1.00  sup_num_of_loops:                       32
% 2.66/1.00  sup_fw_superposition:                   9
% 2.66/1.00  sup_bw_superposition:                   25
% 2.66/1.00  sup_immediate_simplified:               8
% 2.66/1.00  sup_given_eliminated:                   1
% 2.66/1.00  comparisons_done:                       0
% 2.66/1.00  comparisons_avoided:                    3
% 2.66/1.00  
% 2.66/1.00  ------ Simplifications
% 2.66/1.00  
% 2.66/1.00  
% 2.66/1.00  sim_fw_subset_subsumed:                 3
% 2.66/1.00  sim_bw_subset_subsumed:                 0
% 2.66/1.00  sim_fw_subsumed:                        4
% 2.66/1.00  sim_bw_subsumed:                        0
% 2.66/1.00  sim_fw_subsumption_res:                 1
% 2.66/1.00  sim_bw_subsumption_res:                 0
% 2.66/1.00  sim_tautology_del:                      0
% 2.66/1.00  sim_eq_tautology_del:                   2
% 2.66/1.00  sim_eq_res_simp:                        0
% 2.66/1.00  sim_fw_demodulated:                     1
% 2.66/1.00  sim_bw_demodulated:                     8
% 2.66/1.00  sim_light_normalised:                   3
% 2.66/1.00  sim_joinable_taut:                      0
% 2.66/1.00  sim_joinable_simp:                      0
% 2.66/1.00  sim_ac_normalised:                      0
% 2.66/1.00  sim_smt_subsumption:                    0
% 2.66/1.00  
%------------------------------------------------------------------------------
