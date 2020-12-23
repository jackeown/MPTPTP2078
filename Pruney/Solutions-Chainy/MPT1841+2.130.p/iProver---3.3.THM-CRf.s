%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:14 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 286 expanded)
%              Number of clauses        :   75 (  93 expanded)
%              Number of leaves         :   19 (  66 expanded)
%              Depth                    :   14
%              Number of atoms          :  371 ( 914 expanded)
%              Number of equality atoms :  129 ( 221 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
     => ( v1_zfmisc_1(X0)
        & v1_subset_1(k6_domain_1(X0,sK2),X0)
        & m1_subset_1(sK2,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
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

fof(f38,plain,
    ( v1_zfmisc_1(sK1)
    & v1_subset_1(k6_domain_1(sK1,sK2),sK1)
    & m1_subset_1(sK2,sK1)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f28,f37,f36])).

fof(f60,plain,(
    m1_subset_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f54,f46])).

fof(f59,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f62,plain,(
    v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f61,plain,(
    v1_subset_1(k6_domain_1(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f42,f46])).

fof(f72,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_tarski(X0,X0)) ) ),
    inference(equality_resolution,[],[f66])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f43,f46])).

fof(f70,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f65])).

fof(f71,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f70])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f69,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f55,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f12,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1255,plain,
    ( m1_subset_1(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1257,plain,
    ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2035,plain,
    ( k6_domain_1(sK1,sK2) = k2_tarski(sK2,sK2)
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1255,c_1257])).

cnf(c_21,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1396,plain,
    ( ~ m1_subset_1(sK2,sK1)
    | v1_xboole_0(sK1)
    | k6_domain_1(sK1,sK2) = k2_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2380,plain,
    ( k6_domain_1(sK1,sK2) = k2_tarski(sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2035,c_21,c_20,c_1396])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1258,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1259,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2191,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r1_tarski(k6_domain_1(X1,X0),X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1258,c_1259])).

cnf(c_2683,plain,
    ( m1_subset_1(sK2,sK1) != iProver_top
    | r1_tarski(k2_tarski(sK2,sK2),sK1) = iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2380,c_2191])).

cnf(c_22,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_23,plain,
    ( m1_subset_1(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2716,plain,
    ( r1_tarski(k2_tarski(sK2,sK2),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2683,c_22,c_23])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_18,negated_conjecture,
    ( v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_331,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | X1 = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_18])).

cnf(c_332,plain,
    ( ~ r1_tarski(X0,sK1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | sK1 = X0 ),
    inference(unflattening,[status(thm)],[c_331])).

cnf(c_334,plain,
    ( v1_xboole_0(X0)
    | ~ r1_tarski(X0,sK1)
    | sK1 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_332,c_21])).

cnf(c_335,plain,
    ( ~ r1_tarski(X0,sK1)
    | v1_xboole_0(X0)
    | sK1 = X0 ),
    inference(renaming,[status(thm)],[c_334])).

cnf(c_1251,plain,
    ( sK1 = X0
    | r1_tarski(X0,sK1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_335])).

cnf(c_2722,plain,
    ( k2_tarski(sK2,sK2) = sK1
    | v1_xboole_0(k2_tarski(sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2716,c_1251])).

cnf(c_19,negated_conjecture,
    ( v1_subset_1(k6_domain_1(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_56,plain,
    ( ~ r2_hidden(sK1,k2_tarski(sK1,sK1))
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( r2_hidden(X0,k2_tarski(X0,X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_59,plain,
    ( r2_hidden(sK1,k2_tarski(sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_68,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_11,plain,
    ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_13,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_15,plain,
    ( l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_292,plain,
    ( l1_struct_0(X0)
    | k2_yellow_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_15])).

cnf(c_293,plain,
    ( l1_struct_0(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_292])).

cnf(c_303,plain,
    ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
    | k2_yellow_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_293])).

cnf(c_304,plain,
    ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(X0)),u1_struct_0(k2_yellow_1(X0))) ),
    inference(unflattening,[status(thm)],[c_303])).

cnf(c_1252,plain,
    ( v1_subset_1(k2_struct_0(k2_yellow_1(X0)),u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_304])).

cnf(c_16,plain,
    ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_10,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_312,plain,
    ( k2_yellow_1(X0) != X1
    | u1_struct_0(X1) = k2_struct_0(X1) ),
    inference(resolution_lifted,[status(thm)],[c_10,c_293])).

cnf(c_313,plain,
    ( u1_struct_0(k2_yellow_1(X0)) = k2_struct_0(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_312])).

cnf(c_1275,plain,
    ( k2_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_313,c_16])).

cnf(c_1282,plain,
    ( v1_subset_1(X0,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1252,c_16,c_1275])).

cnf(c_1352,plain,
    ( ~ v1_subset_1(X0,X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1282])).

cnf(c_1354,plain,
    ( ~ v1_subset_1(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_1352])).

cnf(c_1384,plain,
    ( m1_subset_1(k6_domain_1(sK1,sK2),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,sK1)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_837,plain,
    ( ~ v1_subset_1(X0,X1)
    | v1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1409,plain,
    ( v1_subset_1(X0,X1)
    | ~ v1_subset_1(k6_domain_1(sK1,sK2),sK1)
    | X0 != k6_domain_1(sK1,sK2)
    | X1 != sK1 ),
    inference(instantiation,[status(thm)],[c_837])).

cnf(c_1411,plain,
    ( ~ v1_subset_1(k6_domain_1(sK1,sK2),sK1)
    | v1_subset_1(sK1,sK1)
    | sK1 != k6_domain_1(sK1,sK2)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1409])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1471,plain,
    ( ~ r1_tarski(X0,k6_domain_1(sK1,sK2))
    | ~ r1_tarski(k6_domain_1(sK1,sK2),X0)
    | X0 = k6_domain_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1478,plain,
    ( ~ r1_tarski(k6_domain_1(sK1,sK2),sK1)
    | ~ r1_tarski(sK1,k6_domain_1(sK1,sK2))
    | sK1 = k6_domain_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1471])).

cnf(c_1543,plain,
    ( ~ m1_subset_1(k6_domain_1(sK1,sK2),k1_zfmisc_1(sK1))
    | r1_tarski(k6_domain_1(sK1,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_831,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,X2)
    | X2 != X1 ),
    theory(equality)).

cnf(c_1613,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k6_domain_1(sK1,sK2))
    | k6_domain_1(sK1,sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_831])).

cnf(c_2091,plain,
    ( r1_tarski(X0,k6_domain_1(sK1,sK2))
    | ~ r1_tarski(X0,k2_tarski(sK2,sK2))
    | k6_domain_1(sK1,sK2) != k2_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1613])).

cnf(c_2093,plain,
    ( r1_tarski(sK1,k6_domain_1(sK1,sK2))
    | ~ r1_tarski(sK1,k2_tarski(sK2,sK2))
    | k6_domain_1(sK1,sK2) != k2_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2091])).

cnf(c_2785,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_tarski(sK2,sK2))
    | k2_tarski(sK2,sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_831])).

cnf(c_2787,plain,
    ( r1_tarski(sK1,k2_tarski(sK2,sK2))
    | ~ r1_tarski(sK1,sK1)
    | k2_tarski(sK2,sK2) != sK1 ),
    inference(instantiation,[status(thm)],[c_2785])).

cnf(c_2837,plain,
    ( v1_xboole_0(k2_tarski(sK2,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2722,c_21,c_20,c_19,c_56,c_59,c_68,c_1354,c_1384,c_1396,c_1411,c_1478,c_1543,c_2093,c_2787])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1265,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1262,plain,
    ( r2_hidden(X0,k2_tarski(X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_165,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_166,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_165])).

cnf(c_203,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_166])).

cnf(c_1253,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_203])).

cnf(c_1637,plain,
    ( r1_tarski(k2_tarski(X0,X0),X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1262,c_1253])).

cnf(c_1860,plain,
    ( v1_xboole_0(k2_tarski(X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1265,c_1637])).

cnf(c_2842,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2837,c_1860])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : iproveropt_run.sh %d %s
% 0.10/0.31  % Computer   : n015.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % WCLimit    : 600
% 0.10/0.31  % DateTime   : Tue Dec  1 19:11:38 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.10/0.32  % Running in FOF mode
% 2.17/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/0.97  
% 2.17/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.17/0.97  
% 2.17/0.97  ------  iProver source info
% 2.17/0.97  
% 2.17/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.17/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.17/0.97  git: non_committed_changes: false
% 2.17/0.97  git: last_make_outside_of_git: false
% 2.17/0.97  
% 2.17/0.97  ------ 
% 2.17/0.97  
% 2.17/0.97  ------ Input Options
% 2.17/0.97  
% 2.17/0.97  --out_options                           all
% 2.17/0.97  --tptp_safe_out                         true
% 2.17/0.97  --problem_path                          ""
% 2.17/0.97  --include_path                          ""
% 2.17/0.97  --clausifier                            res/vclausify_rel
% 2.17/0.97  --clausifier_options                    --mode clausify
% 2.17/0.97  --stdin                                 false
% 2.17/0.97  --stats_out                             all
% 2.17/0.97  
% 2.17/0.97  ------ General Options
% 2.17/0.97  
% 2.17/0.97  --fof                                   false
% 2.17/0.97  --time_out_real                         305.
% 2.17/0.97  --time_out_virtual                      -1.
% 2.17/0.97  --symbol_type_check                     false
% 2.17/0.97  --clausify_out                          false
% 2.17/0.97  --sig_cnt_out                           false
% 2.17/0.97  --trig_cnt_out                          false
% 2.17/0.97  --trig_cnt_out_tolerance                1.
% 2.17/0.97  --trig_cnt_out_sk_spl                   false
% 2.17/0.97  --abstr_cl_out                          false
% 2.17/0.97  
% 2.17/0.97  ------ Global Options
% 2.17/0.97  
% 2.17/0.97  --schedule                              default
% 2.17/0.97  --add_important_lit                     false
% 2.17/0.97  --prop_solver_per_cl                    1000
% 2.17/0.97  --min_unsat_core                        false
% 2.17/0.97  --soft_assumptions                      false
% 2.17/0.97  --soft_lemma_size                       3
% 2.17/0.97  --prop_impl_unit_size                   0
% 2.17/0.97  --prop_impl_unit                        []
% 2.17/0.97  --share_sel_clauses                     true
% 2.17/0.97  --reset_solvers                         false
% 2.17/0.97  --bc_imp_inh                            [conj_cone]
% 2.17/0.97  --conj_cone_tolerance                   3.
% 2.17/0.97  --extra_neg_conj                        none
% 2.17/0.97  --large_theory_mode                     true
% 2.17/0.97  --prolific_symb_bound                   200
% 2.17/0.97  --lt_threshold                          2000
% 2.17/0.97  --clause_weak_htbl                      true
% 2.17/0.97  --gc_record_bc_elim                     false
% 2.17/0.97  
% 2.17/0.97  ------ Preprocessing Options
% 2.17/0.97  
% 2.17/0.97  --preprocessing_flag                    true
% 2.17/0.97  --time_out_prep_mult                    0.1
% 2.17/0.97  --splitting_mode                        input
% 2.17/0.97  --splitting_grd                         true
% 2.17/0.97  --splitting_cvd                         false
% 2.17/0.97  --splitting_cvd_svl                     false
% 2.17/0.97  --splitting_nvd                         32
% 2.17/0.97  --sub_typing                            true
% 2.17/0.97  --prep_gs_sim                           true
% 2.17/0.97  --prep_unflatten                        true
% 2.17/0.97  --prep_res_sim                          true
% 2.17/0.97  --prep_upred                            true
% 2.17/0.97  --prep_sem_filter                       exhaustive
% 2.17/0.97  --prep_sem_filter_out                   false
% 2.17/0.97  --pred_elim                             true
% 2.17/0.97  --res_sim_input                         true
% 2.17/0.97  --eq_ax_congr_red                       true
% 2.17/0.97  --pure_diseq_elim                       true
% 2.17/0.97  --brand_transform                       false
% 2.17/0.97  --non_eq_to_eq                          false
% 2.17/0.97  --prep_def_merge                        true
% 2.17/0.97  --prep_def_merge_prop_impl              false
% 2.17/0.97  --prep_def_merge_mbd                    true
% 2.17/0.97  --prep_def_merge_tr_red                 false
% 2.17/0.97  --prep_def_merge_tr_cl                  false
% 2.17/0.97  --smt_preprocessing                     true
% 2.17/0.97  --smt_ac_axioms                         fast
% 2.17/0.97  --preprocessed_out                      false
% 2.17/0.97  --preprocessed_stats                    false
% 2.17/0.97  
% 2.17/0.97  ------ Abstraction refinement Options
% 2.17/0.97  
% 2.17/0.97  --abstr_ref                             []
% 2.17/0.97  --abstr_ref_prep                        false
% 2.17/0.97  --abstr_ref_until_sat                   false
% 2.17/0.97  --abstr_ref_sig_restrict                funpre
% 2.17/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.17/0.97  --abstr_ref_under                       []
% 2.17/0.97  
% 2.17/0.97  ------ SAT Options
% 2.17/0.97  
% 2.17/0.97  --sat_mode                              false
% 2.17/0.97  --sat_fm_restart_options                ""
% 2.17/0.97  --sat_gr_def                            false
% 2.17/0.97  --sat_epr_types                         true
% 2.17/0.97  --sat_non_cyclic_types                  false
% 2.17/0.97  --sat_finite_models                     false
% 2.17/0.97  --sat_fm_lemmas                         false
% 2.17/0.97  --sat_fm_prep                           false
% 2.17/0.97  --sat_fm_uc_incr                        true
% 2.17/0.97  --sat_out_model                         small
% 2.17/0.97  --sat_out_clauses                       false
% 2.17/0.97  
% 2.17/0.97  ------ QBF Options
% 2.17/0.97  
% 2.17/0.97  --qbf_mode                              false
% 2.17/0.97  --qbf_elim_univ                         false
% 2.17/0.97  --qbf_dom_inst                          none
% 2.17/0.97  --qbf_dom_pre_inst                      false
% 2.17/0.97  --qbf_sk_in                             false
% 2.17/0.97  --qbf_pred_elim                         true
% 2.17/0.97  --qbf_split                             512
% 2.17/0.97  
% 2.17/0.97  ------ BMC1 Options
% 2.17/0.97  
% 2.17/0.97  --bmc1_incremental                      false
% 2.17/0.97  --bmc1_axioms                           reachable_all
% 2.17/0.97  --bmc1_min_bound                        0
% 2.17/0.97  --bmc1_max_bound                        -1
% 2.17/0.97  --bmc1_max_bound_default                -1
% 2.17/0.97  --bmc1_symbol_reachability              true
% 2.17/0.97  --bmc1_property_lemmas                  false
% 2.17/0.97  --bmc1_k_induction                      false
% 2.17/0.97  --bmc1_non_equiv_states                 false
% 2.17/0.97  --bmc1_deadlock                         false
% 2.17/0.97  --bmc1_ucm                              false
% 2.17/0.97  --bmc1_add_unsat_core                   none
% 2.17/0.97  --bmc1_unsat_core_children              false
% 2.17/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.17/0.97  --bmc1_out_stat                         full
% 2.17/0.97  --bmc1_ground_init                      false
% 2.17/0.97  --bmc1_pre_inst_next_state              false
% 2.17/0.97  --bmc1_pre_inst_state                   false
% 2.17/0.97  --bmc1_pre_inst_reach_state             false
% 2.17/0.97  --bmc1_out_unsat_core                   false
% 2.17/0.97  --bmc1_aig_witness_out                  false
% 2.17/0.97  --bmc1_verbose                          false
% 2.17/0.97  --bmc1_dump_clauses_tptp                false
% 2.17/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.17/0.97  --bmc1_dump_file                        -
% 2.17/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.17/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.17/0.97  --bmc1_ucm_extend_mode                  1
% 2.17/0.97  --bmc1_ucm_init_mode                    2
% 2.17/0.97  --bmc1_ucm_cone_mode                    none
% 2.17/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.17/0.97  --bmc1_ucm_relax_model                  4
% 2.17/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.17/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.17/0.97  --bmc1_ucm_layered_model                none
% 2.17/0.97  --bmc1_ucm_max_lemma_size               10
% 2.17/0.97  
% 2.17/0.97  ------ AIG Options
% 2.17/0.97  
% 2.17/0.97  --aig_mode                              false
% 2.17/0.97  
% 2.17/0.97  ------ Instantiation Options
% 2.17/0.97  
% 2.17/0.97  --instantiation_flag                    true
% 2.17/0.97  --inst_sos_flag                         false
% 2.17/0.97  --inst_sos_phase                        true
% 2.17/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.17/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.17/0.97  --inst_lit_sel_side                     num_symb
% 2.17/0.97  --inst_solver_per_active                1400
% 2.17/0.97  --inst_solver_calls_frac                1.
% 2.17/0.97  --inst_passive_queue_type               priority_queues
% 2.17/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.17/0.97  --inst_passive_queues_freq              [25;2]
% 2.17/0.97  --inst_dismatching                      true
% 2.17/0.97  --inst_eager_unprocessed_to_passive     true
% 2.17/0.97  --inst_prop_sim_given                   true
% 2.17/0.97  --inst_prop_sim_new                     false
% 2.17/0.97  --inst_subs_new                         false
% 2.17/0.97  --inst_eq_res_simp                      false
% 2.17/0.97  --inst_subs_given                       false
% 2.17/0.97  --inst_orphan_elimination               true
% 2.17/0.97  --inst_learning_loop_flag               true
% 2.17/0.97  --inst_learning_start                   3000
% 2.17/0.97  --inst_learning_factor                  2
% 2.17/0.97  --inst_start_prop_sim_after_learn       3
% 2.17/0.97  --inst_sel_renew                        solver
% 2.17/0.97  --inst_lit_activity_flag                true
% 2.17/0.97  --inst_restr_to_given                   false
% 2.17/0.97  --inst_activity_threshold               500
% 2.17/0.97  --inst_out_proof                        true
% 2.17/0.97  
% 2.17/0.97  ------ Resolution Options
% 2.17/0.97  
% 2.17/0.97  --resolution_flag                       true
% 2.17/0.97  --res_lit_sel                           adaptive
% 2.17/0.97  --res_lit_sel_side                      none
% 2.17/0.97  --res_ordering                          kbo
% 2.17/0.97  --res_to_prop_solver                    active
% 2.17/0.97  --res_prop_simpl_new                    false
% 2.17/0.97  --res_prop_simpl_given                  true
% 2.17/0.97  --res_passive_queue_type                priority_queues
% 2.17/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.17/0.97  --res_passive_queues_freq               [15;5]
% 2.17/0.97  --res_forward_subs                      full
% 2.17/0.97  --res_backward_subs                     full
% 2.17/0.97  --res_forward_subs_resolution           true
% 2.17/0.97  --res_backward_subs_resolution          true
% 2.17/0.97  --res_orphan_elimination                true
% 2.17/0.97  --res_time_limit                        2.
% 2.17/0.97  --res_out_proof                         true
% 2.17/0.97  
% 2.17/0.97  ------ Superposition Options
% 2.17/0.97  
% 2.17/0.97  --superposition_flag                    true
% 2.17/0.97  --sup_passive_queue_type                priority_queues
% 2.17/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.17/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.17/0.97  --demod_completeness_check              fast
% 2.17/0.97  --demod_use_ground                      true
% 2.17/0.97  --sup_to_prop_solver                    passive
% 2.17/0.97  --sup_prop_simpl_new                    true
% 2.17/0.97  --sup_prop_simpl_given                  true
% 2.17/0.97  --sup_fun_splitting                     false
% 2.17/0.97  --sup_smt_interval                      50000
% 2.17/0.97  
% 2.17/0.97  ------ Superposition Simplification Setup
% 2.17/0.97  
% 2.17/0.97  --sup_indices_passive                   []
% 2.17/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.17/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.97  --sup_full_bw                           [BwDemod]
% 2.17/0.97  --sup_immed_triv                        [TrivRules]
% 2.17/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.17/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.97  --sup_immed_bw_main                     []
% 2.17/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.17/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/0.97  
% 2.17/0.97  ------ Combination Options
% 2.17/0.97  
% 2.17/0.97  --comb_res_mult                         3
% 2.17/0.97  --comb_sup_mult                         2
% 2.17/0.97  --comb_inst_mult                        10
% 2.17/0.97  
% 2.17/0.97  ------ Debug Options
% 2.17/0.97  
% 2.17/0.97  --dbg_backtrace                         false
% 2.17/0.97  --dbg_dump_prop_clauses                 false
% 2.17/0.97  --dbg_dump_prop_clauses_file            -
% 2.17/0.97  --dbg_out_stat                          false
% 2.17/0.97  ------ Parsing...
% 2.17/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.17/0.97  
% 2.17/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.17/0.97  
% 2.17/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.17/0.97  
% 2.17/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.17/0.97  ------ Proving...
% 2.17/0.97  ------ Problem Properties 
% 2.17/0.97  
% 2.17/0.97  
% 2.17/0.97  clauses                                 18
% 2.17/0.97  conjectures                             3
% 2.17/0.97  EPR                                     6
% 2.17/0.97  Horn                                    14
% 2.17/0.97  unary                                   8
% 2.17/0.97  binary                                  3
% 2.17/0.97  lits                                    35
% 2.17/0.97  lits eq                                 10
% 2.17/0.97  fd_pure                                 0
% 2.17/0.97  fd_pseudo                               0
% 2.17/0.97  fd_cond                                 1
% 2.17/0.97  fd_pseudo_cond                          3
% 2.17/0.97  AC symbols                              0
% 2.17/0.97  
% 2.17/0.97  ------ Schedule dynamic 5 is on 
% 2.17/0.97  
% 2.17/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.17/0.97  
% 2.17/0.97  
% 2.17/0.97  ------ 
% 2.17/0.97  Current options:
% 2.17/0.97  ------ 
% 2.17/0.97  
% 2.17/0.97  ------ Input Options
% 2.17/0.97  
% 2.17/0.97  --out_options                           all
% 2.17/0.97  --tptp_safe_out                         true
% 2.17/0.97  --problem_path                          ""
% 2.17/0.97  --include_path                          ""
% 2.17/0.97  --clausifier                            res/vclausify_rel
% 2.17/0.97  --clausifier_options                    --mode clausify
% 2.17/0.97  --stdin                                 false
% 2.17/0.97  --stats_out                             all
% 2.17/0.97  
% 2.17/0.97  ------ General Options
% 2.17/0.97  
% 2.17/0.97  --fof                                   false
% 2.17/0.97  --time_out_real                         305.
% 2.17/0.97  --time_out_virtual                      -1.
% 2.17/0.97  --symbol_type_check                     false
% 2.17/0.97  --clausify_out                          false
% 2.17/0.97  --sig_cnt_out                           false
% 2.17/0.97  --trig_cnt_out                          false
% 2.17/0.97  --trig_cnt_out_tolerance                1.
% 2.17/0.97  --trig_cnt_out_sk_spl                   false
% 2.17/0.97  --abstr_cl_out                          false
% 2.17/0.97  
% 2.17/0.97  ------ Global Options
% 2.17/0.97  
% 2.17/0.97  --schedule                              default
% 2.17/0.97  --add_important_lit                     false
% 2.17/0.97  --prop_solver_per_cl                    1000
% 2.17/0.97  --min_unsat_core                        false
% 2.17/0.97  --soft_assumptions                      false
% 2.17/0.97  --soft_lemma_size                       3
% 2.17/0.97  --prop_impl_unit_size                   0
% 2.17/0.97  --prop_impl_unit                        []
% 2.17/0.97  --share_sel_clauses                     true
% 2.17/0.97  --reset_solvers                         false
% 2.17/0.97  --bc_imp_inh                            [conj_cone]
% 2.17/0.97  --conj_cone_tolerance                   3.
% 2.17/0.97  --extra_neg_conj                        none
% 2.17/0.97  --large_theory_mode                     true
% 2.17/0.97  --prolific_symb_bound                   200
% 2.17/0.97  --lt_threshold                          2000
% 2.17/0.97  --clause_weak_htbl                      true
% 2.17/0.97  --gc_record_bc_elim                     false
% 2.17/0.97  
% 2.17/0.97  ------ Preprocessing Options
% 2.17/0.97  
% 2.17/0.97  --preprocessing_flag                    true
% 2.17/0.97  --time_out_prep_mult                    0.1
% 2.17/0.97  --splitting_mode                        input
% 2.17/0.97  --splitting_grd                         true
% 2.17/0.97  --splitting_cvd                         false
% 2.17/0.97  --splitting_cvd_svl                     false
% 2.17/0.97  --splitting_nvd                         32
% 2.17/0.97  --sub_typing                            true
% 2.17/0.97  --prep_gs_sim                           true
% 2.17/0.97  --prep_unflatten                        true
% 2.17/0.97  --prep_res_sim                          true
% 2.17/0.97  --prep_upred                            true
% 2.17/0.97  --prep_sem_filter                       exhaustive
% 2.17/0.97  --prep_sem_filter_out                   false
% 2.17/0.97  --pred_elim                             true
% 2.17/0.97  --res_sim_input                         true
% 2.17/0.97  --eq_ax_congr_red                       true
% 2.17/0.97  --pure_diseq_elim                       true
% 2.17/0.97  --brand_transform                       false
% 2.17/0.97  --non_eq_to_eq                          false
% 2.17/0.97  --prep_def_merge                        true
% 2.17/0.97  --prep_def_merge_prop_impl              false
% 2.17/0.97  --prep_def_merge_mbd                    true
% 2.17/0.97  --prep_def_merge_tr_red                 false
% 2.17/0.97  --prep_def_merge_tr_cl                  false
% 2.17/0.97  --smt_preprocessing                     true
% 2.17/0.97  --smt_ac_axioms                         fast
% 2.17/0.97  --preprocessed_out                      false
% 2.17/0.97  --preprocessed_stats                    false
% 2.17/0.97  
% 2.17/0.97  ------ Abstraction refinement Options
% 2.17/0.97  
% 2.17/0.97  --abstr_ref                             []
% 2.17/0.97  --abstr_ref_prep                        false
% 2.17/0.97  --abstr_ref_until_sat                   false
% 2.17/0.97  --abstr_ref_sig_restrict                funpre
% 2.17/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.17/0.97  --abstr_ref_under                       []
% 2.17/0.97  
% 2.17/0.97  ------ SAT Options
% 2.17/0.97  
% 2.17/0.97  --sat_mode                              false
% 2.17/0.97  --sat_fm_restart_options                ""
% 2.17/0.97  --sat_gr_def                            false
% 2.17/0.97  --sat_epr_types                         true
% 2.17/0.97  --sat_non_cyclic_types                  false
% 2.17/0.97  --sat_finite_models                     false
% 2.17/0.97  --sat_fm_lemmas                         false
% 2.17/0.97  --sat_fm_prep                           false
% 2.17/0.97  --sat_fm_uc_incr                        true
% 2.17/0.97  --sat_out_model                         small
% 2.17/0.97  --sat_out_clauses                       false
% 2.17/0.97  
% 2.17/0.97  ------ QBF Options
% 2.17/0.97  
% 2.17/0.97  --qbf_mode                              false
% 2.17/0.97  --qbf_elim_univ                         false
% 2.17/0.97  --qbf_dom_inst                          none
% 2.17/0.97  --qbf_dom_pre_inst                      false
% 2.17/0.97  --qbf_sk_in                             false
% 2.17/0.97  --qbf_pred_elim                         true
% 2.17/0.97  --qbf_split                             512
% 2.17/0.97  
% 2.17/0.97  ------ BMC1 Options
% 2.17/0.97  
% 2.17/0.97  --bmc1_incremental                      false
% 2.17/0.97  --bmc1_axioms                           reachable_all
% 2.17/0.97  --bmc1_min_bound                        0
% 2.17/0.97  --bmc1_max_bound                        -1
% 2.17/0.97  --bmc1_max_bound_default                -1
% 2.17/0.97  --bmc1_symbol_reachability              true
% 2.17/0.97  --bmc1_property_lemmas                  false
% 2.17/0.97  --bmc1_k_induction                      false
% 2.17/0.97  --bmc1_non_equiv_states                 false
% 2.17/0.97  --bmc1_deadlock                         false
% 2.17/0.97  --bmc1_ucm                              false
% 2.17/0.97  --bmc1_add_unsat_core                   none
% 2.17/0.97  --bmc1_unsat_core_children              false
% 2.17/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.17/0.97  --bmc1_out_stat                         full
% 2.17/0.97  --bmc1_ground_init                      false
% 2.17/0.97  --bmc1_pre_inst_next_state              false
% 2.17/0.97  --bmc1_pre_inst_state                   false
% 2.17/0.97  --bmc1_pre_inst_reach_state             false
% 2.17/0.97  --bmc1_out_unsat_core                   false
% 2.17/0.97  --bmc1_aig_witness_out                  false
% 2.17/0.97  --bmc1_verbose                          false
% 2.17/0.97  --bmc1_dump_clauses_tptp                false
% 2.17/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.17/0.97  --bmc1_dump_file                        -
% 2.17/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.17/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.17/0.97  --bmc1_ucm_extend_mode                  1
% 2.17/0.97  --bmc1_ucm_init_mode                    2
% 2.17/0.97  --bmc1_ucm_cone_mode                    none
% 2.17/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.17/0.97  --bmc1_ucm_relax_model                  4
% 2.17/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.17/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.17/0.97  --bmc1_ucm_layered_model                none
% 2.17/0.97  --bmc1_ucm_max_lemma_size               10
% 2.17/0.97  
% 2.17/0.97  ------ AIG Options
% 2.17/0.97  
% 2.17/0.97  --aig_mode                              false
% 2.17/0.97  
% 2.17/0.97  ------ Instantiation Options
% 2.17/0.97  
% 2.17/0.97  --instantiation_flag                    true
% 2.17/0.97  --inst_sos_flag                         false
% 2.17/0.97  --inst_sos_phase                        true
% 2.17/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.17/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.17/0.97  --inst_lit_sel_side                     none
% 2.17/0.97  --inst_solver_per_active                1400
% 2.17/0.97  --inst_solver_calls_frac                1.
% 2.17/0.97  --inst_passive_queue_type               priority_queues
% 2.17/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.17/0.97  --inst_passive_queues_freq              [25;2]
% 2.17/0.97  --inst_dismatching                      true
% 2.17/0.97  --inst_eager_unprocessed_to_passive     true
% 2.17/0.97  --inst_prop_sim_given                   true
% 2.17/0.97  --inst_prop_sim_new                     false
% 2.17/0.97  --inst_subs_new                         false
% 2.17/0.97  --inst_eq_res_simp                      false
% 2.17/0.97  --inst_subs_given                       false
% 2.17/0.97  --inst_orphan_elimination               true
% 2.17/0.97  --inst_learning_loop_flag               true
% 2.17/0.97  --inst_learning_start                   3000
% 2.17/0.97  --inst_learning_factor                  2
% 2.17/0.97  --inst_start_prop_sim_after_learn       3
% 2.17/0.97  --inst_sel_renew                        solver
% 2.17/0.97  --inst_lit_activity_flag                true
% 2.17/0.97  --inst_restr_to_given                   false
% 2.17/0.97  --inst_activity_threshold               500
% 2.17/0.97  --inst_out_proof                        true
% 2.17/0.97  
% 2.17/0.97  ------ Resolution Options
% 2.17/0.97  
% 2.17/0.97  --resolution_flag                       false
% 2.17/0.97  --res_lit_sel                           adaptive
% 2.17/0.97  --res_lit_sel_side                      none
% 2.17/0.97  --res_ordering                          kbo
% 2.17/0.97  --res_to_prop_solver                    active
% 2.17/0.97  --res_prop_simpl_new                    false
% 2.17/0.97  --res_prop_simpl_given                  true
% 2.17/0.97  --res_passive_queue_type                priority_queues
% 2.17/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.17/0.97  --res_passive_queues_freq               [15;5]
% 2.17/0.97  --res_forward_subs                      full
% 2.17/0.97  --res_backward_subs                     full
% 2.17/0.97  --res_forward_subs_resolution           true
% 2.17/0.97  --res_backward_subs_resolution          true
% 2.17/0.97  --res_orphan_elimination                true
% 2.17/0.97  --res_time_limit                        2.
% 2.17/0.97  --res_out_proof                         true
% 2.17/0.97  
% 2.17/0.97  ------ Superposition Options
% 2.17/0.97  
% 2.17/0.97  --superposition_flag                    true
% 2.17/0.97  --sup_passive_queue_type                priority_queues
% 2.17/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.17/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.17/0.97  --demod_completeness_check              fast
% 2.17/0.97  --demod_use_ground                      true
% 2.17/0.97  --sup_to_prop_solver                    passive
% 2.17/0.97  --sup_prop_simpl_new                    true
% 2.17/0.97  --sup_prop_simpl_given                  true
% 2.17/0.97  --sup_fun_splitting                     false
% 2.17/0.97  --sup_smt_interval                      50000
% 2.17/0.97  
% 2.17/0.97  ------ Superposition Simplification Setup
% 2.17/0.97  
% 2.17/0.97  --sup_indices_passive                   []
% 2.17/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.17/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.97  --sup_full_bw                           [BwDemod]
% 2.17/0.97  --sup_immed_triv                        [TrivRules]
% 2.17/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.17/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.97  --sup_immed_bw_main                     []
% 2.17/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.17/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/0.97  
% 2.17/0.97  ------ Combination Options
% 2.17/0.97  
% 2.17/0.97  --comb_res_mult                         3
% 2.17/0.97  --comb_sup_mult                         2
% 2.17/0.97  --comb_inst_mult                        10
% 2.17/0.97  
% 2.17/0.97  ------ Debug Options
% 2.17/0.97  
% 2.17/0.97  --dbg_backtrace                         false
% 2.17/0.97  --dbg_dump_prop_clauses                 false
% 2.17/0.97  --dbg_dump_prop_clauses_file            -
% 2.17/0.97  --dbg_out_stat                          false
% 2.17/0.97  
% 2.17/0.97  
% 2.17/0.97  
% 2.17/0.97  
% 2.17/0.97  ------ Proving...
% 2.17/0.97  
% 2.17/0.97  
% 2.17/0.97  % SZS status Theorem for theBenchmark.p
% 2.17/0.97  
% 2.17/0.97   Resolution empty clause
% 2.17/0.97  
% 2.17/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.17/0.97  
% 2.17/0.97  fof(f14,conjecture,(
% 2.17/0.97    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 2.17/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.17/0.97  
% 2.17/0.97  fof(f15,negated_conjecture,(
% 2.17/0.97    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 2.17/0.97    inference(negated_conjecture,[],[f14])).
% 2.17/0.97  
% 2.17/0.97  fof(f27,plain,(
% 2.17/0.97    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 2.17/0.97    inference(ennf_transformation,[],[f15])).
% 2.17/0.97  
% 2.17/0.97  fof(f28,plain,(
% 2.17/0.97    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 2.17/0.97    inference(flattening,[],[f27])).
% 2.17/0.97  
% 2.17/0.97  fof(f37,plain,(
% 2.17/0.97    ( ! [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) => (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,sK2),X0) & m1_subset_1(sK2,X0))) )),
% 2.17/0.97    introduced(choice_axiom,[])).
% 2.17/0.97  
% 2.17/0.97  fof(f36,plain,(
% 2.17/0.97    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK1) & v1_subset_1(k6_domain_1(sK1,X1),sK1) & m1_subset_1(X1,sK1)) & ~v1_xboole_0(sK1))),
% 2.17/0.97    introduced(choice_axiom,[])).
% 2.17/0.97  
% 2.17/0.97  fof(f38,plain,(
% 2.17/0.97    (v1_zfmisc_1(sK1) & v1_subset_1(k6_domain_1(sK1,sK2),sK1) & m1_subset_1(sK2,sK1)) & ~v1_xboole_0(sK1)),
% 2.17/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f28,f37,f36])).
% 2.17/0.97  
% 2.17/0.97  fof(f60,plain,(
% 2.17/0.97    m1_subset_1(sK2,sK1)),
% 2.17/0.97    inference(cnf_transformation,[],[f38])).
% 2.17/0.97  
% 2.17/0.97  fof(f10,axiom,(
% 2.17/0.97    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.17/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.17/0.97  
% 2.17/0.97  fof(f23,plain,(
% 2.17/0.97    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.17/0.97    inference(ennf_transformation,[],[f10])).
% 2.17/0.97  
% 2.17/0.97  fof(f24,plain,(
% 2.17/0.97    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.17/0.97    inference(flattening,[],[f23])).
% 2.17/0.97  
% 2.17/0.97  fof(f54,plain,(
% 2.17/0.97    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.17/0.97    inference(cnf_transformation,[],[f24])).
% 2.17/0.97  
% 2.17/0.97  fof(f3,axiom,(
% 2.17/0.97    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.17/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.17/0.97  
% 2.17/0.97  fof(f46,plain,(
% 2.17/0.97    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.17/0.97    inference(cnf_transformation,[],[f3])).
% 2.17/0.97  
% 2.17/0.97  fof(f67,plain,(
% 2.17/0.97    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.17/0.97    inference(definition_unfolding,[],[f54,f46])).
% 2.17/0.97  
% 2.17/0.97  fof(f59,plain,(
% 2.17/0.97    ~v1_xboole_0(sK1)),
% 2.17/0.97    inference(cnf_transformation,[],[f38])).
% 2.17/0.97  
% 2.17/0.97  fof(f8,axiom,(
% 2.17/0.97    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.17/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.17/0.97  
% 2.17/0.97  fof(f20,plain,(
% 2.17/0.97    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.17/0.97    inference(ennf_transformation,[],[f8])).
% 2.17/0.97  
% 2.17/0.97  fof(f21,plain,(
% 2.17/0.97    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.17/0.97    inference(flattening,[],[f20])).
% 2.17/0.97  
% 2.17/0.97  fof(f52,plain,(
% 2.17/0.97    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.17/0.97    inference(cnf_transformation,[],[f21])).
% 2.17/0.97  
% 2.17/0.97  fof(f4,axiom,(
% 2.17/0.97    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.17/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.17/0.97  
% 2.17/0.97  fof(f35,plain,(
% 2.17/0.97    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.17/0.97    inference(nnf_transformation,[],[f4])).
% 2.17/0.97  
% 2.17/0.97  fof(f47,plain,(
% 2.17/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.17/0.97    inference(cnf_transformation,[],[f35])).
% 2.17/0.97  
% 2.17/0.97  fof(f13,axiom,(
% 2.17/0.97    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 2.17/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.17/0.97  
% 2.17/0.97  fof(f25,plain,(
% 2.17/0.97    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 2.17/0.97    inference(ennf_transformation,[],[f13])).
% 2.17/0.97  
% 2.17/0.97  fof(f26,plain,(
% 2.17/0.97    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.17/0.97    inference(flattening,[],[f25])).
% 2.17/0.97  
% 2.17/0.97  fof(f58,plain,(
% 2.17/0.97    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.17/0.97    inference(cnf_transformation,[],[f26])).
% 2.17/0.97  
% 2.17/0.97  fof(f62,plain,(
% 2.17/0.97    v1_zfmisc_1(sK1)),
% 2.17/0.97    inference(cnf_transformation,[],[f38])).
% 2.17/0.97  
% 2.17/0.97  fof(f61,plain,(
% 2.17/0.97    v1_subset_1(k6_domain_1(sK1,sK2),sK1)),
% 2.17/0.97    inference(cnf_transformation,[],[f38])).
% 2.17/0.97  
% 2.17/0.97  fof(f2,axiom,(
% 2.17/0.97    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.17/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.17/0.97  
% 2.17/0.97  fof(f31,plain,(
% 2.17/0.97    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.17/0.97    inference(nnf_transformation,[],[f2])).
% 2.17/0.97  
% 2.17/0.97  fof(f32,plain,(
% 2.17/0.97    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.17/0.97    inference(rectify,[],[f31])).
% 2.17/0.97  
% 2.17/0.97  fof(f33,plain,(
% 2.17/0.97    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 2.17/0.97    introduced(choice_axiom,[])).
% 2.17/0.97  
% 2.17/0.97  fof(f34,plain,(
% 2.17/0.97    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.17/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 2.17/0.97  
% 2.17/0.97  fof(f42,plain,(
% 2.17/0.97    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.17/0.97    inference(cnf_transformation,[],[f34])).
% 2.17/0.97  
% 2.17/0.97  fof(f66,plain,(
% 2.17/0.97    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 2.17/0.97    inference(definition_unfolding,[],[f42,f46])).
% 2.17/0.97  
% 2.17/0.97  fof(f72,plain,(
% 2.17/0.97    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_tarski(X0,X0))) )),
% 2.17/0.97    inference(equality_resolution,[],[f66])).
% 2.17/0.97  
% 2.17/0.97  fof(f43,plain,(
% 2.17/0.97    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.17/0.97    inference(cnf_transformation,[],[f34])).
% 2.17/0.97  
% 2.17/0.97  fof(f65,plain,(
% 2.17/0.97    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 2.17/0.97    inference(definition_unfolding,[],[f43,f46])).
% 2.17/0.97  
% 2.17/0.97  fof(f70,plain,(
% 2.17/0.97    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 2.17/0.97    inference(equality_resolution,[],[f65])).
% 2.17/0.97  
% 2.17/0.97  fof(f71,plain,(
% 2.17/0.97    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 2.17/0.97    inference(equality_resolution,[],[f70])).
% 2.17/0.97  
% 2.17/0.97  fof(f1,axiom,(
% 2.17/0.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.17/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.17/0.97  
% 2.17/0.97  fof(f29,plain,(
% 2.17/0.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.17/0.97    inference(nnf_transformation,[],[f1])).
% 2.17/0.97  
% 2.17/0.97  fof(f30,plain,(
% 2.17/0.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.17/0.97    inference(flattening,[],[f29])).
% 2.17/0.97  
% 2.17/0.97  fof(f39,plain,(
% 2.17/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.17/0.97    inference(cnf_transformation,[],[f30])).
% 2.17/0.97  
% 2.17/0.97  fof(f69,plain,(
% 2.17/0.97    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.17/0.97    inference(equality_resolution,[],[f39])).
% 2.17/0.97  
% 2.17/0.97  fof(f7,axiom,(
% 2.17/0.97    ! [X0] : (l1_struct_0(X0) => ~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)))),
% 2.17/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.17/0.97  
% 2.17/0.97  fof(f19,plain,(
% 2.17/0.97    ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0))),
% 2.17/0.97    inference(ennf_transformation,[],[f7])).
% 2.17/0.97  
% 2.17/0.97  fof(f51,plain,(
% 2.17/0.97    ( ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 2.17/0.97    inference(cnf_transformation,[],[f19])).
% 2.17/0.97  
% 2.17/0.97  fof(f9,axiom,(
% 2.17/0.97    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 2.17/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.17/0.97  
% 2.17/0.97  fof(f22,plain,(
% 2.17/0.97    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 2.17/0.97    inference(ennf_transformation,[],[f9])).
% 2.17/0.97  
% 2.17/0.97  fof(f53,plain,(
% 2.17/0.97    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 2.17/0.97    inference(cnf_transformation,[],[f22])).
% 2.17/0.97  
% 2.17/0.97  fof(f11,axiom,(
% 2.17/0.97    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 2.17/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.17/0.97  
% 2.17/0.97  fof(f16,plain,(
% 2.17/0.97    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 2.17/0.97    inference(pure_predicate_removal,[],[f11])).
% 2.17/0.97  
% 2.17/0.97  fof(f55,plain,(
% 2.17/0.97    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 2.17/0.97    inference(cnf_transformation,[],[f16])).
% 2.17/0.97  
% 2.17/0.97  fof(f12,axiom,(
% 2.17/0.97    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 2.17/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.17/0.97  
% 2.17/0.97  fof(f56,plain,(
% 2.17/0.97    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 2.17/0.97    inference(cnf_transformation,[],[f12])).
% 2.17/0.97  
% 2.17/0.97  fof(f6,axiom,(
% 2.17/0.97    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.17/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.17/0.97  
% 2.17/0.97  fof(f18,plain,(
% 2.17/0.97    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.17/0.97    inference(ennf_transformation,[],[f6])).
% 2.17/0.97  
% 2.17/0.97  fof(f50,plain,(
% 2.17/0.97    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.17/0.97    inference(cnf_transformation,[],[f18])).
% 2.17/0.97  
% 2.17/0.97  fof(f41,plain,(
% 2.17/0.97    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.17/0.97    inference(cnf_transformation,[],[f30])).
% 2.17/0.97  
% 2.17/0.97  fof(f40,plain,(
% 2.17/0.97    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.17/0.97    inference(cnf_transformation,[],[f30])).
% 2.17/0.97  
% 2.17/0.97  fof(f68,plain,(
% 2.17/0.97    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.17/0.97    inference(equality_resolution,[],[f40])).
% 2.17/0.97  
% 2.17/0.97  fof(f5,axiom,(
% 2.17/0.97    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.17/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.17/0.97  
% 2.17/0.97  fof(f17,plain,(
% 2.17/0.97    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.17/0.97    inference(ennf_transformation,[],[f5])).
% 2.17/0.97  
% 2.17/0.97  fof(f49,plain,(
% 2.17/0.97    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.17/0.97    inference(cnf_transformation,[],[f17])).
% 2.17/0.97  
% 2.17/0.97  fof(f48,plain,(
% 2.17/0.97    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.17/0.97    inference(cnf_transformation,[],[f35])).
% 2.17/0.97  
% 2.17/0.97  cnf(c_20,negated_conjecture,
% 2.17/0.97      ( m1_subset_1(sK2,sK1) ),
% 2.17/0.97      inference(cnf_transformation,[],[f60]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1255,plain,
% 2.17/0.97      ( m1_subset_1(sK2,sK1) = iProver_top ),
% 2.17/0.97      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_14,plain,
% 2.17/0.97      ( ~ m1_subset_1(X0,X1)
% 2.17/0.97      | v1_xboole_0(X1)
% 2.17/0.97      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 2.17/0.97      inference(cnf_transformation,[],[f67]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1257,plain,
% 2.17/0.97      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
% 2.17/0.97      | m1_subset_1(X1,X0) != iProver_top
% 2.17/0.97      | v1_xboole_0(X0) = iProver_top ),
% 2.17/0.97      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_2035,plain,
% 2.17/0.97      ( k6_domain_1(sK1,sK2) = k2_tarski(sK2,sK2)
% 2.17/0.97      | v1_xboole_0(sK1) = iProver_top ),
% 2.17/0.97      inference(superposition,[status(thm)],[c_1255,c_1257]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_21,negated_conjecture,
% 2.17/0.97      ( ~ v1_xboole_0(sK1) ),
% 2.17/0.97      inference(cnf_transformation,[],[f59]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1396,plain,
% 2.17/0.97      ( ~ m1_subset_1(sK2,sK1)
% 2.17/0.97      | v1_xboole_0(sK1)
% 2.17/0.97      | k6_domain_1(sK1,sK2) = k2_tarski(sK2,sK2) ),
% 2.17/0.97      inference(instantiation,[status(thm)],[c_14]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_2380,plain,
% 2.17/0.97      ( k6_domain_1(sK1,sK2) = k2_tarski(sK2,sK2) ),
% 2.17/0.97      inference(global_propositional_subsumption,
% 2.17/0.97                [status(thm)],
% 2.17/0.97                [c_2035,c_21,c_20,c_1396]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_12,plain,
% 2.17/0.97      ( ~ m1_subset_1(X0,X1)
% 2.17/0.97      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 2.17/0.97      | v1_xboole_0(X1) ),
% 2.17/0.97      inference(cnf_transformation,[],[f52]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1258,plain,
% 2.17/0.97      ( m1_subset_1(X0,X1) != iProver_top
% 2.17/0.97      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
% 2.17/0.97      | v1_xboole_0(X1) = iProver_top ),
% 2.17/0.97      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_8,plain,
% 2.17/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.17/0.97      inference(cnf_transformation,[],[f47]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1259,plain,
% 2.17/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.17/0.97      | r1_tarski(X0,X1) = iProver_top ),
% 2.17/0.97      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_2191,plain,
% 2.17/0.97      ( m1_subset_1(X0,X1) != iProver_top
% 2.17/0.97      | r1_tarski(k6_domain_1(X1,X0),X1) = iProver_top
% 2.17/0.97      | v1_xboole_0(X1) = iProver_top ),
% 2.17/0.97      inference(superposition,[status(thm)],[c_1258,c_1259]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_2683,plain,
% 2.17/0.97      ( m1_subset_1(sK2,sK1) != iProver_top
% 2.17/0.97      | r1_tarski(k2_tarski(sK2,sK2),sK1) = iProver_top
% 2.17/0.97      | v1_xboole_0(sK1) = iProver_top ),
% 2.17/0.97      inference(superposition,[status(thm)],[c_2380,c_2191]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_22,plain,
% 2.17/0.97      ( v1_xboole_0(sK1) != iProver_top ),
% 2.17/0.97      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_23,plain,
% 2.17/0.97      ( m1_subset_1(sK2,sK1) = iProver_top ),
% 2.17/0.97      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_2716,plain,
% 2.17/0.97      ( r1_tarski(k2_tarski(sK2,sK2),sK1) = iProver_top ),
% 2.17/0.97      inference(global_propositional_subsumption,
% 2.17/0.97                [status(thm)],
% 2.17/0.97                [c_2683,c_22,c_23]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_17,plain,
% 2.17/0.97      ( ~ r1_tarski(X0,X1)
% 2.17/0.97      | ~ v1_zfmisc_1(X1)
% 2.17/0.97      | v1_xboole_0(X1)
% 2.17/0.97      | v1_xboole_0(X0)
% 2.17/0.97      | X1 = X0 ),
% 2.17/0.97      inference(cnf_transformation,[],[f58]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_18,negated_conjecture,
% 2.17/0.97      ( v1_zfmisc_1(sK1) ),
% 2.17/0.97      inference(cnf_transformation,[],[f62]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_331,plain,
% 2.17/0.97      ( ~ r1_tarski(X0,X1)
% 2.17/0.97      | v1_xboole_0(X1)
% 2.17/0.97      | v1_xboole_0(X0)
% 2.17/0.97      | X1 = X0
% 2.17/0.97      | sK1 != X1 ),
% 2.17/0.97      inference(resolution_lifted,[status(thm)],[c_17,c_18]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_332,plain,
% 2.17/0.97      ( ~ r1_tarski(X0,sK1) | v1_xboole_0(X0) | v1_xboole_0(sK1) | sK1 = X0 ),
% 2.17/0.97      inference(unflattening,[status(thm)],[c_331]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_334,plain,
% 2.17/0.97      ( v1_xboole_0(X0) | ~ r1_tarski(X0,sK1) | sK1 = X0 ),
% 2.17/0.97      inference(global_propositional_subsumption,[status(thm)],[c_332,c_21]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_335,plain,
% 2.17/0.97      ( ~ r1_tarski(X0,sK1) | v1_xboole_0(X0) | sK1 = X0 ),
% 2.17/0.97      inference(renaming,[status(thm)],[c_334]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1251,plain,
% 2.17/0.97      ( sK1 = X0
% 2.17/0.97      | r1_tarski(X0,sK1) != iProver_top
% 2.17/0.97      | v1_xboole_0(X0) = iProver_top ),
% 2.17/0.97      inference(predicate_to_equality,[status(thm)],[c_335]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_2722,plain,
% 2.17/0.97      ( k2_tarski(sK2,sK2) = sK1
% 2.17/0.97      | v1_xboole_0(k2_tarski(sK2,sK2)) = iProver_top ),
% 2.17/0.97      inference(superposition,[status(thm)],[c_2716,c_1251]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_19,negated_conjecture,
% 2.17/0.97      ( v1_subset_1(k6_domain_1(sK1,sK2),sK1) ),
% 2.17/0.97      inference(cnf_transformation,[],[f61]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_6,plain,
% 2.17/0.97      ( ~ r2_hidden(X0,k2_tarski(X1,X1)) | X0 = X1 ),
% 2.17/0.97      inference(cnf_transformation,[],[f72]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_56,plain,
% 2.17/0.97      ( ~ r2_hidden(sK1,k2_tarski(sK1,sK1)) | sK1 = sK1 ),
% 2.17/0.97      inference(instantiation,[status(thm)],[c_6]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_5,plain,
% 2.17/0.97      ( r2_hidden(X0,k2_tarski(X0,X0)) ),
% 2.17/0.97      inference(cnf_transformation,[],[f71]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_59,plain,
% 2.17/0.97      ( r2_hidden(sK1,k2_tarski(sK1,sK1)) ),
% 2.17/0.97      inference(instantiation,[status(thm)],[c_5]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f69]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_68,plain,
% 2.17/0.97      ( r1_tarski(sK1,sK1) ),
% 2.17/0.97      inference(instantiation,[status(thm)],[c_2]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_11,plain,
% 2.17/0.97      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~ l1_struct_0(X0) ),
% 2.17/0.97      inference(cnf_transformation,[],[f51]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_13,plain,
% 2.17/0.97      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 2.17/0.97      inference(cnf_transformation,[],[f53]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_15,plain,
% 2.17/0.97      ( l1_orders_2(k2_yellow_1(X0)) ),
% 2.17/0.97      inference(cnf_transformation,[],[f55]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_292,plain,
% 2.17/0.97      ( l1_struct_0(X0) | k2_yellow_1(X1) != X0 ),
% 2.17/0.97      inference(resolution_lifted,[status(thm)],[c_13,c_15]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_293,plain,
% 2.17/0.97      ( l1_struct_0(k2_yellow_1(X0)) ),
% 2.17/0.97      inference(unflattening,[status(thm)],[c_292]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_303,plain,
% 2.17/0.97      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
% 2.17/0.97      | k2_yellow_1(X1) != X0 ),
% 2.17/0.97      inference(resolution_lifted,[status(thm)],[c_11,c_293]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_304,plain,
% 2.17/0.97      ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(X0)),u1_struct_0(k2_yellow_1(X0))) ),
% 2.17/0.97      inference(unflattening,[status(thm)],[c_303]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1252,plain,
% 2.17/0.97      ( v1_subset_1(k2_struct_0(k2_yellow_1(X0)),u1_struct_0(k2_yellow_1(X0))) != iProver_top ),
% 2.17/0.97      inference(predicate_to_equality,[status(thm)],[c_304]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_16,plain,
% 2.17/0.97      ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
% 2.17/0.97      inference(cnf_transformation,[],[f56]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_10,plain,
% 2.17/0.97      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.17/0.97      inference(cnf_transformation,[],[f50]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_312,plain,
% 2.17/0.97      ( k2_yellow_1(X0) != X1 | u1_struct_0(X1) = k2_struct_0(X1) ),
% 2.17/0.97      inference(resolution_lifted,[status(thm)],[c_10,c_293]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_313,plain,
% 2.17/0.97      ( u1_struct_0(k2_yellow_1(X0)) = k2_struct_0(k2_yellow_1(X0)) ),
% 2.17/0.97      inference(unflattening,[status(thm)],[c_312]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1275,plain,
% 2.17/0.97      ( k2_struct_0(k2_yellow_1(X0)) = X0 ),
% 2.17/0.97      inference(light_normalisation,[status(thm)],[c_313,c_16]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1282,plain,
% 2.17/0.97      ( v1_subset_1(X0,X0) != iProver_top ),
% 2.17/0.97      inference(light_normalisation,[status(thm)],[c_1252,c_16,c_1275]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1352,plain,
% 2.17/0.97      ( ~ v1_subset_1(X0,X0) ),
% 2.17/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_1282]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1354,plain,
% 2.17/0.97      ( ~ v1_subset_1(sK1,sK1) ),
% 2.17/0.97      inference(instantiation,[status(thm)],[c_1352]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1384,plain,
% 2.17/0.97      ( m1_subset_1(k6_domain_1(sK1,sK2),k1_zfmisc_1(sK1))
% 2.17/0.97      | ~ m1_subset_1(sK2,sK1)
% 2.17/0.97      | v1_xboole_0(sK1) ),
% 2.17/0.97      inference(instantiation,[status(thm)],[c_12]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_837,plain,
% 2.17/0.97      ( ~ v1_subset_1(X0,X1) | v1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.17/0.97      theory(equality) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1409,plain,
% 2.17/0.97      ( v1_subset_1(X0,X1)
% 2.17/0.97      | ~ v1_subset_1(k6_domain_1(sK1,sK2),sK1)
% 2.17/0.97      | X0 != k6_domain_1(sK1,sK2)
% 2.17/0.97      | X1 != sK1 ),
% 2.17/0.97      inference(instantiation,[status(thm)],[c_837]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1411,plain,
% 2.17/0.97      ( ~ v1_subset_1(k6_domain_1(sK1,sK2),sK1)
% 2.17/0.97      | v1_subset_1(sK1,sK1)
% 2.17/0.97      | sK1 != k6_domain_1(sK1,sK2)
% 2.17/0.97      | sK1 != sK1 ),
% 2.17/0.97      inference(instantiation,[status(thm)],[c_1409]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_0,plain,
% 2.17/0.97      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.17/0.97      inference(cnf_transformation,[],[f41]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1471,plain,
% 2.17/0.97      ( ~ r1_tarski(X0,k6_domain_1(sK1,sK2))
% 2.17/0.97      | ~ r1_tarski(k6_domain_1(sK1,sK2),X0)
% 2.17/0.97      | X0 = k6_domain_1(sK1,sK2) ),
% 2.17/0.97      inference(instantiation,[status(thm)],[c_0]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1478,plain,
% 2.17/0.97      ( ~ r1_tarski(k6_domain_1(sK1,sK2),sK1)
% 2.17/0.97      | ~ r1_tarski(sK1,k6_domain_1(sK1,sK2))
% 2.17/0.97      | sK1 = k6_domain_1(sK1,sK2) ),
% 2.17/0.97      inference(instantiation,[status(thm)],[c_1471]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1543,plain,
% 2.17/0.97      ( ~ m1_subset_1(k6_domain_1(sK1,sK2),k1_zfmisc_1(sK1))
% 2.17/0.97      | r1_tarski(k6_domain_1(sK1,sK2),sK1) ),
% 2.17/0.97      inference(instantiation,[status(thm)],[c_8]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_831,plain,
% 2.17/0.97      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,X2) | X2 != X1 ),
% 2.17/0.97      theory(equality) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1613,plain,
% 2.17/0.97      ( ~ r1_tarski(X0,X1)
% 2.17/0.97      | r1_tarski(X0,k6_domain_1(sK1,sK2))
% 2.17/0.97      | k6_domain_1(sK1,sK2) != X1 ),
% 2.17/0.97      inference(instantiation,[status(thm)],[c_831]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_2091,plain,
% 2.17/0.97      ( r1_tarski(X0,k6_domain_1(sK1,sK2))
% 2.17/0.97      | ~ r1_tarski(X0,k2_tarski(sK2,sK2))
% 2.17/0.97      | k6_domain_1(sK1,sK2) != k2_tarski(sK2,sK2) ),
% 2.17/0.97      inference(instantiation,[status(thm)],[c_1613]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_2093,plain,
% 2.17/0.97      ( r1_tarski(sK1,k6_domain_1(sK1,sK2))
% 2.17/0.97      | ~ r1_tarski(sK1,k2_tarski(sK2,sK2))
% 2.17/0.97      | k6_domain_1(sK1,sK2) != k2_tarski(sK2,sK2) ),
% 2.17/0.97      inference(instantiation,[status(thm)],[c_2091]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_2785,plain,
% 2.17/0.97      ( ~ r1_tarski(X0,X1)
% 2.17/0.97      | r1_tarski(X0,k2_tarski(sK2,sK2))
% 2.17/0.97      | k2_tarski(sK2,sK2) != X1 ),
% 2.17/0.97      inference(instantiation,[status(thm)],[c_831]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_2787,plain,
% 2.17/0.97      ( r1_tarski(sK1,k2_tarski(sK2,sK2))
% 2.17/0.97      | ~ r1_tarski(sK1,sK1)
% 2.17/0.97      | k2_tarski(sK2,sK2) != sK1 ),
% 2.17/0.97      inference(instantiation,[status(thm)],[c_2785]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_2837,plain,
% 2.17/0.97      ( v1_xboole_0(k2_tarski(sK2,sK2)) = iProver_top ),
% 2.17/0.97      inference(global_propositional_subsumption,
% 2.17/0.97                [status(thm)],
% 2.17/0.97                [c_2722,c_21,c_20,c_19,c_56,c_59,c_68,c_1354,c_1384,c_1396,
% 2.17/0.97                 c_1411,c_1478,c_1543,c_2093,c_2787]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f68]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1265,plain,
% 2.17/0.97      ( r1_tarski(X0,X0) = iProver_top ),
% 2.17/0.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1262,plain,
% 2.17/0.97      ( r2_hidden(X0,k2_tarski(X0,X0)) = iProver_top ),
% 2.17/0.97      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_9,plain,
% 2.17/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.17/0.97      | ~ r2_hidden(X2,X0)
% 2.17/0.97      | ~ v1_xboole_0(X1) ),
% 2.17/0.97      inference(cnf_transformation,[],[f49]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_7,plain,
% 2.17/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.17/0.97      inference(cnf_transformation,[],[f48]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_165,plain,
% 2.17/0.97      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.17/0.97      inference(prop_impl,[status(thm)],[c_7]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_166,plain,
% 2.17/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.17/0.97      inference(renaming,[status(thm)],[c_165]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_203,plain,
% 2.17/0.97      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 2.17/0.97      inference(bin_hyper_res,[status(thm)],[c_9,c_166]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1253,plain,
% 2.17/0.97      ( r2_hidden(X0,X1) != iProver_top
% 2.17/0.97      | r1_tarski(X1,X2) != iProver_top
% 2.17/0.97      | v1_xboole_0(X2) != iProver_top ),
% 2.17/0.97      inference(predicate_to_equality,[status(thm)],[c_203]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1637,plain,
% 2.17/0.97      ( r1_tarski(k2_tarski(X0,X0),X1) != iProver_top
% 2.17/0.97      | v1_xboole_0(X1) != iProver_top ),
% 2.17/0.97      inference(superposition,[status(thm)],[c_1262,c_1253]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_1860,plain,
% 2.17/0.97      ( v1_xboole_0(k2_tarski(X0,X0)) != iProver_top ),
% 2.17/0.97      inference(superposition,[status(thm)],[c_1265,c_1637]) ).
% 2.17/0.97  
% 2.17/0.97  cnf(c_2842,plain,
% 2.17/0.97      ( $false ),
% 2.17/0.97      inference(forward_subsumption_resolution,[status(thm)],[c_2837,c_1860]) ).
% 2.17/0.97  
% 2.17/0.97  
% 2.17/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.17/0.97  
% 2.17/0.97  ------                               Statistics
% 2.17/0.97  
% 2.17/0.97  ------ General
% 2.17/0.97  
% 2.17/0.97  abstr_ref_over_cycles:                  0
% 2.17/0.97  abstr_ref_under_cycles:                 0
% 2.17/0.97  gc_basic_clause_elim:                   0
% 2.17/0.97  forced_gc_time:                         0
% 2.17/0.97  parsing_time:                           0.009
% 2.17/0.97  unif_index_cands_time:                  0.
% 2.17/0.97  unif_index_add_time:                    0.
% 2.17/0.97  orderings_time:                         0.
% 2.17/0.97  out_proof_time:                         0.011
% 2.17/0.97  total_time:                             0.12
% 2.17/0.97  num_of_symbols:                         48
% 2.17/0.97  num_of_terms:                           2516
% 2.17/0.97  
% 2.17/0.97  ------ Preprocessing
% 2.17/0.97  
% 2.17/0.97  num_of_splits:                          0
% 2.17/0.97  num_of_split_atoms:                     0
% 2.17/0.97  num_of_reused_defs:                     0
% 2.17/0.97  num_eq_ax_congr_red:                    24
% 2.17/0.97  num_of_sem_filtered_clauses:            1
% 2.17/0.97  num_of_subtypes:                        0
% 2.17/0.97  monotx_restored_types:                  0
% 2.17/0.97  sat_num_of_epr_types:                   0
% 2.17/0.97  sat_num_of_non_cyclic_types:            0
% 2.17/0.97  sat_guarded_non_collapsed_types:        0
% 2.17/0.97  num_pure_diseq_elim:                    0
% 2.17/0.97  simp_replaced_by:                       0
% 2.17/0.97  res_preprocessed:                       96
% 2.17/0.97  prep_upred:                             0
% 2.17/0.97  prep_unflattend:                        32
% 2.17/0.97  smt_new_axioms:                         0
% 2.17/0.97  pred_elim_cands:                        5
% 2.17/0.97  pred_elim:                              3
% 2.17/0.97  pred_elim_cl:                           3
% 2.17/0.97  pred_elim_cycles:                       10
% 2.17/0.97  merged_defs:                            8
% 2.17/0.97  merged_defs_ncl:                        0
% 2.17/0.97  bin_hyper_res:                          9
% 2.17/0.97  prep_cycles:                            4
% 2.17/0.97  pred_elim_time:                         0.008
% 2.17/0.97  splitting_time:                         0.
% 2.17/0.97  sem_filter_time:                        0.
% 2.17/0.97  monotx_time:                            0.
% 2.17/0.97  subtype_inf_time:                       0.
% 2.17/0.97  
% 2.17/0.97  ------ Problem properties
% 2.17/0.97  
% 2.17/0.97  clauses:                                18
% 2.17/0.97  conjectures:                            3
% 2.17/0.97  epr:                                    6
% 2.17/0.97  horn:                                   14
% 2.17/0.97  ground:                                 3
% 2.17/0.97  unary:                                  8
% 2.17/0.97  binary:                                 3
% 2.17/0.97  lits:                                   35
% 2.17/0.97  lits_eq:                                10
% 2.17/0.97  fd_pure:                                0
% 2.17/0.97  fd_pseudo:                              0
% 2.17/0.97  fd_cond:                                1
% 2.17/0.97  fd_pseudo_cond:                         3
% 2.17/0.97  ac_symbols:                             0
% 2.17/0.97  
% 2.17/0.97  ------ Propositional Solver
% 2.17/0.97  
% 2.17/0.97  prop_solver_calls:                      27
% 2.17/0.97  prop_fast_solver_calls:                 544
% 2.17/0.97  smt_solver_calls:                       0
% 2.17/0.97  smt_fast_solver_calls:                  0
% 2.17/0.97  prop_num_of_clauses:                    887
% 2.17/0.97  prop_preprocess_simplified:             4033
% 2.17/0.97  prop_fo_subsumed:                       5
% 2.17/0.97  prop_solver_time:                       0.
% 2.17/0.97  smt_solver_time:                        0.
% 2.17/0.97  smt_fast_solver_time:                   0.
% 2.17/0.97  prop_fast_solver_time:                  0.
% 2.17/0.97  prop_unsat_core_time:                   0.
% 2.17/0.97  
% 2.17/0.97  ------ QBF
% 2.17/0.97  
% 2.17/0.97  qbf_q_res:                              0
% 2.17/0.97  qbf_num_tautologies:                    0
% 2.17/0.97  qbf_prep_cycles:                        0
% 2.17/0.97  
% 2.17/0.97  ------ BMC1
% 2.17/0.97  
% 2.17/0.97  bmc1_current_bound:                     -1
% 2.17/0.97  bmc1_last_solved_bound:                 -1
% 2.17/0.97  bmc1_unsat_core_size:                   -1
% 2.17/0.97  bmc1_unsat_core_parents_size:           -1
% 2.17/0.97  bmc1_merge_next_fun:                    0
% 2.17/0.97  bmc1_unsat_core_clauses_time:           0.
% 2.17/0.97  
% 2.17/0.97  ------ Instantiation
% 2.17/0.97  
% 2.17/0.97  inst_num_of_clauses:                    274
% 2.17/0.97  inst_num_in_passive:                    124
% 2.17/0.97  inst_num_in_active:                     124
% 2.17/0.97  inst_num_in_unprocessed:                26
% 2.17/0.97  inst_num_of_loops:                      130
% 2.17/0.97  inst_num_of_learning_restarts:          0
% 2.17/0.97  inst_num_moves_active_passive:          4
% 2.17/0.97  inst_lit_activity:                      0
% 2.17/0.97  inst_lit_activity_moves:                0
% 2.17/0.97  inst_num_tautologies:                   0
% 2.17/0.97  inst_num_prop_implied:                  0
% 2.17/0.97  inst_num_existing_simplified:           0
% 2.17/0.97  inst_num_eq_res_simplified:             0
% 2.17/0.97  inst_num_child_elim:                    0
% 2.17/0.97  inst_num_of_dismatching_blockings:      62
% 2.17/0.97  inst_num_of_non_proper_insts:           191
% 2.17/0.97  inst_num_of_duplicates:                 0
% 2.17/0.97  inst_inst_num_from_inst_to_res:         0
% 2.17/0.97  inst_dismatching_checking_time:         0.
% 2.17/0.97  
% 2.17/0.97  ------ Resolution
% 2.17/0.97  
% 2.17/0.97  res_num_of_clauses:                     0
% 2.17/0.97  res_num_in_passive:                     0
% 2.17/0.97  res_num_in_active:                      0
% 2.17/0.97  res_num_of_loops:                       100
% 2.17/0.97  res_forward_subset_subsumed:            14
% 2.17/0.97  res_backward_subset_subsumed:           0
% 2.17/0.97  res_forward_subsumed:                   0
% 2.17/0.97  res_backward_subsumed:                  0
% 2.17/0.97  res_forward_subsumption_resolution:     0
% 2.17/0.97  res_backward_subsumption_resolution:    0
% 2.17/0.97  res_clause_to_clause_subsumption:       95
% 2.17/0.97  res_orphan_elimination:                 0
% 2.17/0.97  res_tautology_del:                      37
% 2.17/0.97  res_num_eq_res_simplified:              0
% 2.17/0.97  res_num_sel_changes:                    0
% 2.17/0.97  res_moves_from_active_to_pass:          0
% 2.17/0.97  
% 2.17/0.97  ------ Superposition
% 2.17/0.97  
% 2.17/0.97  sup_time_total:                         0.
% 2.17/0.97  sup_time_generating:                    0.
% 2.17/0.97  sup_time_sim_full:                      0.
% 2.17/0.97  sup_time_sim_immed:                     0.
% 2.17/0.97  
% 2.17/0.97  sup_num_of_clauses:                     34
% 2.17/0.97  sup_num_in_active:                      23
% 2.17/0.97  sup_num_in_passive:                     11
% 2.17/0.97  sup_num_of_loops:                       24
% 2.17/0.97  sup_fw_superposition:                   6
% 2.17/0.97  sup_bw_superposition:                   13
% 2.17/0.97  sup_immediate_simplified:               1
% 2.17/0.97  sup_given_eliminated:                   0
% 2.17/0.97  comparisons_done:                       0
% 2.17/0.97  comparisons_avoided:                    2
% 2.17/0.97  
% 2.17/0.97  ------ Simplifications
% 2.17/0.97  
% 2.17/0.97  
% 2.17/0.97  sim_fw_subset_subsumed:                 1
% 2.17/0.97  sim_bw_subset_subsumed:                 0
% 2.17/0.97  sim_fw_subsumed:                        0
% 2.17/0.97  sim_bw_subsumed:                        0
% 2.17/0.97  sim_fw_subsumption_res:                 1
% 2.17/0.97  sim_bw_subsumption_res:                 0
% 2.17/0.97  sim_tautology_del:                      1
% 2.17/0.97  sim_eq_tautology_del:                   2
% 2.17/0.97  sim_eq_res_simp:                        0
% 2.17/0.97  sim_fw_demodulated:                     0
% 2.17/0.97  sim_bw_demodulated:                     1
% 2.17/0.97  sim_light_normalised:                   2
% 2.17/0.97  sim_joinable_taut:                      0
% 2.17/0.97  sim_joinable_simp:                      0
% 2.17/0.97  sim_ac_normalised:                      0
% 2.17/0.97  sim_smt_subsumption:                    0
% 2.17/0.97  
%------------------------------------------------------------------------------
