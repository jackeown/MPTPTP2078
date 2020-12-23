%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:57 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 303 expanded)
%              Number of clauses        :   64 (  99 expanded)
%              Number of leaves         :   19 (  73 expanded)
%              Depth                    :   18
%              Number of atoms          :  323 ( 958 expanded)
%              Number of equality atoms :   94 ( 141 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
     => ( v1_zfmisc_1(X0)
        & v1_subset_1(k6_domain_1(X0,sK4),X0)
        & m1_subset_1(sK4,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_zfmisc_1(X0)
            & v1_subset_1(k6_domain_1(X0,X1),X0)
            & m1_subset_1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( v1_zfmisc_1(sK3)
          & v1_subset_1(k6_domain_1(sK3,X1),sK3)
          & m1_subset_1(X1,sK3) )
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( v1_zfmisc_1(sK3)
    & v1_subset_1(k6_domain_1(sK3,sK4),sK3)
    & m1_subset_1(sK4,sK3)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f29,f44,f43])).

fof(f68,plain,(
    m1_subset_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f67,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f66,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f70,plain,(
    v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_subset_1(sK2(X0),X0)
        & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK2(X0),X0)
      & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f40])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_subset_1(X1,X0)
           => ~ v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f60,plain,(
    ! [X0] : ~ v1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,(
    v1_subset_1(k6_domain_1(sK3,sK4),sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

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
    inference(nnf_transformation,[],[f17])).

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
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f46,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f71,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f72,plain,(
    ! [X0,X1] : k1_xboole_0 != k5_xboole_0(k1_tarski(X0),k4_xboole_0(X1,k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f56,f55])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_939,plain,
    ( m1_subset_1(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_940,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1790,plain,
    ( k6_domain_1(sK3,sK4) = k1_tarski(sK4)
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_939,c_940])).

cnf(c_23,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1110,plain,
    ( ~ m1_subset_1(sK4,sK3)
    | v1_xboole_0(sK3)
    | k6_domain_1(sK3,sK4) = k1_tarski(sK4) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2018,plain,
    ( k6_domain_1(sK3,sK4) = k1_tarski(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1790,c_23,c_22,c_1110])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_941,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2348,plain,
    ( m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(sK3)) = iProver_top
    | m1_subset_1(sK4,sK3) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2018,c_941])).

cnf(c_24,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_25,plain,
    ( m1_subset_1(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2625,plain,
    ( m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2348,c_24,c_25])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_943,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2630,plain,
    ( r1_tarski(k1_tarski(sK4),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2625,c_943])).

cnf(c_19,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_20,negated_conjecture,
    ( v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_305,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_20])).

cnf(c_306,plain,
    ( ~ r1_tarski(X0,sK3)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | sK3 = X0 ),
    inference(unflattening,[status(thm)],[c_305])).

cnf(c_308,plain,
    ( v1_xboole_0(X0)
    | ~ r1_tarski(X0,sK3)
    | sK3 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_306,c_23])).

cnf(c_309,plain,
    ( ~ r1_tarski(X0,sK3)
    | v1_xboole_0(X0)
    | sK3 = X0 ),
    inference(renaming,[status(thm)],[c_308])).

cnf(c_936,plain,
    ( sK3 = X0
    | r1_tarski(X0,sK3) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_309])).

cnf(c_2753,plain,
    ( k1_tarski(sK4) = sK3
    | v1_xboole_0(k1_tarski(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2630,c_936])).

cnf(c_13,plain,
    ( m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_945,plain,
    ( m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1632,plain,
    ( r1_tarski(sK2(X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_945,c_943])).

cnf(c_1711,plain,
    ( sK2(sK3) = sK3
    | v1_xboole_0(sK2(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1632,c_936])).

cnf(c_11,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_14,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_167,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_14])).

cnf(c_168,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_167])).

cnf(c_203,plain,
    ( v1_subset_1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_11,c_168])).

cnf(c_12,plain,
    ( ~ v1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_280,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X2 != X1
    | sK2(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_203,c_12])).

cnf(c_281,plain,
    ( ~ r1_tarski(sK2(X0),X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(sK2(X0)) ),
    inference(unflattening,[status(thm)],[c_280])).

cnf(c_282,plain,
    ( r1_tarski(sK2(X0),X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK2(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_281])).

cnf(c_284,plain,
    ( r1_tarski(sK2(sK3),sK3) != iProver_top
    | v1_xboole_0(sK2(sK3)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_282])).

cnf(c_1641,plain,
    ( r1_tarski(sK2(sK3),sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1632])).

cnf(c_1725,plain,
    ( sK2(sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1711,c_24,c_284,c_1641])).

cnf(c_21,negated_conjecture,
    ( v1_subset_1(k6_domain_1(sK3,sK4),sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_295,plain,
    ( k6_domain_1(sK3,sK4) != sK2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_21])).

cnf(c_296,plain,
    ( k6_domain_1(sK3,sK4) != sK2(sK3) ),
    inference(unflattening,[status(thm)],[c_295])).

cnf(c_1728,plain,
    ( k6_domain_1(sK3,sK4) != sK3 ),
    inference(demodulation,[status(thm)],[c_1725,c_296])).

cnf(c_2021,plain,
    ( k1_tarski(sK4) != sK3 ),
    inference(demodulation,[status(thm)],[c_2018,c_1728])).

cnf(c_2772,plain,
    ( v1_xboole_0(k1_tarski(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2753,c_2021])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_950,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_952,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1871,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_950,c_952])).

cnf(c_10,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_946,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1631,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_946,c_943])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_948,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1978,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1631,c_948])).

cnf(c_2306,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1871,c_1978])).

cnf(c_6434,plain,
    ( k1_tarski(sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2772,c_2306])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_9,plain,
    ( k5_xboole_0(k1_tarski(X0),k4_xboole_0(X1,k1_tarski(X0))) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1323,plain,
    ( k1_tarski(X0) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8,c_9])).

cnf(c_7412,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6434,c_1323])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:21:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.08/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.03  
% 2.08/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.08/1.03  
% 2.08/1.03  ------  iProver source info
% 2.08/1.03  
% 2.08/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.08/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.08/1.03  git: non_committed_changes: false
% 2.08/1.03  git: last_make_outside_of_git: false
% 2.08/1.03  
% 2.08/1.03  ------ 
% 2.08/1.03  
% 2.08/1.03  ------ Input Options
% 2.08/1.03  
% 2.08/1.03  --out_options                           all
% 2.08/1.03  --tptp_safe_out                         true
% 2.08/1.03  --problem_path                          ""
% 2.08/1.03  --include_path                          ""
% 2.08/1.03  --clausifier                            res/vclausify_rel
% 2.08/1.03  --clausifier_options                    --mode clausify
% 2.08/1.03  --stdin                                 false
% 2.08/1.03  --stats_out                             all
% 2.08/1.03  
% 2.08/1.03  ------ General Options
% 2.08/1.03  
% 2.08/1.03  --fof                                   false
% 2.08/1.03  --time_out_real                         305.
% 2.08/1.03  --time_out_virtual                      -1.
% 2.08/1.03  --symbol_type_check                     false
% 2.08/1.03  --clausify_out                          false
% 2.08/1.03  --sig_cnt_out                           false
% 2.08/1.03  --trig_cnt_out                          false
% 2.08/1.03  --trig_cnt_out_tolerance                1.
% 2.08/1.03  --trig_cnt_out_sk_spl                   false
% 2.08/1.03  --abstr_cl_out                          false
% 2.08/1.03  
% 2.08/1.03  ------ Global Options
% 2.08/1.03  
% 2.08/1.03  --schedule                              default
% 2.08/1.03  --add_important_lit                     false
% 2.08/1.03  --prop_solver_per_cl                    1000
% 2.08/1.03  --min_unsat_core                        false
% 2.08/1.03  --soft_assumptions                      false
% 2.08/1.03  --soft_lemma_size                       3
% 2.08/1.03  --prop_impl_unit_size                   0
% 2.08/1.03  --prop_impl_unit                        []
% 2.08/1.03  --share_sel_clauses                     true
% 2.08/1.03  --reset_solvers                         false
% 2.08/1.03  --bc_imp_inh                            [conj_cone]
% 2.08/1.03  --conj_cone_tolerance                   3.
% 2.08/1.03  --extra_neg_conj                        none
% 2.08/1.03  --large_theory_mode                     true
% 2.08/1.03  --prolific_symb_bound                   200
% 2.08/1.03  --lt_threshold                          2000
% 2.08/1.03  --clause_weak_htbl                      true
% 2.08/1.03  --gc_record_bc_elim                     false
% 2.08/1.03  
% 2.08/1.03  ------ Preprocessing Options
% 2.08/1.03  
% 2.08/1.03  --preprocessing_flag                    true
% 2.08/1.03  --time_out_prep_mult                    0.1
% 2.08/1.03  --splitting_mode                        input
% 2.08/1.03  --splitting_grd                         true
% 2.08/1.03  --splitting_cvd                         false
% 2.08/1.03  --splitting_cvd_svl                     false
% 2.08/1.03  --splitting_nvd                         32
% 2.08/1.03  --sub_typing                            true
% 2.08/1.03  --prep_gs_sim                           true
% 2.08/1.03  --prep_unflatten                        true
% 2.08/1.03  --prep_res_sim                          true
% 2.08/1.03  --prep_upred                            true
% 2.08/1.03  --prep_sem_filter                       exhaustive
% 2.08/1.03  --prep_sem_filter_out                   false
% 2.08/1.03  --pred_elim                             true
% 2.08/1.03  --res_sim_input                         true
% 2.08/1.03  --eq_ax_congr_red                       true
% 2.08/1.03  --pure_diseq_elim                       true
% 2.08/1.03  --brand_transform                       false
% 2.08/1.03  --non_eq_to_eq                          false
% 2.08/1.03  --prep_def_merge                        true
% 2.08/1.03  --prep_def_merge_prop_impl              false
% 2.08/1.03  --prep_def_merge_mbd                    true
% 2.08/1.03  --prep_def_merge_tr_red                 false
% 2.08/1.03  --prep_def_merge_tr_cl                  false
% 2.08/1.03  --smt_preprocessing                     true
% 2.08/1.03  --smt_ac_axioms                         fast
% 2.08/1.03  --preprocessed_out                      false
% 2.08/1.03  --preprocessed_stats                    false
% 2.08/1.03  
% 2.08/1.03  ------ Abstraction refinement Options
% 2.08/1.03  
% 2.08/1.03  --abstr_ref                             []
% 2.08/1.03  --abstr_ref_prep                        false
% 2.08/1.03  --abstr_ref_until_sat                   false
% 2.08/1.03  --abstr_ref_sig_restrict                funpre
% 2.08/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.08/1.03  --abstr_ref_under                       []
% 2.08/1.03  
% 2.08/1.03  ------ SAT Options
% 2.08/1.03  
% 2.08/1.03  --sat_mode                              false
% 2.08/1.03  --sat_fm_restart_options                ""
% 2.08/1.03  --sat_gr_def                            false
% 2.08/1.03  --sat_epr_types                         true
% 2.08/1.03  --sat_non_cyclic_types                  false
% 2.08/1.03  --sat_finite_models                     false
% 2.08/1.03  --sat_fm_lemmas                         false
% 2.08/1.03  --sat_fm_prep                           false
% 2.08/1.03  --sat_fm_uc_incr                        true
% 2.08/1.03  --sat_out_model                         small
% 2.08/1.03  --sat_out_clauses                       false
% 2.08/1.03  
% 2.08/1.03  ------ QBF Options
% 2.08/1.03  
% 2.08/1.03  --qbf_mode                              false
% 2.08/1.03  --qbf_elim_univ                         false
% 2.08/1.03  --qbf_dom_inst                          none
% 2.08/1.03  --qbf_dom_pre_inst                      false
% 2.08/1.03  --qbf_sk_in                             false
% 2.08/1.03  --qbf_pred_elim                         true
% 2.08/1.03  --qbf_split                             512
% 2.08/1.03  
% 2.08/1.03  ------ BMC1 Options
% 2.08/1.03  
% 2.08/1.03  --bmc1_incremental                      false
% 2.08/1.03  --bmc1_axioms                           reachable_all
% 2.08/1.03  --bmc1_min_bound                        0
% 2.08/1.03  --bmc1_max_bound                        -1
% 2.08/1.03  --bmc1_max_bound_default                -1
% 2.08/1.03  --bmc1_symbol_reachability              true
% 2.08/1.03  --bmc1_property_lemmas                  false
% 2.08/1.03  --bmc1_k_induction                      false
% 2.08/1.03  --bmc1_non_equiv_states                 false
% 2.08/1.03  --bmc1_deadlock                         false
% 2.08/1.03  --bmc1_ucm                              false
% 2.08/1.03  --bmc1_add_unsat_core                   none
% 2.08/1.03  --bmc1_unsat_core_children              false
% 2.08/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.08/1.03  --bmc1_out_stat                         full
% 2.08/1.03  --bmc1_ground_init                      false
% 2.08/1.03  --bmc1_pre_inst_next_state              false
% 2.08/1.03  --bmc1_pre_inst_state                   false
% 2.08/1.03  --bmc1_pre_inst_reach_state             false
% 2.08/1.03  --bmc1_out_unsat_core                   false
% 2.08/1.03  --bmc1_aig_witness_out                  false
% 2.08/1.03  --bmc1_verbose                          false
% 2.08/1.03  --bmc1_dump_clauses_tptp                false
% 2.08/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.08/1.03  --bmc1_dump_file                        -
% 2.08/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.08/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.08/1.03  --bmc1_ucm_extend_mode                  1
% 2.08/1.03  --bmc1_ucm_init_mode                    2
% 2.08/1.03  --bmc1_ucm_cone_mode                    none
% 2.08/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.08/1.03  --bmc1_ucm_relax_model                  4
% 2.08/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.08/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.08/1.03  --bmc1_ucm_layered_model                none
% 2.08/1.03  --bmc1_ucm_max_lemma_size               10
% 2.08/1.03  
% 2.08/1.03  ------ AIG Options
% 2.08/1.03  
% 2.08/1.03  --aig_mode                              false
% 2.08/1.03  
% 2.08/1.03  ------ Instantiation Options
% 2.08/1.03  
% 2.08/1.03  --instantiation_flag                    true
% 2.08/1.03  --inst_sos_flag                         false
% 2.08/1.03  --inst_sos_phase                        true
% 2.08/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.08/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.08/1.03  --inst_lit_sel_side                     num_symb
% 2.08/1.03  --inst_solver_per_active                1400
% 2.08/1.03  --inst_solver_calls_frac                1.
% 2.08/1.03  --inst_passive_queue_type               priority_queues
% 2.08/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.08/1.03  --inst_passive_queues_freq              [25;2]
% 2.08/1.03  --inst_dismatching                      true
% 2.08/1.03  --inst_eager_unprocessed_to_passive     true
% 2.08/1.03  --inst_prop_sim_given                   true
% 2.08/1.03  --inst_prop_sim_new                     false
% 2.08/1.03  --inst_subs_new                         false
% 2.08/1.03  --inst_eq_res_simp                      false
% 2.08/1.03  --inst_subs_given                       false
% 2.08/1.03  --inst_orphan_elimination               true
% 2.08/1.03  --inst_learning_loop_flag               true
% 2.08/1.03  --inst_learning_start                   3000
% 2.08/1.03  --inst_learning_factor                  2
% 2.08/1.03  --inst_start_prop_sim_after_learn       3
% 2.08/1.03  --inst_sel_renew                        solver
% 2.08/1.03  --inst_lit_activity_flag                true
% 2.08/1.03  --inst_restr_to_given                   false
% 2.08/1.03  --inst_activity_threshold               500
% 2.08/1.03  --inst_out_proof                        true
% 2.08/1.03  
% 2.08/1.03  ------ Resolution Options
% 2.08/1.03  
% 2.08/1.03  --resolution_flag                       true
% 2.08/1.03  --res_lit_sel                           adaptive
% 2.08/1.03  --res_lit_sel_side                      none
% 2.08/1.03  --res_ordering                          kbo
% 2.08/1.03  --res_to_prop_solver                    active
% 2.08/1.03  --res_prop_simpl_new                    false
% 2.08/1.03  --res_prop_simpl_given                  true
% 2.08/1.03  --res_passive_queue_type                priority_queues
% 2.08/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.08/1.03  --res_passive_queues_freq               [15;5]
% 2.08/1.03  --res_forward_subs                      full
% 2.08/1.03  --res_backward_subs                     full
% 2.08/1.03  --res_forward_subs_resolution           true
% 2.08/1.03  --res_backward_subs_resolution          true
% 2.08/1.03  --res_orphan_elimination                true
% 2.08/1.03  --res_time_limit                        2.
% 2.08/1.03  --res_out_proof                         true
% 2.08/1.03  
% 2.08/1.03  ------ Superposition Options
% 2.08/1.03  
% 2.08/1.03  --superposition_flag                    true
% 2.08/1.03  --sup_passive_queue_type                priority_queues
% 2.08/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.08/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.08/1.03  --demod_completeness_check              fast
% 2.08/1.03  --demod_use_ground                      true
% 2.08/1.03  --sup_to_prop_solver                    passive
% 2.08/1.03  --sup_prop_simpl_new                    true
% 2.08/1.03  --sup_prop_simpl_given                  true
% 2.08/1.03  --sup_fun_splitting                     false
% 2.08/1.03  --sup_smt_interval                      50000
% 2.08/1.03  
% 2.08/1.03  ------ Superposition Simplification Setup
% 2.08/1.03  
% 2.08/1.03  --sup_indices_passive                   []
% 2.08/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.08/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/1.03  --sup_full_bw                           [BwDemod]
% 2.08/1.03  --sup_immed_triv                        [TrivRules]
% 2.08/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.08/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/1.03  --sup_immed_bw_main                     []
% 2.08/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.08/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/1.03  
% 2.08/1.03  ------ Combination Options
% 2.08/1.03  
% 2.08/1.03  --comb_res_mult                         3
% 2.08/1.03  --comb_sup_mult                         2
% 2.08/1.03  --comb_inst_mult                        10
% 2.08/1.03  
% 2.08/1.03  ------ Debug Options
% 2.08/1.03  
% 2.08/1.03  --dbg_backtrace                         false
% 2.08/1.03  --dbg_dump_prop_clauses                 false
% 2.08/1.03  --dbg_dump_prop_clauses_file            -
% 2.08/1.03  --dbg_out_stat                          false
% 2.08/1.03  ------ Parsing...
% 2.08/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.08/1.03  
% 2.08/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.08/1.03  
% 2.08/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.08/1.03  
% 2.08/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.08/1.03  ------ Proving...
% 2.08/1.03  ------ Problem Properties 
% 2.08/1.03  
% 2.08/1.03  
% 2.08/1.03  clauses                                 21
% 2.08/1.03  conjectures                             2
% 2.08/1.03  EPR                                     7
% 2.08/1.03  Horn                                    16
% 2.08/1.03  unary                                   8
% 2.08/1.03  binary                                  6
% 2.08/1.03  lits                                    41
% 2.08/1.03  lits eq                                 6
% 2.08/1.03  fd_pure                                 0
% 2.08/1.03  fd_pseudo                               0
% 2.08/1.03  fd_cond                                 1
% 2.08/1.03  fd_pseudo_cond                          1
% 2.08/1.03  AC symbols                              0
% 2.08/1.03  
% 2.08/1.03  ------ Schedule dynamic 5 is on 
% 2.08/1.03  
% 2.08/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.08/1.03  
% 2.08/1.03  
% 2.08/1.03  ------ 
% 2.08/1.03  Current options:
% 2.08/1.03  ------ 
% 2.08/1.03  
% 2.08/1.03  ------ Input Options
% 2.08/1.03  
% 2.08/1.03  --out_options                           all
% 2.08/1.03  --tptp_safe_out                         true
% 2.08/1.03  --problem_path                          ""
% 2.08/1.03  --include_path                          ""
% 2.08/1.03  --clausifier                            res/vclausify_rel
% 2.08/1.03  --clausifier_options                    --mode clausify
% 2.08/1.03  --stdin                                 false
% 2.08/1.03  --stats_out                             all
% 2.08/1.03  
% 2.08/1.03  ------ General Options
% 2.08/1.03  
% 2.08/1.03  --fof                                   false
% 2.08/1.03  --time_out_real                         305.
% 2.08/1.03  --time_out_virtual                      -1.
% 2.08/1.03  --symbol_type_check                     false
% 2.08/1.03  --clausify_out                          false
% 2.08/1.03  --sig_cnt_out                           false
% 2.08/1.03  --trig_cnt_out                          false
% 2.08/1.03  --trig_cnt_out_tolerance                1.
% 2.08/1.03  --trig_cnt_out_sk_spl                   false
% 2.08/1.03  --abstr_cl_out                          false
% 2.08/1.03  
% 2.08/1.03  ------ Global Options
% 2.08/1.03  
% 2.08/1.03  --schedule                              default
% 2.08/1.03  --add_important_lit                     false
% 2.08/1.03  --prop_solver_per_cl                    1000
% 2.08/1.03  --min_unsat_core                        false
% 2.08/1.03  --soft_assumptions                      false
% 2.08/1.03  --soft_lemma_size                       3
% 2.08/1.03  --prop_impl_unit_size                   0
% 2.08/1.03  --prop_impl_unit                        []
% 2.08/1.03  --share_sel_clauses                     true
% 2.08/1.03  --reset_solvers                         false
% 2.08/1.03  --bc_imp_inh                            [conj_cone]
% 2.08/1.03  --conj_cone_tolerance                   3.
% 2.08/1.03  --extra_neg_conj                        none
% 2.08/1.03  --large_theory_mode                     true
% 2.08/1.03  --prolific_symb_bound                   200
% 2.08/1.03  --lt_threshold                          2000
% 2.08/1.03  --clause_weak_htbl                      true
% 2.08/1.03  --gc_record_bc_elim                     false
% 2.08/1.03  
% 2.08/1.03  ------ Preprocessing Options
% 2.08/1.03  
% 2.08/1.03  --preprocessing_flag                    true
% 2.08/1.03  --time_out_prep_mult                    0.1
% 2.08/1.03  --splitting_mode                        input
% 2.08/1.03  --splitting_grd                         true
% 2.08/1.03  --splitting_cvd                         false
% 2.08/1.03  --splitting_cvd_svl                     false
% 2.08/1.03  --splitting_nvd                         32
% 2.08/1.03  --sub_typing                            true
% 2.08/1.03  --prep_gs_sim                           true
% 2.08/1.03  --prep_unflatten                        true
% 2.08/1.03  --prep_res_sim                          true
% 2.08/1.03  --prep_upred                            true
% 2.08/1.03  --prep_sem_filter                       exhaustive
% 2.08/1.03  --prep_sem_filter_out                   false
% 2.08/1.03  --pred_elim                             true
% 2.08/1.03  --res_sim_input                         true
% 2.08/1.03  --eq_ax_congr_red                       true
% 2.08/1.03  --pure_diseq_elim                       true
% 2.08/1.03  --brand_transform                       false
% 2.08/1.03  --non_eq_to_eq                          false
% 2.08/1.03  --prep_def_merge                        true
% 2.08/1.03  --prep_def_merge_prop_impl              false
% 2.08/1.03  --prep_def_merge_mbd                    true
% 2.08/1.03  --prep_def_merge_tr_red                 false
% 2.08/1.03  --prep_def_merge_tr_cl                  false
% 2.08/1.03  --smt_preprocessing                     true
% 2.08/1.03  --smt_ac_axioms                         fast
% 2.08/1.03  --preprocessed_out                      false
% 2.08/1.03  --preprocessed_stats                    false
% 2.08/1.03  
% 2.08/1.03  ------ Abstraction refinement Options
% 2.08/1.03  
% 2.08/1.03  --abstr_ref                             []
% 2.08/1.03  --abstr_ref_prep                        false
% 2.08/1.03  --abstr_ref_until_sat                   false
% 2.08/1.03  --abstr_ref_sig_restrict                funpre
% 2.08/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.08/1.03  --abstr_ref_under                       []
% 2.08/1.03  
% 2.08/1.03  ------ SAT Options
% 2.08/1.03  
% 2.08/1.03  --sat_mode                              false
% 2.08/1.03  --sat_fm_restart_options                ""
% 2.08/1.03  --sat_gr_def                            false
% 2.08/1.03  --sat_epr_types                         true
% 2.08/1.03  --sat_non_cyclic_types                  false
% 2.08/1.03  --sat_finite_models                     false
% 2.08/1.03  --sat_fm_lemmas                         false
% 2.08/1.03  --sat_fm_prep                           false
% 2.08/1.03  --sat_fm_uc_incr                        true
% 2.08/1.03  --sat_out_model                         small
% 2.08/1.03  --sat_out_clauses                       false
% 2.08/1.03  
% 2.08/1.03  ------ QBF Options
% 2.08/1.03  
% 2.08/1.03  --qbf_mode                              false
% 2.08/1.03  --qbf_elim_univ                         false
% 2.08/1.03  --qbf_dom_inst                          none
% 2.08/1.03  --qbf_dom_pre_inst                      false
% 2.08/1.03  --qbf_sk_in                             false
% 2.08/1.03  --qbf_pred_elim                         true
% 2.08/1.03  --qbf_split                             512
% 2.08/1.03  
% 2.08/1.03  ------ BMC1 Options
% 2.08/1.03  
% 2.08/1.03  --bmc1_incremental                      false
% 2.08/1.03  --bmc1_axioms                           reachable_all
% 2.08/1.03  --bmc1_min_bound                        0
% 2.08/1.03  --bmc1_max_bound                        -1
% 2.08/1.03  --bmc1_max_bound_default                -1
% 2.08/1.03  --bmc1_symbol_reachability              true
% 2.08/1.03  --bmc1_property_lemmas                  false
% 2.08/1.03  --bmc1_k_induction                      false
% 2.08/1.03  --bmc1_non_equiv_states                 false
% 2.08/1.03  --bmc1_deadlock                         false
% 2.08/1.03  --bmc1_ucm                              false
% 2.08/1.03  --bmc1_add_unsat_core                   none
% 2.08/1.03  --bmc1_unsat_core_children              false
% 2.08/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.08/1.03  --bmc1_out_stat                         full
% 2.08/1.03  --bmc1_ground_init                      false
% 2.08/1.03  --bmc1_pre_inst_next_state              false
% 2.08/1.03  --bmc1_pre_inst_state                   false
% 2.08/1.03  --bmc1_pre_inst_reach_state             false
% 2.08/1.03  --bmc1_out_unsat_core                   false
% 2.08/1.03  --bmc1_aig_witness_out                  false
% 2.08/1.03  --bmc1_verbose                          false
% 2.08/1.03  --bmc1_dump_clauses_tptp                false
% 2.08/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.08/1.03  --bmc1_dump_file                        -
% 2.08/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.08/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.08/1.03  --bmc1_ucm_extend_mode                  1
% 2.08/1.03  --bmc1_ucm_init_mode                    2
% 2.08/1.03  --bmc1_ucm_cone_mode                    none
% 2.08/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.08/1.03  --bmc1_ucm_relax_model                  4
% 2.08/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.08/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.08/1.03  --bmc1_ucm_layered_model                none
% 2.08/1.03  --bmc1_ucm_max_lemma_size               10
% 2.08/1.03  
% 2.08/1.03  ------ AIG Options
% 2.08/1.03  
% 2.08/1.03  --aig_mode                              false
% 2.08/1.03  
% 2.08/1.03  ------ Instantiation Options
% 2.08/1.03  
% 2.08/1.03  --instantiation_flag                    true
% 2.08/1.03  --inst_sos_flag                         false
% 2.08/1.03  --inst_sos_phase                        true
% 2.08/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.08/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.08/1.03  --inst_lit_sel_side                     none
% 2.08/1.03  --inst_solver_per_active                1400
% 2.08/1.03  --inst_solver_calls_frac                1.
% 2.08/1.03  --inst_passive_queue_type               priority_queues
% 2.08/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.08/1.03  --inst_passive_queues_freq              [25;2]
% 2.08/1.03  --inst_dismatching                      true
% 2.08/1.03  --inst_eager_unprocessed_to_passive     true
% 2.08/1.03  --inst_prop_sim_given                   true
% 2.08/1.03  --inst_prop_sim_new                     false
% 2.08/1.03  --inst_subs_new                         false
% 2.08/1.03  --inst_eq_res_simp                      false
% 2.08/1.03  --inst_subs_given                       false
% 2.08/1.03  --inst_orphan_elimination               true
% 2.08/1.03  --inst_learning_loop_flag               true
% 2.08/1.03  --inst_learning_start                   3000
% 2.08/1.03  --inst_learning_factor                  2
% 2.08/1.03  --inst_start_prop_sim_after_learn       3
% 2.08/1.03  --inst_sel_renew                        solver
% 2.08/1.03  --inst_lit_activity_flag                true
% 2.08/1.03  --inst_restr_to_given                   false
% 2.08/1.03  --inst_activity_threshold               500
% 2.08/1.03  --inst_out_proof                        true
% 2.08/1.03  
% 2.08/1.03  ------ Resolution Options
% 2.08/1.03  
% 2.08/1.03  --resolution_flag                       false
% 2.08/1.03  --res_lit_sel                           adaptive
% 2.08/1.03  --res_lit_sel_side                      none
% 2.08/1.03  --res_ordering                          kbo
% 2.08/1.03  --res_to_prop_solver                    active
% 2.08/1.03  --res_prop_simpl_new                    false
% 2.08/1.03  --res_prop_simpl_given                  true
% 2.08/1.03  --res_passive_queue_type                priority_queues
% 2.08/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.08/1.03  --res_passive_queues_freq               [15;5]
% 2.08/1.03  --res_forward_subs                      full
% 2.08/1.03  --res_backward_subs                     full
% 2.08/1.03  --res_forward_subs_resolution           true
% 2.08/1.03  --res_backward_subs_resolution          true
% 2.08/1.03  --res_orphan_elimination                true
% 2.08/1.03  --res_time_limit                        2.
% 2.08/1.03  --res_out_proof                         true
% 2.08/1.03  
% 2.08/1.03  ------ Superposition Options
% 2.08/1.03  
% 2.08/1.03  --superposition_flag                    true
% 2.08/1.03  --sup_passive_queue_type                priority_queues
% 2.08/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.08/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.08/1.03  --demod_completeness_check              fast
% 2.08/1.03  --demod_use_ground                      true
% 2.08/1.03  --sup_to_prop_solver                    passive
% 2.08/1.03  --sup_prop_simpl_new                    true
% 2.08/1.03  --sup_prop_simpl_given                  true
% 2.08/1.03  --sup_fun_splitting                     false
% 2.08/1.03  --sup_smt_interval                      50000
% 2.08/1.03  
% 2.08/1.03  ------ Superposition Simplification Setup
% 2.08/1.03  
% 2.08/1.03  --sup_indices_passive                   []
% 2.08/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.08/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/1.03  --sup_full_bw                           [BwDemod]
% 2.08/1.03  --sup_immed_triv                        [TrivRules]
% 2.08/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.08/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/1.03  --sup_immed_bw_main                     []
% 2.08/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.08/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/1.03  
% 2.08/1.03  ------ Combination Options
% 2.08/1.03  
% 2.08/1.03  --comb_res_mult                         3
% 2.08/1.03  --comb_sup_mult                         2
% 2.08/1.03  --comb_inst_mult                        10
% 2.08/1.03  
% 2.08/1.03  ------ Debug Options
% 2.08/1.03  
% 2.08/1.03  --dbg_backtrace                         false
% 2.08/1.03  --dbg_dump_prop_clauses                 false
% 2.08/1.03  --dbg_dump_prop_clauses_file            -
% 2.08/1.03  --dbg_out_stat                          false
% 2.08/1.03  
% 2.08/1.03  
% 2.08/1.03  
% 2.08/1.03  
% 2.08/1.03  ------ Proving...
% 2.08/1.03  
% 2.08/1.03  
% 2.08/1.03  % SZS status Theorem for theBenchmark.p
% 2.08/1.03  
% 2.08/1.03   Resolution empty clause
% 2.08/1.03  
% 2.08/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.08/1.03  
% 2.08/1.03  fof(f15,conjecture,(
% 2.08/1.03    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 2.08/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.03  
% 2.08/1.03  fof(f16,negated_conjecture,(
% 2.08/1.03    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 2.08/1.03    inference(negated_conjecture,[],[f15])).
% 2.08/1.03  
% 2.08/1.03  fof(f28,plain,(
% 2.08/1.03    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 2.08/1.03    inference(ennf_transformation,[],[f16])).
% 2.08/1.03  
% 2.08/1.03  fof(f29,plain,(
% 2.08/1.03    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 2.08/1.03    inference(flattening,[],[f28])).
% 2.08/1.03  
% 2.08/1.03  fof(f44,plain,(
% 2.08/1.03    ( ! [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) => (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,sK4),X0) & m1_subset_1(sK4,X0))) )),
% 2.08/1.03    introduced(choice_axiom,[])).
% 2.08/1.03  
% 2.08/1.03  fof(f43,plain,(
% 2.08/1.03    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK3) & v1_subset_1(k6_domain_1(sK3,X1),sK3) & m1_subset_1(X1,sK3)) & ~v1_xboole_0(sK3))),
% 2.08/1.03    introduced(choice_axiom,[])).
% 2.08/1.03  
% 2.08/1.03  fof(f45,plain,(
% 2.08/1.03    (v1_zfmisc_1(sK3) & v1_subset_1(k6_domain_1(sK3,sK4),sK3) & m1_subset_1(sK4,sK3)) & ~v1_xboole_0(sK3)),
% 2.08/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f29,f44,f43])).
% 2.08/1.03  
% 2.08/1.03  fof(f68,plain,(
% 2.08/1.03    m1_subset_1(sK4,sK3)),
% 2.08/1.03    inference(cnf_transformation,[],[f45])).
% 2.08/1.03  
% 2.08/1.03  fof(f13,axiom,(
% 2.08/1.03    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.08/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.03  
% 2.08/1.03  fof(f24,plain,(
% 2.08/1.03    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.08/1.03    inference(ennf_transformation,[],[f13])).
% 2.08/1.03  
% 2.08/1.03  fof(f25,plain,(
% 2.08/1.03    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.08/1.03    inference(flattening,[],[f24])).
% 2.08/1.03  
% 2.08/1.03  fof(f65,plain,(
% 2.08/1.03    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.08/1.03    inference(cnf_transformation,[],[f25])).
% 2.08/1.03  
% 2.08/1.03  fof(f67,plain,(
% 2.08/1.03    ~v1_xboole_0(sK3)),
% 2.08/1.03    inference(cnf_transformation,[],[f45])).
% 2.08/1.03  
% 2.08/1.03  fof(f12,axiom,(
% 2.08/1.03    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.08/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.03  
% 2.08/1.03  fof(f22,plain,(
% 2.08/1.03    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.08/1.03    inference(ennf_transformation,[],[f12])).
% 2.08/1.03  
% 2.08/1.03  fof(f23,plain,(
% 2.08/1.03    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.08/1.03    inference(flattening,[],[f22])).
% 2.08/1.03  
% 2.08/1.03  fof(f64,plain,(
% 2.08/1.03    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.08/1.03    inference(cnf_transformation,[],[f23])).
% 2.08/1.03  
% 2.08/1.03  fof(f10,axiom,(
% 2.08/1.03    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.08/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.03  
% 2.08/1.03  fof(f42,plain,(
% 2.08/1.03    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.08/1.03    inference(nnf_transformation,[],[f10])).
% 2.08/1.03  
% 2.08/1.03  fof(f61,plain,(
% 2.08/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.08/1.03    inference(cnf_transformation,[],[f42])).
% 2.08/1.03  
% 2.08/1.03  fof(f14,axiom,(
% 2.08/1.03    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 2.08/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.03  
% 2.08/1.03  fof(f26,plain,(
% 2.08/1.03    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 2.08/1.03    inference(ennf_transformation,[],[f14])).
% 2.08/1.03  
% 2.08/1.03  fof(f27,plain,(
% 2.08/1.03    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.08/1.03    inference(flattening,[],[f26])).
% 2.08/1.03  
% 2.08/1.03  fof(f66,plain,(
% 2.08/1.03    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.08/1.03    inference(cnf_transformation,[],[f27])).
% 2.08/1.03  
% 2.08/1.03  fof(f70,plain,(
% 2.08/1.03    v1_zfmisc_1(sK3)),
% 2.08/1.03    inference(cnf_transformation,[],[f45])).
% 2.08/1.03  
% 2.08/1.03  fof(f9,axiom,(
% 2.08/1.03    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.08/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.03  
% 2.08/1.03  fof(f40,plain,(
% 2.08/1.03    ! [X0] : (? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (~v1_subset_1(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(X0))))),
% 2.08/1.03    introduced(choice_axiom,[])).
% 2.08/1.03  
% 2.08/1.03  fof(f41,plain,(
% 2.08/1.03    ! [X0] : (~v1_subset_1(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)))),
% 2.08/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f40])).
% 2.08/1.03  
% 2.08/1.03  fof(f59,plain,(
% 2.08/1.03    ( ! [X0] : (m1_subset_1(sK2(X0),k1_zfmisc_1(X0))) )),
% 2.08/1.03    inference(cnf_transformation,[],[f41])).
% 2.08/1.03  
% 2.08/1.03  fof(f8,axiom,(
% 2.08/1.03    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_subset_1(X1,X0) => ~v1_xboole_0(X1))))),
% 2.08/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.03  
% 2.08/1.03  fof(f18,plain,(
% 2.08/1.03    ! [X0] : (! [X1] : ((~v1_xboole_0(X1) | v1_subset_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 2.08/1.03    inference(ennf_transformation,[],[f8])).
% 2.08/1.03  
% 2.08/1.03  fof(f19,plain,(
% 2.08/1.03    ! [X0] : (! [X1] : (~v1_xboole_0(X1) | v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 2.08/1.03    inference(flattening,[],[f18])).
% 2.08/1.03  
% 2.08/1.03  fof(f58,plain,(
% 2.08/1.03    ( ! [X0,X1] : (~v1_xboole_0(X1) | v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 2.08/1.03    inference(cnf_transformation,[],[f19])).
% 2.08/1.03  
% 2.08/1.03  fof(f62,plain,(
% 2.08/1.03    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.08/1.03    inference(cnf_transformation,[],[f42])).
% 2.08/1.03  
% 2.08/1.03  fof(f60,plain,(
% 2.08/1.03    ( ! [X0] : (~v1_subset_1(sK2(X0),X0)) )),
% 2.08/1.03    inference(cnf_transformation,[],[f41])).
% 2.08/1.03  
% 2.08/1.03  fof(f69,plain,(
% 2.08/1.03    v1_subset_1(k6_domain_1(sK3,sK4),sK3)),
% 2.08/1.03    inference(cnf_transformation,[],[f45])).
% 2.08/1.03  
% 2.08/1.03  fof(f2,axiom,(
% 2.08/1.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.08/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.03  
% 2.08/1.03  fof(f17,plain,(
% 2.08/1.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.08/1.03    inference(ennf_transformation,[],[f2])).
% 2.08/1.03  
% 2.08/1.03  fof(f34,plain,(
% 2.08/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.08/1.03    inference(nnf_transformation,[],[f17])).
% 2.08/1.03  
% 2.08/1.03  fof(f35,plain,(
% 2.08/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.08/1.03    inference(rectify,[],[f34])).
% 2.08/1.03  
% 2.08/1.03  fof(f36,plain,(
% 2.08/1.03    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 2.08/1.03    introduced(choice_axiom,[])).
% 2.08/1.03  
% 2.08/1.03  fof(f37,plain,(
% 2.08/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.08/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).
% 2.08/1.03  
% 2.08/1.03  fof(f49,plain,(
% 2.08/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 2.08/1.03    inference(cnf_transformation,[],[f37])).
% 2.08/1.03  
% 2.08/1.03  fof(f1,axiom,(
% 2.08/1.03    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.08/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.03  
% 2.08/1.03  fof(f30,plain,(
% 2.08/1.03    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.08/1.03    inference(nnf_transformation,[],[f1])).
% 2.08/1.03  
% 2.08/1.03  fof(f31,plain,(
% 2.08/1.03    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.08/1.03    inference(rectify,[],[f30])).
% 2.08/1.03  
% 2.08/1.03  fof(f32,plain,(
% 2.08/1.03    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.08/1.03    introduced(choice_axiom,[])).
% 2.08/1.03  
% 2.08/1.03  fof(f33,plain,(
% 2.08/1.03    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.08/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 2.08/1.03  
% 2.08/1.03  fof(f46,plain,(
% 2.08/1.03    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.08/1.03    inference(cnf_transformation,[],[f33])).
% 2.08/1.03  
% 2.08/1.03  fof(f7,axiom,(
% 2.08/1.03    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.08/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.03  
% 2.08/1.03  fof(f57,plain,(
% 2.08/1.03    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.08/1.03    inference(cnf_transformation,[],[f7])).
% 2.08/1.03  
% 2.08/1.03  fof(f3,axiom,(
% 2.08/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.08/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.03  
% 2.08/1.03  fof(f38,plain,(
% 2.08/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.08/1.03    inference(nnf_transformation,[],[f3])).
% 2.08/1.03  
% 2.08/1.03  fof(f39,plain,(
% 2.08/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.08/1.03    inference(flattening,[],[f38])).
% 2.08/1.03  
% 2.08/1.03  fof(f53,plain,(
% 2.08/1.03    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.08/1.03    inference(cnf_transformation,[],[f39])).
% 2.08/1.03  
% 2.08/1.03  fof(f4,axiom,(
% 2.08/1.03    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.08/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.03  
% 2.08/1.03  fof(f54,plain,(
% 2.08/1.03    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.08/1.03    inference(cnf_transformation,[],[f4])).
% 2.08/1.03  
% 2.08/1.03  fof(f5,axiom,(
% 2.08/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.08/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.03  
% 2.08/1.03  fof(f55,plain,(
% 2.08/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.08/1.03    inference(cnf_transformation,[],[f5])).
% 2.08/1.03  
% 2.08/1.03  fof(f71,plain,(
% 2.08/1.03    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 2.08/1.03    inference(definition_unfolding,[],[f54,f55])).
% 2.08/1.03  
% 2.08/1.03  fof(f6,axiom,(
% 2.08/1.03    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 2.08/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/1.03  
% 2.08/1.03  fof(f56,plain,(
% 2.08/1.03    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 2.08/1.03    inference(cnf_transformation,[],[f6])).
% 2.08/1.03  
% 2.08/1.03  fof(f72,plain,(
% 2.08/1.03    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(k1_tarski(X0),k4_xboole_0(X1,k1_tarski(X0)))) )),
% 2.08/1.03    inference(definition_unfolding,[],[f56,f55])).
% 2.08/1.03  
% 2.08/1.03  cnf(c_22,negated_conjecture,
% 2.08/1.03      ( m1_subset_1(sK4,sK3) ),
% 2.08/1.03      inference(cnf_transformation,[],[f68]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_939,plain,
% 2.08/1.03      ( m1_subset_1(sK4,sK3) = iProver_top ),
% 2.08/1.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_18,plain,
% 2.08/1.03      ( ~ m1_subset_1(X0,X1)
% 2.08/1.03      | v1_xboole_0(X1)
% 2.08/1.03      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 2.08/1.03      inference(cnf_transformation,[],[f65]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_940,plain,
% 2.08/1.03      ( k6_domain_1(X0,X1) = k1_tarski(X1)
% 2.08/1.03      | m1_subset_1(X1,X0) != iProver_top
% 2.08/1.03      | v1_xboole_0(X0) = iProver_top ),
% 2.08/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_1790,plain,
% 2.08/1.03      ( k6_domain_1(sK3,sK4) = k1_tarski(sK4)
% 2.08/1.03      | v1_xboole_0(sK3) = iProver_top ),
% 2.08/1.03      inference(superposition,[status(thm)],[c_939,c_940]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_23,negated_conjecture,
% 2.08/1.03      ( ~ v1_xboole_0(sK3) ),
% 2.08/1.03      inference(cnf_transformation,[],[f67]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_1110,plain,
% 2.08/1.03      ( ~ m1_subset_1(sK4,sK3)
% 2.08/1.03      | v1_xboole_0(sK3)
% 2.08/1.03      | k6_domain_1(sK3,sK4) = k1_tarski(sK4) ),
% 2.08/1.03      inference(instantiation,[status(thm)],[c_18]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_2018,plain,
% 2.08/1.03      ( k6_domain_1(sK3,sK4) = k1_tarski(sK4) ),
% 2.08/1.03      inference(global_propositional_subsumption,
% 2.08/1.03                [status(thm)],
% 2.08/1.03                [c_1790,c_23,c_22,c_1110]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_17,plain,
% 2.08/1.03      ( ~ m1_subset_1(X0,X1)
% 2.08/1.03      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 2.08/1.03      | v1_xboole_0(X1) ),
% 2.08/1.03      inference(cnf_transformation,[],[f64]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_941,plain,
% 2.08/1.03      ( m1_subset_1(X0,X1) != iProver_top
% 2.08/1.03      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
% 2.08/1.03      | v1_xboole_0(X1) = iProver_top ),
% 2.08/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_2348,plain,
% 2.08/1.03      ( m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(sK3)) = iProver_top
% 2.08/1.03      | m1_subset_1(sK4,sK3) != iProver_top
% 2.08/1.03      | v1_xboole_0(sK3) = iProver_top ),
% 2.08/1.03      inference(superposition,[status(thm)],[c_2018,c_941]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_24,plain,
% 2.08/1.03      ( v1_xboole_0(sK3) != iProver_top ),
% 2.08/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_25,plain,
% 2.08/1.03      ( m1_subset_1(sK4,sK3) = iProver_top ),
% 2.08/1.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_2625,plain,
% 2.08/1.03      ( m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(sK3)) = iProver_top ),
% 2.08/1.03      inference(global_propositional_subsumption,
% 2.08/1.03                [status(thm)],
% 2.08/1.03                [c_2348,c_24,c_25]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_15,plain,
% 2.08/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.08/1.03      inference(cnf_transformation,[],[f61]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_943,plain,
% 2.08/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.08/1.03      | r1_tarski(X0,X1) = iProver_top ),
% 2.08/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_2630,plain,
% 2.08/1.03      ( r1_tarski(k1_tarski(sK4),sK3) = iProver_top ),
% 2.08/1.03      inference(superposition,[status(thm)],[c_2625,c_943]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_19,plain,
% 2.08/1.03      ( ~ r1_tarski(X0,X1)
% 2.08/1.03      | ~ v1_zfmisc_1(X1)
% 2.08/1.03      | v1_xboole_0(X0)
% 2.08/1.03      | v1_xboole_0(X1)
% 2.08/1.03      | X1 = X0 ),
% 2.08/1.03      inference(cnf_transformation,[],[f66]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_20,negated_conjecture,
% 2.08/1.03      ( v1_zfmisc_1(sK3) ),
% 2.08/1.03      inference(cnf_transformation,[],[f70]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_305,plain,
% 2.08/1.03      ( ~ r1_tarski(X0,X1)
% 2.08/1.03      | v1_xboole_0(X0)
% 2.08/1.03      | v1_xboole_0(X1)
% 2.08/1.03      | X1 = X0
% 2.08/1.03      | sK3 != X1 ),
% 2.08/1.03      inference(resolution_lifted,[status(thm)],[c_19,c_20]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_306,plain,
% 2.08/1.03      ( ~ r1_tarski(X0,sK3) | v1_xboole_0(X0) | v1_xboole_0(sK3) | sK3 = X0 ),
% 2.08/1.03      inference(unflattening,[status(thm)],[c_305]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_308,plain,
% 2.08/1.03      ( v1_xboole_0(X0) | ~ r1_tarski(X0,sK3) | sK3 = X0 ),
% 2.08/1.03      inference(global_propositional_subsumption,[status(thm)],[c_306,c_23]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_309,plain,
% 2.08/1.03      ( ~ r1_tarski(X0,sK3) | v1_xboole_0(X0) | sK3 = X0 ),
% 2.08/1.03      inference(renaming,[status(thm)],[c_308]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_936,plain,
% 2.08/1.03      ( sK3 = X0
% 2.08/1.03      | r1_tarski(X0,sK3) != iProver_top
% 2.08/1.03      | v1_xboole_0(X0) = iProver_top ),
% 2.08/1.03      inference(predicate_to_equality,[status(thm)],[c_309]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_2753,plain,
% 2.08/1.03      ( k1_tarski(sK4) = sK3 | v1_xboole_0(k1_tarski(sK4)) = iProver_top ),
% 2.08/1.03      inference(superposition,[status(thm)],[c_2630,c_936]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_13,plain,
% 2.08/1.03      ( m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ),
% 2.08/1.03      inference(cnf_transformation,[],[f59]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_945,plain,
% 2.08/1.03      ( m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.08/1.03      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_1632,plain,
% 2.08/1.03      ( r1_tarski(sK2(X0),X0) = iProver_top ),
% 2.08/1.03      inference(superposition,[status(thm)],[c_945,c_943]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_1711,plain,
% 2.08/1.03      ( sK2(sK3) = sK3 | v1_xboole_0(sK2(sK3)) = iProver_top ),
% 2.08/1.03      inference(superposition,[status(thm)],[c_1632,c_936]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_11,plain,
% 2.08/1.03      ( v1_subset_1(X0,X1)
% 2.08/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.08/1.03      | ~ v1_xboole_0(X0)
% 2.08/1.03      | v1_xboole_0(X1) ),
% 2.08/1.03      inference(cnf_transformation,[],[f58]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_14,plain,
% 2.08/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.08/1.03      inference(cnf_transformation,[],[f62]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_167,plain,
% 2.08/1.03      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.08/1.03      inference(prop_impl,[status(thm)],[c_14]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_168,plain,
% 2.08/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.08/1.03      inference(renaming,[status(thm)],[c_167]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_203,plain,
% 2.08/1.03      ( v1_subset_1(X0,X1)
% 2.08/1.03      | ~ r1_tarski(X0,X1)
% 2.08/1.03      | ~ v1_xboole_0(X0)
% 2.08/1.03      | v1_xboole_0(X1) ),
% 2.08/1.03      inference(bin_hyper_res,[status(thm)],[c_11,c_168]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_12,plain,
% 2.08/1.03      ( ~ v1_subset_1(sK2(X0),X0) ),
% 2.08/1.03      inference(cnf_transformation,[],[f60]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_280,plain,
% 2.08/1.03      ( ~ r1_tarski(X0,X1)
% 2.08/1.03      | ~ v1_xboole_0(X0)
% 2.08/1.03      | v1_xboole_0(X1)
% 2.08/1.03      | X2 != X1
% 2.08/1.03      | sK2(X2) != X0 ),
% 2.08/1.03      inference(resolution_lifted,[status(thm)],[c_203,c_12]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_281,plain,
% 2.08/1.03      ( ~ r1_tarski(sK2(X0),X0) | v1_xboole_0(X0) | ~ v1_xboole_0(sK2(X0)) ),
% 2.08/1.03      inference(unflattening,[status(thm)],[c_280]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_282,plain,
% 2.08/1.03      ( r1_tarski(sK2(X0),X0) != iProver_top
% 2.08/1.03      | v1_xboole_0(X0) = iProver_top
% 2.08/1.03      | v1_xboole_0(sK2(X0)) != iProver_top ),
% 2.08/1.03      inference(predicate_to_equality,[status(thm)],[c_281]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_284,plain,
% 2.08/1.03      ( r1_tarski(sK2(sK3),sK3) != iProver_top
% 2.08/1.03      | v1_xboole_0(sK2(sK3)) != iProver_top
% 2.08/1.03      | v1_xboole_0(sK3) = iProver_top ),
% 2.08/1.03      inference(instantiation,[status(thm)],[c_282]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_1641,plain,
% 2.08/1.03      ( r1_tarski(sK2(sK3),sK3) = iProver_top ),
% 2.08/1.03      inference(instantiation,[status(thm)],[c_1632]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_1725,plain,
% 2.08/1.03      ( sK2(sK3) = sK3 ),
% 2.08/1.03      inference(global_propositional_subsumption,
% 2.08/1.03                [status(thm)],
% 2.08/1.03                [c_1711,c_24,c_284,c_1641]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_21,negated_conjecture,
% 2.08/1.03      ( v1_subset_1(k6_domain_1(sK3,sK4),sK3) ),
% 2.08/1.03      inference(cnf_transformation,[],[f69]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_295,plain,
% 2.08/1.03      ( k6_domain_1(sK3,sK4) != sK2(X0) | sK3 != X0 ),
% 2.08/1.03      inference(resolution_lifted,[status(thm)],[c_12,c_21]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_296,plain,
% 2.08/1.03      ( k6_domain_1(sK3,sK4) != sK2(sK3) ),
% 2.08/1.03      inference(unflattening,[status(thm)],[c_295]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_1728,plain,
% 2.08/1.03      ( k6_domain_1(sK3,sK4) != sK3 ),
% 2.08/1.03      inference(demodulation,[status(thm)],[c_1725,c_296]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_2021,plain,
% 2.08/1.03      ( k1_tarski(sK4) != sK3 ),
% 2.08/1.03      inference(demodulation,[status(thm)],[c_2018,c_1728]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_2772,plain,
% 2.08/1.03      ( v1_xboole_0(k1_tarski(sK4)) = iProver_top ),
% 2.08/1.03      inference(global_propositional_subsumption,[status(thm)],[c_2753,c_2021]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_3,plain,
% 2.08/1.03      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 2.08/1.03      inference(cnf_transformation,[],[f49]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_950,plain,
% 2.08/1.03      ( r1_tarski(X0,X1) = iProver_top
% 2.08/1.03      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 2.08/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_1,plain,
% 2.08/1.03      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.08/1.03      inference(cnf_transformation,[],[f46]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_952,plain,
% 2.08/1.03      ( r2_hidden(X0,X1) != iProver_top | v1_xboole_0(X1) != iProver_top ),
% 2.08/1.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_1871,plain,
% 2.08/1.03      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 2.08/1.03      inference(superposition,[status(thm)],[c_950,c_952]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_10,plain,
% 2.08/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.08/1.03      inference(cnf_transformation,[],[f57]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_946,plain,
% 2.08/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.08/1.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_1631,plain,
% 2.08/1.03      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.08/1.03      inference(superposition,[status(thm)],[c_946,c_943]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_5,plain,
% 2.08/1.03      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.08/1.03      inference(cnf_transformation,[],[f53]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_948,plain,
% 2.08/1.03      ( X0 = X1
% 2.08/1.03      | r1_tarski(X1,X0) != iProver_top
% 2.08/1.03      | r1_tarski(X0,X1) != iProver_top ),
% 2.08/1.03      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_1978,plain,
% 2.08/1.03      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.08/1.03      inference(superposition,[status(thm)],[c_1631,c_948]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_2306,plain,
% 2.08/1.03      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.08/1.03      inference(superposition,[status(thm)],[c_1871,c_1978]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_6434,plain,
% 2.08/1.03      ( k1_tarski(sK4) = k1_xboole_0 ),
% 2.08/1.03      inference(superposition,[status(thm)],[c_2772,c_2306]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_8,plain,
% 2.08/1.03      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
% 2.08/1.03      inference(cnf_transformation,[],[f71]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_9,plain,
% 2.08/1.03      ( k5_xboole_0(k1_tarski(X0),k4_xboole_0(X1,k1_tarski(X0))) != k1_xboole_0 ),
% 2.08/1.03      inference(cnf_transformation,[],[f72]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_1323,plain,
% 2.08/1.03      ( k1_tarski(X0) != k1_xboole_0 ),
% 2.08/1.03      inference(superposition,[status(thm)],[c_8,c_9]) ).
% 2.08/1.03  
% 2.08/1.03  cnf(c_7412,plain,
% 2.08/1.03      ( $false ),
% 2.08/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_6434,c_1323]) ).
% 2.08/1.03  
% 2.08/1.03  
% 2.08/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.08/1.03  
% 2.08/1.03  ------                               Statistics
% 2.08/1.03  
% 2.08/1.03  ------ General
% 2.08/1.03  
% 2.08/1.03  abstr_ref_over_cycles:                  0
% 2.08/1.03  abstr_ref_under_cycles:                 0
% 2.08/1.03  gc_basic_clause_elim:                   0
% 2.08/1.03  forced_gc_time:                         0
% 2.08/1.03  parsing_time:                           0.007
% 2.08/1.03  unif_index_cands_time:                  0.
% 2.08/1.03  unif_index_add_time:                    0.
% 2.08/1.03  orderings_time:                         0.
% 2.08/1.03  out_proof_time:                         0.024
% 2.08/1.03  total_time:                             0.278
% 2.08/1.03  num_of_symbols:                         48
% 2.08/1.03  num_of_terms:                           5928
% 2.08/1.03  
% 2.08/1.03  ------ Preprocessing
% 2.08/1.03  
% 2.08/1.03  num_of_splits:                          0
% 2.08/1.03  num_of_split_atoms:                     0
% 2.08/1.03  num_of_reused_defs:                     0
% 2.08/1.03  num_eq_ax_congr_red:                    21
% 2.08/1.03  num_of_sem_filtered_clauses:            1
% 2.08/1.03  num_of_subtypes:                        0
% 2.08/1.03  monotx_restored_types:                  0
% 2.08/1.03  sat_num_of_epr_types:                   0
% 2.08/1.03  sat_num_of_non_cyclic_types:            0
% 2.08/1.03  sat_guarded_non_collapsed_types:        0
% 2.08/1.03  num_pure_diseq_elim:                    0
% 2.08/1.03  simp_replaced_by:                       0
% 2.08/1.03  res_preprocessed:                       107
% 2.08/1.03  prep_upred:                             0
% 2.08/1.03  prep_unflattend:                        4
% 2.08/1.03  smt_new_axioms:                         0
% 2.08/1.03  pred_elim_cands:                        4
% 2.08/1.03  pred_elim:                              2
% 2.08/1.03  pred_elim_cl:                           2
% 2.08/1.03  pred_elim_cycles:                       4
% 2.08/1.03  merged_defs:                            8
% 2.08/1.03  merged_defs_ncl:                        0
% 2.08/1.03  bin_hyper_res:                          9
% 2.08/1.03  prep_cycles:                            4
% 2.08/1.03  pred_elim_time:                         0.001
% 2.08/1.03  splitting_time:                         0.
% 2.08/1.03  sem_filter_time:                        0.
% 2.08/1.03  monotx_time:                            0.
% 2.08/1.03  subtype_inf_time:                       0.
% 2.08/1.03  
% 2.08/1.03  ------ Problem properties
% 2.08/1.03  
% 2.08/1.03  clauses:                                21
% 2.08/1.03  conjectures:                            2
% 2.08/1.03  epr:                                    7
% 2.08/1.03  horn:                                   16
% 2.08/1.03  ground:                                 3
% 2.08/1.03  unary:                                  8
% 2.08/1.03  binary:                                 6
% 2.08/1.03  lits:                                   41
% 2.08/1.03  lits_eq:                                6
% 2.08/1.03  fd_pure:                                0
% 2.08/1.03  fd_pseudo:                              0
% 2.08/1.03  fd_cond:                                1
% 2.08/1.03  fd_pseudo_cond:                         1
% 2.08/1.03  ac_symbols:                             0
% 2.08/1.03  
% 2.08/1.03  ------ Propositional Solver
% 2.08/1.03  
% 2.08/1.03  prop_solver_calls:                      29
% 2.08/1.03  prop_fast_solver_calls:                 719
% 2.08/1.03  smt_solver_calls:                       0
% 2.08/1.03  smt_fast_solver_calls:                  0
% 2.08/1.03  prop_num_of_clauses:                    2591
% 2.08/1.03  prop_preprocess_simplified:             6219
% 2.08/1.03  prop_fo_subsumed:                       17
% 2.08/1.03  prop_solver_time:                       0.
% 2.08/1.03  smt_solver_time:                        0.
% 2.08/1.03  smt_fast_solver_time:                   0.
% 2.08/1.03  prop_fast_solver_time:                  0.
% 2.08/1.03  prop_unsat_core_time:                   0.
% 2.08/1.03  
% 2.08/1.03  ------ QBF
% 2.08/1.03  
% 2.08/1.03  qbf_q_res:                              0
% 2.08/1.03  qbf_num_tautologies:                    0
% 2.08/1.03  qbf_prep_cycles:                        0
% 2.08/1.03  
% 2.08/1.03  ------ BMC1
% 2.08/1.03  
% 2.08/1.03  bmc1_current_bound:                     -1
% 2.08/1.03  bmc1_last_solved_bound:                 -1
% 2.08/1.03  bmc1_unsat_core_size:                   -1
% 2.08/1.03  bmc1_unsat_core_parents_size:           -1
% 2.08/1.03  bmc1_merge_next_fun:                    0
% 2.08/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.08/1.03  
% 2.08/1.03  ------ Instantiation
% 2.08/1.03  
% 2.08/1.03  inst_num_of_clauses:                    793
% 2.08/1.03  inst_num_in_passive:                    174
% 2.08/1.03  inst_num_in_active:                     380
% 2.08/1.03  inst_num_in_unprocessed:                239
% 2.08/1.03  inst_num_of_loops:                      520
% 2.08/1.03  inst_num_of_learning_restarts:          0
% 2.08/1.03  inst_num_moves_active_passive:          137
% 2.08/1.03  inst_lit_activity:                      0
% 2.08/1.03  inst_lit_activity_moves:                0
% 2.08/1.03  inst_num_tautologies:                   0
% 2.08/1.03  inst_num_prop_implied:                  0
% 2.08/1.03  inst_num_existing_simplified:           0
% 2.08/1.03  inst_num_eq_res_simplified:             0
% 2.08/1.03  inst_num_child_elim:                    0
% 2.08/1.03  inst_num_of_dismatching_blockings:      210
% 2.08/1.03  inst_num_of_non_proper_insts:           827
% 2.08/1.03  inst_num_of_duplicates:                 0
% 2.08/1.03  inst_inst_num_from_inst_to_res:         0
% 2.08/1.03  inst_dismatching_checking_time:         0.
% 2.08/1.03  
% 2.08/1.03  ------ Resolution
% 2.08/1.03  
% 2.08/1.03  res_num_of_clauses:                     0
% 2.08/1.03  res_num_in_passive:                     0
% 2.08/1.03  res_num_in_active:                      0
% 2.08/1.03  res_num_of_loops:                       111
% 2.08/1.03  res_forward_subset_subsumed:            50
% 2.08/1.03  res_backward_subset_subsumed:           0
% 2.08/1.03  res_forward_subsumed:                   0
% 2.08/1.03  res_backward_subsumed:                  0
% 2.08/1.03  res_forward_subsumption_resolution:     0
% 2.08/1.03  res_backward_subsumption_resolution:    0
% 2.08/1.03  res_clause_to_clause_subsumption:       686
% 2.08/1.03  res_orphan_elimination:                 0
% 2.08/1.03  res_tautology_del:                      72
% 2.08/1.03  res_num_eq_res_simplified:              0
% 2.08/1.03  res_num_sel_changes:                    0
% 2.08/1.03  res_moves_from_active_to_pass:          0
% 2.08/1.03  
% 2.08/1.03  ------ Superposition
% 2.08/1.03  
% 2.08/1.03  sup_time_total:                         0.
% 2.08/1.03  sup_time_generating:                    0.
% 2.08/1.03  sup_time_sim_full:                      0.
% 2.08/1.03  sup_time_sim_immed:                     0.
% 2.08/1.03  
% 2.08/1.03  sup_num_of_clauses:                     207
% 2.08/1.03  sup_num_in_active:                      100
% 2.08/1.03  sup_num_in_passive:                     107
% 2.08/1.03  sup_num_of_loops:                       103
% 2.08/1.03  sup_fw_superposition:                   170
% 2.08/1.03  sup_bw_superposition:                   146
% 2.08/1.03  sup_immediate_simplified:               77
% 2.08/1.03  sup_given_eliminated:                   1
% 2.08/1.03  comparisons_done:                       0
% 2.08/1.03  comparisons_avoided:                    46
% 2.08/1.03  
% 2.08/1.03  ------ Simplifications
% 2.08/1.03  
% 2.08/1.03  
% 2.08/1.03  sim_fw_subset_subsumed:                 41
% 2.08/1.03  sim_bw_subset_subsumed:                 0
% 2.08/1.03  sim_fw_subsumed:                        13
% 2.08/1.03  sim_bw_subsumed:                        5
% 2.08/1.03  sim_fw_subsumption_res:                 2
% 2.08/1.03  sim_bw_subsumption_res:                 0
% 2.08/1.03  sim_tautology_del:                      14
% 2.08/1.03  sim_eq_tautology_del:                   13
% 2.08/1.03  sim_eq_res_simp:                        0
% 2.08/1.03  sim_fw_demodulated:                     4
% 2.08/1.03  sim_bw_demodulated:                     5
% 2.08/1.03  sim_light_normalised:                   19
% 2.08/1.03  sim_joinable_taut:                      0
% 2.08/1.03  sim_joinable_simp:                      0
% 2.08/1.03  sim_ac_normalised:                      0
% 2.08/1.03  sim_smt_subsumption:                    0
% 2.08/1.03  
%------------------------------------------------------------------------------
