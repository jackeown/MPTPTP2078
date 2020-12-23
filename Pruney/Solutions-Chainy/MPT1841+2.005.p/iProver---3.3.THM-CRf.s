%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:51 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 718 expanded)
%              Number of clauses        :   77 ( 208 expanded)
%              Number of leaves         :   20 ( 170 expanded)
%              Depth                    :   27
%              Number of atoms          :  378 (2335 expanded)
%              Number of equality atoms :  132 ( 383 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

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

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
     => ( v1_zfmisc_1(X0)
        & v1_subset_1(k6_domain_1(X0,sK3),X0)
        & m1_subset_1(sK3,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
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

fof(f43,plain,
    ( v1_zfmisc_1(sK2)
    & v1_subset_1(k6_domain_1(sK2,sK3),sK2)
    & m1_subset_1(sK3,sK2)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f29,f42,f41])).

fof(f66,plain,(
    m1_subset_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f63,f55])).

fof(f65,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f18])).

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

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
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

fof(f44,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f67,plain,(
    v1_subset_1(k6_domain_1(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f68,plain,(
    v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f69,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f54,f52])).

fof(f70,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f53,f69])).

fof(f8,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f71,plain,(
    ! [X0,X1] : k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,k2_tarski(X0,X0)))) != k1_xboole_0 ),
    inference(definition_unfolding,[],[f56,f69,f55])).

cnf(c_10,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_864,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_862,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1143,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_864,c_862])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_858,plain,
    ( m1_subset_1(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_859,plain,
    ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1874,plain,
    ( k6_domain_1(sK2,sK3) = k2_tarski(sK3,sK3)
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_858,c_859])).

cnf(c_21,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1021,plain,
    ( ~ m1_subset_1(sK3,sK2)
    | v1_xboole_0(sK2)
    | k6_domain_1(sK2,sK3) = k2_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2254,plain,
    ( k6_domain_1(sK2,sK3) = k2_tarski(sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1874,c_21,c_20,c_1021])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_860,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2259,plain,
    ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK3,sK2) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2254,c_860])).

cnf(c_22,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_23,plain,
    ( m1_subset_1(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2322,plain,
    ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2259,c_22,c_23])).

cnf(c_2105,plain,
    ( k2_tarski(k6_domain_1(X0,X1),k6_domain_1(X0,X1)) = k6_domain_1(k1_zfmisc_1(X0),k6_domain_1(X0,X1))
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_860,c_859])).

cnf(c_4870,plain,
    ( k2_tarski(k6_domain_1(k1_zfmisc_1(sK2),k2_tarski(sK3,sK3)),k6_domain_1(k1_zfmisc_1(sK2),k2_tarski(sK3,sK3))) = k6_domain_1(k1_zfmisc_1(k1_zfmisc_1(sK2)),k6_domain_1(k1_zfmisc_1(sK2),k2_tarski(sK3,sK3)))
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2322,c_2105])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_868,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_14,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_861,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2328,plain,
    ( m1_subset_1(X0,sK2) = iProver_top
    | r2_hidden(X0,k2_tarski(sK3,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2322,c_861])).

cnf(c_2461,plain,
    ( m1_subset_1(sK1(k2_tarski(sK3,sK3),X0),sK2) = iProver_top
    | r1_tarski(k2_tarski(sK3,sK3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_868,c_2328])).

cnf(c_2947,plain,
    ( k2_tarski(sK1(k2_tarski(sK3,sK3),X0),sK1(k2_tarski(sK3,sK3),X0)) = k6_domain_1(sK2,sK1(k2_tarski(sK3,sK3),X0))
    | r1_tarski(k2_tarski(sK3,sK3),X0) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2461,c_859])).

cnf(c_3106,plain,
    ( r1_tarski(k2_tarski(sK3,sK3),X0) = iProver_top
    | k2_tarski(sK1(k2_tarski(sK3,sK3),X0),sK1(k2_tarski(sK3,sK3),X0)) = k6_domain_1(sK2,sK1(k2_tarski(sK3,sK3),X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2947,c_22])).

cnf(c_3107,plain,
    ( k2_tarski(sK1(k2_tarski(sK3,sK3),X0),sK1(k2_tarski(sK3,sK3),X0)) = k6_domain_1(sK2,sK1(k2_tarski(sK3,sK3),X0))
    | r1_tarski(k2_tarski(sK3,sK3),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_3106])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_867,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3112,plain,
    ( k2_tarski(sK1(k2_tarski(sK3,sK3),X0),sK1(k2_tarski(sK3,sK3),X0)) = k6_domain_1(sK2,sK1(k2_tarski(sK3,sK3),X0))
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,k2_tarski(sK3,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3107,c_867])).

cnf(c_3397,plain,
    ( k2_tarski(sK1(k2_tarski(sK3,sK3),X0),sK1(k2_tarski(sK3,sK3),X0)) = k6_domain_1(sK2,sK1(k2_tarski(sK3,sK3),X0))
    | r1_tarski(k2_tarski(sK3,sK3),X1) = iProver_top
    | r2_hidden(sK1(k2_tarski(sK3,sK3),X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_868,c_3112])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_870,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4242,plain,
    ( k2_tarski(sK1(k2_tarski(sK3,sK3),X0),sK1(k2_tarski(sK3,sK3),X0)) = k6_domain_1(sK2,sK1(k2_tarski(sK3,sK3),X0))
    | r1_tarski(k2_tarski(sK3,sK3),X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3397,c_870])).

cnf(c_5292,plain,
    ( k2_tarski(k6_domain_1(k1_zfmisc_1(sK2),k2_tarski(sK3,sK3)),k6_domain_1(k1_zfmisc_1(sK2),k2_tarski(sK3,sK3))) = k6_domain_1(k1_zfmisc_1(k1_zfmisc_1(sK2)),k6_domain_1(k1_zfmisc_1(sK2),k2_tarski(sK3,sK3)))
    | k2_tarski(sK1(k2_tarski(sK3,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2))),sK1(k2_tarski(sK3,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2)))) = k6_domain_1(sK2,sK1(k2_tarski(sK3,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2))))
    | r1_tarski(k2_tarski(sK3,sK3),X0) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4870,c_4242])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_866,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5320,plain,
    ( k2_tarski(k6_domain_1(k1_zfmisc_1(sK2),k2_tarski(sK3,sK3)),k6_domain_1(k1_zfmisc_1(sK2),k2_tarski(sK3,sK3))) = k6_domain_1(k1_zfmisc_1(k1_zfmisc_1(sK2)),k6_domain_1(k1_zfmisc_1(sK2),k2_tarski(sK3,sK3)))
    | k2_tarski(sK1(k2_tarski(sK3,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2))),sK1(k2_tarski(sK3,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2)))) = k6_domain_1(sK2,sK1(k2_tarski(sK3,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2))))
    | k2_tarski(sK3,sK3) = X0
    | r1_tarski(X0,k2_tarski(sK3,sK3)) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5292,c_866])).

cnf(c_2793,plain,
    ( ~ r1_tarski(X0,k2_tarski(sK3,sK3))
    | ~ r1_tarski(k2_tarski(sK3,sK3),X0)
    | k2_tarski(sK3,sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2794,plain,
    ( k2_tarski(sK3,sK3) = X0
    | r1_tarski(X0,k2_tarski(sK3,sK3)) != iProver_top
    | r1_tarski(k2_tarski(sK3,sK3),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2793])).

cnf(c_5319,plain,
    ( k2_tarski(k6_domain_1(k1_zfmisc_1(sK2),k2_tarski(sK3,sK3)),k6_domain_1(k1_zfmisc_1(sK2),k2_tarski(sK3,sK3))) = k6_domain_1(k1_zfmisc_1(k1_zfmisc_1(sK2)),k6_domain_1(k1_zfmisc_1(sK2),k2_tarski(sK3,sK3)))
    | k2_tarski(sK1(k2_tarski(sK3,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2))),sK1(k2_tarski(sK3,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2)))) = k6_domain_1(sK2,sK1(k2_tarski(sK3,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2))))
    | r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k2_tarski(sK3,sK3)) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5292,c_867])).

cnf(c_17,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_109,plain,
    ( ~ v1_zfmisc_1(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X0,X1)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_11])).

cnf(c_110,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_109])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_155,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_156,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_155])).

cnf(c_191,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_110,c_156])).

cnf(c_19,negated_conjecture,
    ( v1_subset_1(k6_domain_1(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_262,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | k6_domain_1(sK2,sK3) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_191,c_19])).

cnf(c_263,plain,
    ( ~ r1_tarski(k6_domain_1(sK2,sK3),sK2)
    | ~ v1_zfmisc_1(sK2)
    | v1_xboole_0(k6_domain_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_262])).

cnf(c_18,negated_conjecture,
    ( v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_265,plain,
    ( ~ r1_tarski(k6_domain_1(sK2,sK3),sK2)
    | v1_xboole_0(k6_domain_1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_263,c_18])).

cnf(c_855,plain,
    ( r1_tarski(k6_domain_1(sK2,sK3),sK2) != iProver_top
    | v1_xboole_0(k6_domain_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_265])).

cnf(c_25,plain,
    ( v1_zfmisc_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_264,plain,
    ( r1_tarski(k6_domain_1(sK2,sK3),sK2) != iProver_top
    | v1_zfmisc_1(sK2) != iProver_top
    | v1_xboole_0(k6_domain_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_263])).

cnf(c_986,plain,
    ( ~ m1_subset_1(k6_domain_1(sK2,sK3),k1_zfmisc_1(sK2))
    | r1_tarski(k6_domain_1(sK2,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_987,plain,
    ( m1_subset_1(k6_domain_1(sK2,sK3),k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(k6_domain_1(sK2,sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_986])).

cnf(c_1008,plain,
    ( m1_subset_1(k6_domain_1(sK2,sK3),k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK3,sK2)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1009,plain,
    ( m1_subset_1(k6_domain_1(sK2,sK3),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK3,sK2) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1008])).

cnf(c_1046,plain,
    ( v1_xboole_0(k6_domain_1(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_855,c_22,c_23,c_25,c_264,c_987,c_1009])).

cnf(c_2257,plain,
    ( v1_xboole_0(k2_tarski(sK3,sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2254,c_1046])).

cnf(c_4006,plain,
    ( ~ r2_hidden(X0,k2_tarski(sK3,sK3))
    | ~ v1_xboole_0(k2_tarski(sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4007,plain,
    ( r2_hidden(X0,k2_tarski(sK3,sK3)) != iProver_top
    | v1_xboole_0(k2_tarski(sK3,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4006])).

cnf(c_5782,plain,
    ( r2_hidden(X0,k2_tarski(sK3,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5319,c_2257,c_4007])).

cnf(c_5790,plain,
    ( r1_tarski(k2_tarski(sK3,sK3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_868,c_5782])).

cnf(c_5938,plain,
    ( r1_tarski(X0,k2_tarski(sK3,sK3)) != iProver_top
    | k2_tarski(sK3,sK3) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5320,c_2794,c_5790])).

cnf(c_5939,plain,
    ( k2_tarski(sK3,sK3) = X0
    | r1_tarski(X0,k2_tarski(sK3,sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5938])).

cnf(c_5946,plain,
    ( k2_tarski(sK3,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1143,c_5939])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_9,plain,
    ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,k2_tarski(X0,X0)))) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1281,plain,
    ( k2_tarski(X0,X0) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8,c_9])).

cnf(c_6579,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5946,c_1281])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:06:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.36/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.00  
% 2.36/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.36/1.00  
% 2.36/1.00  ------  iProver source info
% 2.36/1.00  
% 2.36/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.36/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.36/1.00  git: non_committed_changes: false
% 2.36/1.00  git: last_make_outside_of_git: false
% 2.36/1.00  
% 2.36/1.00  ------ 
% 2.36/1.00  
% 2.36/1.00  ------ Input Options
% 2.36/1.00  
% 2.36/1.00  --out_options                           all
% 2.36/1.00  --tptp_safe_out                         true
% 2.36/1.00  --problem_path                          ""
% 2.36/1.00  --include_path                          ""
% 2.36/1.00  --clausifier                            res/vclausify_rel
% 2.36/1.00  --clausifier_options                    --mode clausify
% 2.36/1.00  --stdin                                 false
% 2.36/1.00  --stats_out                             all
% 2.36/1.00  
% 2.36/1.00  ------ General Options
% 2.36/1.00  
% 2.36/1.00  --fof                                   false
% 2.36/1.00  --time_out_real                         305.
% 2.36/1.00  --time_out_virtual                      -1.
% 2.36/1.00  --symbol_type_check                     false
% 2.36/1.00  --clausify_out                          false
% 2.36/1.00  --sig_cnt_out                           false
% 2.36/1.00  --trig_cnt_out                          false
% 2.36/1.00  --trig_cnt_out_tolerance                1.
% 2.36/1.00  --trig_cnt_out_sk_spl                   false
% 2.36/1.00  --abstr_cl_out                          false
% 2.36/1.00  
% 2.36/1.00  ------ Global Options
% 2.36/1.00  
% 2.36/1.00  --schedule                              default
% 2.36/1.00  --add_important_lit                     false
% 2.36/1.00  --prop_solver_per_cl                    1000
% 2.36/1.00  --min_unsat_core                        false
% 2.36/1.00  --soft_assumptions                      false
% 2.36/1.00  --soft_lemma_size                       3
% 2.36/1.00  --prop_impl_unit_size                   0
% 2.36/1.00  --prop_impl_unit                        []
% 2.36/1.00  --share_sel_clauses                     true
% 2.36/1.00  --reset_solvers                         false
% 2.36/1.00  --bc_imp_inh                            [conj_cone]
% 2.36/1.00  --conj_cone_tolerance                   3.
% 2.36/1.00  --extra_neg_conj                        none
% 2.36/1.00  --large_theory_mode                     true
% 2.36/1.00  --prolific_symb_bound                   200
% 2.36/1.00  --lt_threshold                          2000
% 2.36/1.00  --clause_weak_htbl                      true
% 2.36/1.00  --gc_record_bc_elim                     false
% 2.36/1.00  
% 2.36/1.00  ------ Preprocessing Options
% 2.36/1.00  
% 2.36/1.00  --preprocessing_flag                    true
% 2.36/1.00  --time_out_prep_mult                    0.1
% 2.36/1.00  --splitting_mode                        input
% 2.36/1.00  --splitting_grd                         true
% 2.36/1.00  --splitting_cvd                         false
% 2.36/1.00  --splitting_cvd_svl                     false
% 2.36/1.00  --splitting_nvd                         32
% 2.36/1.00  --sub_typing                            true
% 2.36/1.00  --prep_gs_sim                           true
% 2.36/1.00  --prep_unflatten                        true
% 2.36/1.00  --prep_res_sim                          true
% 2.36/1.00  --prep_upred                            true
% 2.36/1.00  --prep_sem_filter                       exhaustive
% 2.36/1.00  --prep_sem_filter_out                   false
% 2.36/1.00  --pred_elim                             true
% 2.36/1.00  --res_sim_input                         true
% 2.36/1.00  --eq_ax_congr_red                       true
% 2.36/1.00  --pure_diseq_elim                       true
% 2.36/1.00  --brand_transform                       false
% 2.36/1.00  --non_eq_to_eq                          false
% 2.36/1.00  --prep_def_merge                        true
% 2.36/1.00  --prep_def_merge_prop_impl              false
% 2.36/1.01  --prep_def_merge_mbd                    true
% 2.36/1.01  --prep_def_merge_tr_red                 false
% 2.36/1.01  --prep_def_merge_tr_cl                  false
% 2.36/1.01  --smt_preprocessing                     true
% 2.36/1.01  --smt_ac_axioms                         fast
% 2.36/1.01  --preprocessed_out                      false
% 2.36/1.01  --preprocessed_stats                    false
% 2.36/1.01  
% 2.36/1.01  ------ Abstraction refinement Options
% 2.36/1.01  
% 2.36/1.01  --abstr_ref                             []
% 2.36/1.01  --abstr_ref_prep                        false
% 2.36/1.01  --abstr_ref_until_sat                   false
% 2.36/1.01  --abstr_ref_sig_restrict                funpre
% 2.36/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.36/1.01  --abstr_ref_under                       []
% 2.36/1.01  
% 2.36/1.01  ------ SAT Options
% 2.36/1.01  
% 2.36/1.01  --sat_mode                              false
% 2.36/1.01  --sat_fm_restart_options                ""
% 2.36/1.01  --sat_gr_def                            false
% 2.36/1.01  --sat_epr_types                         true
% 2.36/1.01  --sat_non_cyclic_types                  false
% 2.36/1.01  --sat_finite_models                     false
% 2.36/1.01  --sat_fm_lemmas                         false
% 2.36/1.01  --sat_fm_prep                           false
% 2.36/1.01  --sat_fm_uc_incr                        true
% 2.36/1.01  --sat_out_model                         small
% 2.36/1.01  --sat_out_clauses                       false
% 2.36/1.01  
% 2.36/1.01  ------ QBF Options
% 2.36/1.01  
% 2.36/1.01  --qbf_mode                              false
% 2.36/1.01  --qbf_elim_univ                         false
% 2.36/1.01  --qbf_dom_inst                          none
% 2.36/1.01  --qbf_dom_pre_inst                      false
% 2.36/1.01  --qbf_sk_in                             false
% 2.36/1.01  --qbf_pred_elim                         true
% 2.36/1.01  --qbf_split                             512
% 2.36/1.01  
% 2.36/1.01  ------ BMC1 Options
% 2.36/1.01  
% 2.36/1.01  --bmc1_incremental                      false
% 2.36/1.01  --bmc1_axioms                           reachable_all
% 2.36/1.01  --bmc1_min_bound                        0
% 2.36/1.01  --bmc1_max_bound                        -1
% 2.36/1.01  --bmc1_max_bound_default                -1
% 2.36/1.01  --bmc1_symbol_reachability              true
% 2.36/1.01  --bmc1_property_lemmas                  false
% 2.36/1.01  --bmc1_k_induction                      false
% 2.36/1.01  --bmc1_non_equiv_states                 false
% 2.36/1.01  --bmc1_deadlock                         false
% 2.36/1.01  --bmc1_ucm                              false
% 2.36/1.01  --bmc1_add_unsat_core                   none
% 2.36/1.01  --bmc1_unsat_core_children              false
% 2.36/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.36/1.01  --bmc1_out_stat                         full
% 2.36/1.01  --bmc1_ground_init                      false
% 2.36/1.01  --bmc1_pre_inst_next_state              false
% 2.36/1.01  --bmc1_pre_inst_state                   false
% 2.36/1.01  --bmc1_pre_inst_reach_state             false
% 2.36/1.01  --bmc1_out_unsat_core                   false
% 2.36/1.01  --bmc1_aig_witness_out                  false
% 2.36/1.01  --bmc1_verbose                          false
% 2.36/1.01  --bmc1_dump_clauses_tptp                false
% 2.36/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.36/1.01  --bmc1_dump_file                        -
% 2.36/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.36/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.36/1.01  --bmc1_ucm_extend_mode                  1
% 2.36/1.01  --bmc1_ucm_init_mode                    2
% 2.36/1.01  --bmc1_ucm_cone_mode                    none
% 2.36/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.36/1.01  --bmc1_ucm_relax_model                  4
% 2.36/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.36/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.36/1.01  --bmc1_ucm_layered_model                none
% 2.36/1.01  --bmc1_ucm_max_lemma_size               10
% 2.36/1.01  
% 2.36/1.01  ------ AIG Options
% 2.36/1.01  
% 2.36/1.01  --aig_mode                              false
% 2.36/1.01  
% 2.36/1.01  ------ Instantiation Options
% 2.36/1.01  
% 2.36/1.01  --instantiation_flag                    true
% 2.36/1.01  --inst_sos_flag                         false
% 2.36/1.01  --inst_sos_phase                        true
% 2.36/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.36/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.36/1.01  --inst_lit_sel_side                     num_symb
% 2.36/1.01  --inst_solver_per_active                1400
% 2.36/1.01  --inst_solver_calls_frac                1.
% 2.36/1.01  --inst_passive_queue_type               priority_queues
% 2.36/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.36/1.01  --inst_passive_queues_freq              [25;2]
% 2.36/1.01  --inst_dismatching                      true
% 2.36/1.01  --inst_eager_unprocessed_to_passive     true
% 2.36/1.01  --inst_prop_sim_given                   true
% 2.36/1.01  --inst_prop_sim_new                     false
% 2.36/1.01  --inst_subs_new                         false
% 2.36/1.01  --inst_eq_res_simp                      false
% 2.36/1.01  --inst_subs_given                       false
% 2.36/1.01  --inst_orphan_elimination               true
% 2.36/1.01  --inst_learning_loop_flag               true
% 2.36/1.01  --inst_learning_start                   3000
% 2.36/1.01  --inst_learning_factor                  2
% 2.36/1.01  --inst_start_prop_sim_after_learn       3
% 2.36/1.01  --inst_sel_renew                        solver
% 2.36/1.01  --inst_lit_activity_flag                true
% 2.36/1.01  --inst_restr_to_given                   false
% 2.36/1.01  --inst_activity_threshold               500
% 2.36/1.01  --inst_out_proof                        true
% 2.36/1.01  
% 2.36/1.01  ------ Resolution Options
% 2.36/1.01  
% 2.36/1.01  --resolution_flag                       true
% 2.36/1.01  --res_lit_sel                           adaptive
% 2.36/1.01  --res_lit_sel_side                      none
% 2.36/1.01  --res_ordering                          kbo
% 2.36/1.01  --res_to_prop_solver                    active
% 2.36/1.01  --res_prop_simpl_new                    false
% 2.36/1.01  --res_prop_simpl_given                  true
% 2.36/1.01  --res_passive_queue_type                priority_queues
% 2.36/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.36/1.01  --res_passive_queues_freq               [15;5]
% 2.36/1.01  --res_forward_subs                      full
% 2.36/1.01  --res_backward_subs                     full
% 2.36/1.01  --res_forward_subs_resolution           true
% 2.36/1.01  --res_backward_subs_resolution          true
% 2.36/1.01  --res_orphan_elimination                true
% 2.36/1.01  --res_time_limit                        2.
% 2.36/1.01  --res_out_proof                         true
% 2.36/1.01  
% 2.36/1.01  ------ Superposition Options
% 2.36/1.01  
% 2.36/1.01  --superposition_flag                    true
% 2.36/1.01  --sup_passive_queue_type                priority_queues
% 2.36/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.36/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.36/1.01  --demod_completeness_check              fast
% 2.36/1.01  --demod_use_ground                      true
% 2.36/1.01  --sup_to_prop_solver                    passive
% 2.36/1.01  --sup_prop_simpl_new                    true
% 2.36/1.01  --sup_prop_simpl_given                  true
% 2.36/1.01  --sup_fun_splitting                     false
% 2.36/1.01  --sup_smt_interval                      50000
% 2.36/1.01  
% 2.36/1.01  ------ Superposition Simplification Setup
% 2.36/1.01  
% 2.36/1.01  --sup_indices_passive                   []
% 2.36/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.36/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/1.01  --sup_full_bw                           [BwDemod]
% 2.36/1.01  --sup_immed_triv                        [TrivRules]
% 2.36/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.36/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/1.01  --sup_immed_bw_main                     []
% 2.36/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.36/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/1.01  
% 2.36/1.01  ------ Combination Options
% 2.36/1.01  
% 2.36/1.01  --comb_res_mult                         3
% 2.36/1.01  --comb_sup_mult                         2
% 2.36/1.01  --comb_inst_mult                        10
% 2.36/1.01  
% 2.36/1.01  ------ Debug Options
% 2.36/1.01  
% 2.36/1.01  --dbg_backtrace                         false
% 2.36/1.01  --dbg_dump_prop_clauses                 false
% 2.36/1.01  --dbg_dump_prop_clauses_file            -
% 2.36/1.01  --dbg_out_stat                          false
% 2.36/1.01  ------ Parsing...
% 2.36/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.36/1.01  
% 2.36/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.36/1.01  
% 2.36/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.36/1.01  
% 2.36/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.36/1.01  ------ Proving...
% 2.36/1.01  ------ Problem Properties 
% 2.36/1.01  
% 2.36/1.01  
% 2.36/1.01  clauses                                 19
% 2.36/1.01  conjectures                             2
% 2.36/1.01  EPR                                     7
% 2.36/1.01  Horn                                    15
% 2.36/1.01  unary                                   6
% 2.36/1.01  binary                                  7
% 2.36/1.01  lits                                    38
% 2.36/1.01  lits eq                                 4
% 2.36/1.01  fd_pure                                 0
% 2.36/1.01  fd_pseudo                               0
% 2.36/1.01  fd_cond                                 0
% 2.36/1.01  fd_pseudo_cond                          1
% 2.36/1.01  AC symbols                              0
% 2.36/1.01  
% 2.36/1.01  ------ Schedule dynamic 5 is on 
% 2.36/1.01  
% 2.36/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.36/1.01  
% 2.36/1.01  
% 2.36/1.01  ------ 
% 2.36/1.01  Current options:
% 2.36/1.01  ------ 
% 2.36/1.01  
% 2.36/1.01  ------ Input Options
% 2.36/1.01  
% 2.36/1.01  --out_options                           all
% 2.36/1.01  --tptp_safe_out                         true
% 2.36/1.01  --problem_path                          ""
% 2.36/1.01  --include_path                          ""
% 2.36/1.01  --clausifier                            res/vclausify_rel
% 2.36/1.01  --clausifier_options                    --mode clausify
% 2.36/1.01  --stdin                                 false
% 2.36/1.01  --stats_out                             all
% 2.36/1.01  
% 2.36/1.01  ------ General Options
% 2.36/1.01  
% 2.36/1.01  --fof                                   false
% 2.36/1.01  --time_out_real                         305.
% 2.36/1.01  --time_out_virtual                      -1.
% 2.36/1.01  --symbol_type_check                     false
% 2.36/1.01  --clausify_out                          false
% 2.36/1.01  --sig_cnt_out                           false
% 2.36/1.01  --trig_cnt_out                          false
% 2.36/1.01  --trig_cnt_out_tolerance                1.
% 2.36/1.01  --trig_cnt_out_sk_spl                   false
% 2.36/1.01  --abstr_cl_out                          false
% 2.36/1.01  
% 2.36/1.01  ------ Global Options
% 2.36/1.01  
% 2.36/1.01  --schedule                              default
% 2.36/1.01  --add_important_lit                     false
% 2.36/1.01  --prop_solver_per_cl                    1000
% 2.36/1.01  --min_unsat_core                        false
% 2.36/1.01  --soft_assumptions                      false
% 2.36/1.01  --soft_lemma_size                       3
% 2.36/1.01  --prop_impl_unit_size                   0
% 2.36/1.01  --prop_impl_unit                        []
% 2.36/1.01  --share_sel_clauses                     true
% 2.36/1.01  --reset_solvers                         false
% 2.36/1.01  --bc_imp_inh                            [conj_cone]
% 2.36/1.01  --conj_cone_tolerance                   3.
% 2.36/1.01  --extra_neg_conj                        none
% 2.36/1.01  --large_theory_mode                     true
% 2.36/1.01  --prolific_symb_bound                   200
% 2.36/1.01  --lt_threshold                          2000
% 2.36/1.01  --clause_weak_htbl                      true
% 2.36/1.01  --gc_record_bc_elim                     false
% 2.36/1.01  
% 2.36/1.01  ------ Preprocessing Options
% 2.36/1.01  
% 2.36/1.01  --preprocessing_flag                    true
% 2.36/1.01  --time_out_prep_mult                    0.1
% 2.36/1.01  --splitting_mode                        input
% 2.36/1.01  --splitting_grd                         true
% 2.36/1.01  --splitting_cvd                         false
% 2.36/1.01  --splitting_cvd_svl                     false
% 2.36/1.01  --splitting_nvd                         32
% 2.36/1.01  --sub_typing                            true
% 2.36/1.01  --prep_gs_sim                           true
% 2.36/1.01  --prep_unflatten                        true
% 2.36/1.01  --prep_res_sim                          true
% 2.36/1.01  --prep_upred                            true
% 2.36/1.01  --prep_sem_filter                       exhaustive
% 2.36/1.01  --prep_sem_filter_out                   false
% 2.36/1.01  --pred_elim                             true
% 2.36/1.01  --res_sim_input                         true
% 2.36/1.01  --eq_ax_congr_red                       true
% 2.36/1.01  --pure_diseq_elim                       true
% 2.36/1.01  --brand_transform                       false
% 2.36/1.01  --non_eq_to_eq                          false
% 2.36/1.01  --prep_def_merge                        true
% 2.36/1.01  --prep_def_merge_prop_impl              false
% 2.36/1.01  --prep_def_merge_mbd                    true
% 2.36/1.01  --prep_def_merge_tr_red                 false
% 2.36/1.01  --prep_def_merge_tr_cl                  false
% 2.36/1.01  --smt_preprocessing                     true
% 2.36/1.01  --smt_ac_axioms                         fast
% 2.36/1.01  --preprocessed_out                      false
% 2.36/1.01  --preprocessed_stats                    false
% 2.36/1.01  
% 2.36/1.01  ------ Abstraction refinement Options
% 2.36/1.01  
% 2.36/1.01  --abstr_ref                             []
% 2.36/1.01  --abstr_ref_prep                        false
% 2.36/1.01  --abstr_ref_until_sat                   false
% 2.36/1.01  --abstr_ref_sig_restrict                funpre
% 2.36/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.36/1.01  --abstr_ref_under                       []
% 2.36/1.01  
% 2.36/1.01  ------ SAT Options
% 2.36/1.01  
% 2.36/1.01  --sat_mode                              false
% 2.36/1.01  --sat_fm_restart_options                ""
% 2.36/1.01  --sat_gr_def                            false
% 2.36/1.01  --sat_epr_types                         true
% 2.36/1.01  --sat_non_cyclic_types                  false
% 2.36/1.01  --sat_finite_models                     false
% 2.36/1.01  --sat_fm_lemmas                         false
% 2.36/1.01  --sat_fm_prep                           false
% 2.36/1.01  --sat_fm_uc_incr                        true
% 2.36/1.01  --sat_out_model                         small
% 2.36/1.01  --sat_out_clauses                       false
% 2.36/1.01  
% 2.36/1.01  ------ QBF Options
% 2.36/1.01  
% 2.36/1.01  --qbf_mode                              false
% 2.36/1.01  --qbf_elim_univ                         false
% 2.36/1.01  --qbf_dom_inst                          none
% 2.36/1.01  --qbf_dom_pre_inst                      false
% 2.36/1.01  --qbf_sk_in                             false
% 2.36/1.01  --qbf_pred_elim                         true
% 2.36/1.01  --qbf_split                             512
% 2.36/1.01  
% 2.36/1.01  ------ BMC1 Options
% 2.36/1.01  
% 2.36/1.01  --bmc1_incremental                      false
% 2.36/1.01  --bmc1_axioms                           reachable_all
% 2.36/1.01  --bmc1_min_bound                        0
% 2.36/1.01  --bmc1_max_bound                        -1
% 2.36/1.01  --bmc1_max_bound_default                -1
% 2.36/1.01  --bmc1_symbol_reachability              true
% 2.36/1.01  --bmc1_property_lemmas                  false
% 2.36/1.01  --bmc1_k_induction                      false
% 2.36/1.01  --bmc1_non_equiv_states                 false
% 2.36/1.01  --bmc1_deadlock                         false
% 2.36/1.01  --bmc1_ucm                              false
% 2.36/1.01  --bmc1_add_unsat_core                   none
% 2.36/1.01  --bmc1_unsat_core_children              false
% 2.36/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.36/1.01  --bmc1_out_stat                         full
% 2.36/1.01  --bmc1_ground_init                      false
% 2.36/1.01  --bmc1_pre_inst_next_state              false
% 2.36/1.01  --bmc1_pre_inst_state                   false
% 2.36/1.01  --bmc1_pre_inst_reach_state             false
% 2.36/1.01  --bmc1_out_unsat_core                   false
% 2.36/1.01  --bmc1_aig_witness_out                  false
% 2.36/1.01  --bmc1_verbose                          false
% 2.36/1.01  --bmc1_dump_clauses_tptp                false
% 2.36/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.36/1.01  --bmc1_dump_file                        -
% 2.36/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.36/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.36/1.01  --bmc1_ucm_extend_mode                  1
% 2.36/1.01  --bmc1_ucm_init_mode                    2
% 2.36/1.01  --bmc1_ucm_cone_mode                    none
% 2.36/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.36/1.01  --bmc1_ucm_relax_model                  4
% 2.36/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.36/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.36/1.01  --bmc1_ucm_layered_model                none
% 2.36/1.01  --bmc1_ucm_max_lemma_size               10
% 2.36/1.01  
% 2.36/1.01  ------ AIG Options
% 2.36/1.01  
% 2.36/1.01  --aig_mode                              false
% 2.36/1.01  
% 2.36/1.01  ------ Instantiation Options
% 2.36/1.01  
% 2.36/1.01  --instantiation_flag                    true
% 2.36/1.01  --inst_sos_flag                         false
% 2.36/1.01  --inst_sos_phase                        true
% 2.36/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.36/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.36/1.01  --inst_lit_sel_side                     none
% 2.36/1.01  --inst_solver_per_active                1400
% 2.36/1.01  --inst_solver_calls_frac                1.
% 2.36/1.01  --inst_passive_queue_type               priority_queues
% 2.36/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.36/1.01  --inst_passive_queues_freq              [25;2]
% 2.36/1.01  --inst_dismatching                      true
% 2.36/1.01  --inst_eager_unprocessed_to_passive     true
% 2.36/1.01  --inst_prop_sim_given                   true
% 2.36/1.01  --inst_prop_sim_new                     false
% 2.36/1.01  --inst_subs_new                         false
% 2.36/1.01  --inst_eq_res_simp                      false
% 2.36/1.01  --inst_subs_given                       false
% 2.36/1.01  --inst_orphan_elimination               true
% 2.36/1.01  --inst_learning_loop_flag               true
% 2.36/1.01  --inst_learning_start                   3000
% 2.36/1.01  --inst_learning_factor                  2
% 2.36/1.01  --inst_start_prop_sim_after_learn       3
% 2.36/1.01  --inst_sel_renew                        solver
% 2.36/1.01  --inst_lit_activity_flag                true
% 2.36/1.01  --inst_restr_to_given                   false
% 2.36/1.01  --inst_activity_threshold               500
% 2.36/1.01  --inst_out_proof                        true
% 2.36/1.01  
% 2.36/1.01  ------ Resolution Options
% 2.36/1.01  
% 2.36/1.01  --resolution_flag                       false
% 2.36/1.01  --res_lit_sel                           adaptive
% 2.36/1.01  --res_lit_sel_side                      none
% 2.36/1.01  --res_ordering                          kbo
% 2.36/1.01  --res_to_prop_solver                    active
% 2.36/1.01  --res_prop_simpl_new                    false
% 2.36/1.01  --res_prop_simpl_given                  true
% 2.36/1.01  --res_passive_queue_type                priority_queues
% 2.36/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.36/1.01  --res_passive_queues_freq               [15;5]
% 2.36/1.01  --res_forward_subs                      full
% 2.36/1.01  --res_backward_subs                     full
% 2.36/1.01  --res_forward_subs_resolution           true
% 2.36/1.01  --res_backward_subs_resolution          true
% 2.36/1.01  --res_orphan_elimination                true
% 2.36/1.01  --res_time_limit                        2.
% 2.36/1.01  --res_out_proof                         true
% 2.36/1.01  
% 2.36/1.01  ------ Superposition Options
% 2.36/1.01  
% 2.36/1.01  --superposition_flag                    true
% 2.36/1.01  --sup_passive_queue_type                priority_queues
% 2.36/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.36/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.36/1.01  --demod_completeness_check              fast
% 2.36/1.01  --demod_use_ground                      true
% 2.36/1.01  --sup_to_prop_solver                    passive
% 2.36/1.01  --sup_prop_simpl_new                    true
% 2.36/1.01  --sup_prop_simpl_given                  true
% 2.36/1.01  --sup_fun_splitting                     false
% 2.36/1.01  --sup_smt_interval                      50000
% 2.36/1.01  
% 2.36/1.01  ------ Superposition Simplification Setup
% 2.36/1.01  
% 2.36/1.01  --sup_indices_passive                   []
% 2.36/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.36/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/1.01  --sup_full_bw                           [BwDemod]
% 2.36/1.01  --sup_immed_triv                        [TrivRules]
% 2.36/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.36/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/1.01  --sup_immed_bw_main                     []
% 2.36/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.36/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/1.01  
% 2.36/1.01  ------ Combination Options
% 2.36/1.01  
% 2.36/1.01  --comb_res_mult                         3
% 2.36/1.01  --comb_sup_mult                         2
% 2.36/1.01  --comb_inst_mult                        10
% 2.36/1.01  
% 2.36/1.01  ------ Debug Options
% 2.36/1.01  
% 2.36/1.01  --dbg_backtrace                         false
% 2.36/1.01  --dbg_dump_prop_clauses                 false
% 2.36/1.01  --dbg_dump_prop_clauses_file            -
% 2.36/1.01  --dbg_out_stat                          false
% 2.36/1.01  
% 2.36/1.01  
% 2.36/1.01  
% 2.36/1.01  
% 2.36/1.01  ------ Proving...
% 2.36/1.01  
% 2.36/1.01  
% 2.36/1.01  % SZS status Theorem for theBenchmark.p
% 2.36/1.01  
% 2.36/1.01   Resolution empty clause
% 2.36/1.01  
% 2.36/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.36/1.01  
% 2.36/1.01  fof(f9,axiom,(
% 2.36/1.01    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.36/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/1.01  
% 2.36/1.01  fof(f57,plain,(
% 2.36/1.01    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.36/1.01    inference(cnf_transformation,[],[f9])).
% 2.36/1.01  
% 2.36/1.01  fof(f11,axiom,(
% 2.36/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.36/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/1.01  
% 2.36/1.01  fof(f40,plain,(
% 2.36/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.36/1.01    inference(nnf_transformation,[],[f11])).
% 2.36/1.01  
% 2.36/1.01  fof(f59,plain,(
% 2.36/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.36/1.01    inference(cnf_transformation,[],[f40])).
% 2.36/1.01  
% 2.36/1.01  fof(f16,conjecture,(
% 2.36/1.01    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 2.36/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/1.01  
% 2.36/1.01  fof(f17,negated_conjecture,(
% 2.36/1.01    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 2.36/1.01    inference(negated_conjecture,[],[f16])).
% 2.36/1.01  
% 2.36/1.01  fof(f28,plain,(
% 2.36/1.01    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 2.36/1.01    inference(ennf_transformation,[],[f17])).
% 2.36/1.01  
% 2.36/1.01  fof(f29,plain,(
% 2.36/1.01    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 2.36/1.01    inference(flattening,[],[f28])).
% 2.36/1.01  
% 2.36/1.01  fof(f42,plain,(
% 2.36/1.01    ( ! [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) => (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,sK3),X0) & m1_subset_1(sK3,X0))) )),
% 2.36/1.01    introduced(choice_axiom,[])).
% 2.36/1.01  
% 2.36/1.01  fof(f41,plain,(
% 2.36/1.01    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK2) & v1_subset_1(k6_domain_1(sK2,X1),sK2) & m1_subset_1(X1,sK2)) & ~v1_xboole_0(sK2))),
% 2.36/1.01    introduced(choice_axiom,[])).
% 2.36/1.01  
% 2.36/1.01  fof(f43,plain,(
% 2.36/1.01    (v1_zfmisc_1(sK2) & v1_subset_1(k6_domain_1(sK2,sK3),sK2) & m1_subset_1(sK3,sK2)) & ~v1_xboole_0(sK2)),
% 2.36/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f29,f42,f41])).
% 2.36/1.01  
% 2.36/1.01  fof(f66,plain,(
% 2.36/1.01    m1_subset_1(sK3,sK2)),
% 2.36/1.01    inference(cnf_transformation,[],[f43])).
% 2.36/1.01  
% 2.36/1.01  fof(f14,axiom,(
% 2.36/1.01    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.36/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/1.01  
% 2.36/1.01  fof(f24,plain,(
% 2.36/1.01    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.36/1.01    inference(ennf_transformation,[],[f14])).
% 2.36/1.01  
% 2.36/1.01  fof(f25,plain,(
% 2.36/1.01    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.36/1.01    inference(flattening,[],[f24])).
% 2.36/1.01  
% 2.36/1.01  fof(f63,plain,(
% 2.36/1.01    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.36/1.01    inference(cnf_transformation,[],[f25])).
% 2.36/1.01  
% 2.36/1.01  fof(f7,axiom,(
% 2.36/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.36/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/1.01  
% 2.36/1.01  fof(f55,plain,(
% 2.36/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.36/1.01    inference(cnf_transformation,[],[f7])).
% 2.36/1.01  
% 2.36/1.01  fof(f72,plain,(
% 2.36/1.01    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.36/1.01    inference(definition_unfolding,[],[f63,f55])).
% 2.36/1.01  
% 2.36/1.01  fof(f65,plain,(
% 2.36/1.01    ~v1_xboole_0(sK2)),
% 2.36/1.01    inference(cnf_transformation,[],[f43])).
% 2.36/1.01  
% 2.36/1.01  fof(f13,axiom,(
% 2.36/1.01    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.36/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/1.01  
% 2.36/1.01  fof(f22,plain,(
% 2.36/1.01    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.36/1.01    inference(ennf_transformation,[],[f13])).
% 2.36/1.01  
% 2.36/1.01  fof(f23,plain,(
% 2.36/1.01    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.36/1.01    inference(flattening,[],[f22])).
% 2.36/1.01  
% 2.36/1.01  fof(f62,plain,(
% 2.36/1.01    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.36/1.01    inference(cnf_transformation,[],[f23])).
% 2.36/1.01  
% 2.36/1.01  fof(f2,axiom,(
% 2.36/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.36/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/1.01  
% 2.36/1.01  fof(f18,plain,(
% 2.36/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.36/1.01    inference(ennf_transformation,[],[f2])).
% 2.36/1.01  
% 2.36/1.01  fof(f34,plain,(
% 2.36/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.36/1.01    inference(nnf_transformation,[],[f18])).
% 2.36/1.01  
% 2.36/1.01  fof(f35,plain,(
% 2.36/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.36/1.01    inference(rectify,[],[f34])).
% 2.36/1.01  
% 2.36/1.01  fof(f36,plain,(
% 2.36/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 2.36/1.01    introduced(choice_axiom,[])).
% 2.36/1.01  
% 2.36/1.01  fof(f37,plain,(
% 2.36/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.36/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).
% 2.36/1.01  
% 2.36/1.01  fof(f47,plain,(
% 2.36/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 2.36/1.01    inference(cnf_transformation,[],[f37])).
% 2.36/1.01  
% 2.36/1.01  fof(f12,axiom,(
% 2.36/1.01    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.36/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/1.01  
% 2.36/1.01  fof(f20,plain,(
% 2.36/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.36/1.01    inference(ennf_transformation,[],[f12])).
% 2.36/1.01  
% 2.36/1.01  fof(f21,plain,(
% 2.36/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.36/1.01    inference(flattening,[],[f20])).
% 2.36/1.01  
% 2.36/1.01  fof(f61,plain,(
% 2.36/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.36/1.01    inference(cnf_transformation,[],[f21])).
% 2.36/1.01  
% 2.36/1.01  fof(f46,plain,(
% 2.36/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.36/1.01    inference(cnf_transformation,[],[f37])).
% 2.36/1.01  
% 2.36/1.01  fof(f1,axiom,(
% 2.36/1.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.36/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/1.01  
% 2.36/1.01  fof(f30,plain,(
% 2.36/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.36/1.01    inference(nnf_transformation,[],[f1])).
% 2.36/1.01  
% 2.36/1.01  fof(f31,plain,(
% 2.36/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.36/1.01    inference(rectify,[],[f30])).
% 2.36/1.01  
% 2.36/1.01  fof(f32,plain,(
% 2.36/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.36/1.01    introduced(choice_axiom,[])).
% 2.36/1.01  
% 2.36/1.01  fof(f33,plain,(
% 2.36/1.01    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.36/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 2.36/1.01  
% 2.36/1.01  fof(f44,plain,(
% 2.36/1.01    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.36/1.01    inference(cnf_transformation,[],[f33])).
% 2.36/1.01  
% 2.36/1.01  fof(f3,axiom,(
% 2.36/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.36/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/1.01  
% 2.36/1.01  fof(f38,plain,(
% 2.36/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.36/1.01    inference(nnf_transformation,[],[f3])).
% 2.36/1.01  
% 2.36/1.01  fof(f39,plain,(
% 2.36/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.36/1.01    inference(flattening,[],[f38])).
% 2.36/1.01  
% 2.36/1.01  fof(f51,plain,(
% 2.36/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.36/1.01    inference(cnf_transformation,[],[f39])).
% 2.36/1.01  
% 2.36/1.01  fof(f15,axiom,(
% 2.36/1.01    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 2.36/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/1.01  
% 2.36/1.01  fof(f26,plain,(
% 2.36/1.01    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 2.36/1.01    inference(ennf_transformation,[],[f15])).
% 2.36/1.01  
% 2.36/1.01  fof(f27,plain,(
% 2.36/1.01    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 2.36/1.01    inference(flattening,[],[f26])).
% 2.36/1.01  
% 2.36/1.01  fof(f64,plain,(
% 2.36/1.01    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 2.36/1.01    inference(cnf_transformation,[],[f27])).
% 2.36/1.01  
% 2.36/1.01  fof(f10,axiom,(
% 2.36/1.01    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.36/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/1.01  
% 2.36/1.01  fof(f19,plain,(
% 2.36/1.01    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.36/1.01    inference(ennf_transformation,[],[f10])).
% 2.36/1.01  
% 2.36/1.01  fof(f58,plain,(
% 2.36/1.01    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.36/1.01    inference(cnf_transformation,[],[f19])).
% 2.36/1.01  
% 2.36/1.01  fof(f60,plain,(
% 2.36/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.36/1.01    inference(cnf_transformation,[],[f40])).
% 2.36/1.01  
% 2.36/1.01  fof(f67,plain,(
% 2.36/1.01    v1_subset_1(k6_domain_1(sK2,sK3),sK2)),
% 2.36/1.01    inference(cnf_transformation,[],[f43])).
% 2.36/1.01  
% 2.36/1.01  fof(f68,plain,(
% 2.36/1.01    v1_zfmisc_1(sK2)),
% 2.36/1.01    inference(cnf_transformation,[],[f43])).
% 2.36/1.01  
% 2.36/1.01  fof(f5,axiom,(
% 2.36/1.01    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.36/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/1.01  
% 2.36/1.01  fof(f53,plain,(
% 2.36/1.01    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.36/1.01    inference(cnf_transformation,[],[f5])).
% 2.36/1.01  
% 2.36/1.01  fof(f6,axiom,(
% 2.36/1.01    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.36/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/1.01  
% 2.36/1.01  fof(f54,plain,(
% 2.36/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.36/1.01    inference(cnf_transformation,[],[f6])).
% 2.36/1.01  
% 2.36/1.01  fof(f4,axiom,(
% 2.36/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.36/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/1.01  
% 2.36/1.01  fof(f52,plain,(
% 2.36/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.36/1.01    inference(cnf_transformation,[],[f4])).
% 2.36/1.01  
% 2.36/1.01  fof(f69,plain,(
% 2.36/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 2.36/1.01    inference(definition_unfolding,[],[f54,f52])).
% 2.36/1.01  
% 2.36/1.01  fof(f70,plain,(
% 2.36/1.01    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 2.36/1.01    inference(definition_unfolding,[],[f53,f69])).
% 2.36/1.01  
% 2.36/1.01  fof(f8,axiom,(
% 2.36/1.01    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 2.36/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/1.01  
% 2.36/1.01  fof(f56,plain,(
% 2.36/1.01    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 2.36/1.01    inference(cnf_transformation,[],[f8])).
% 2.36/1.01  
% 2.36/1.01  fof(f71,plain,(
% 2.36/1.01    ( ! [X0,X1] : (k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,k2_tarski(X0,X0)))) != k1_xboole_0) )),
% 2.36/1.01    inference(definition_unfolding,[],[f56,f69,f55])).
% 2.36/1.01  
% 2.36/1.01  cnf(c_10,plain,
% 2.36/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.36/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_864,plain,
% 2.36/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.36/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_13,plain,
% 2.36/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.36/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_862,plain,
% 2.36/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.36/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 2.36/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_1143,plain,
% 2.36/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.36/1.01      inference(superposition,[status(thm)],[c_864,c_862]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_20,negated_conjecture,
% 2.36/1.01      ( m1_subset_1(sK3,sK2) ),
% 2.36/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_858,plain,
% 2.36/1.01      ( m1_subset_1(sK3,sK2) = iProver_top ),
% 2.36/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_16,plain,
% 2.36/1.01      ( ~ m1_subset_1(X0,X1)
% 2.36/1.01      | v1_xboole_0(X1)
% 2.36/1.01      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 2.36/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_859,plain,
% 2.36/1.01      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
% 2.36/1.01      | m1_subset_1(X1,X0) != iProver_top
% 2.36/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.36/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_1874,plain,
% 2.36/1.01      ( k6_domain_1(sK2,sK3) = k2_tarski(sK3,sK3)
% 2.36/1.01      | v1_xboole_0(sK2) = iProver_top ),
% 2.36/1.01      inference(superposition,[status(thm)],[c_858,c_859]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_21,negated_conjecture,
% 2.36/1.01      ( ~ v1_xboole_0(sK2) ),
% 2.36/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_1021,plain,
% 2.36/1.01      ( ~ m1_subset_1(sK3,sK2)
% 2.36/1.01      | v1_xboole_0(sK2)
% 2.36/1.01      | k6_domain_1(sK2,sK3) = k2_tarski(sK3,sK3) ),
% 2.36/1.01      inference(instantiation,[status(thm)],[c_16]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_2254,plain,
% 2.36/1.01      ( k6_domain_1(sK2,sK3) = k2_tarski(sK3,sK3) ),
% 2.36/1.01      inference(global_propositional_subsumption,
% 2.36/1.01                [status(thm)],
% 2.36/1.01                [c_1874,c_21,c_20,c_1021]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_15,plain,
% 2.36/1.01      ( ~ m1_subset_1(X0,X1)
% 2.36/1.01      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 2.36/1.01      | v1_xboole_0(X1) ),
% 2.36/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_860,plain,
% 2.36/1.01      ( m1_subset_1(X0,X1) != iProver_top
% 2.36/1.01      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
% 2.36/1.01      | v1_xboole_0(X1) = iProver_top ),
% 2.36/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_2259,plain,
% 2.36/1.01      ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(sK2)) = iProver_top
% 2.36/1.01      | m1_subset_1(sK3,sK2) != iProver_top
% 2.36/1.01      | v1_xboole_0(sK2) = iProver_top ),
% 2.36/1.01      inference(superposition,[status(thm)],[c_2254,c_860]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_22,plain,
% 2.36/1.01      ( v1_xboole_0(sK2) != iProver_top ),
% 2.36/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_23,plain,
% 2.36/1.01      ( m1_subset_1(sK3,sK2) = iProver_top ),
% 2.36/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_2322,plain,
% 2.36/1.01      ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(sK2)) = iProver_top ),
% 2.36/1.01      inference(global_propositional_subsumption,
% 2.36/1.01                [status(thm)],
% 2.36/1.01                [c_2259,c_22,c_23]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_2105,plain,
% 2.36/1.01      ( k2_tarski(k6_domain_1(X0,X1),k6_domain_1(X0,X1)) = k6_domain_1(k1_zfmisc_1(X0),k6_domain_1(X0,X1))
% 2.36/1.01      | m1_subset_1(X1,X0) != iProver_top
% 2.36/1.01      | v1_xboole_0(X0) = iProver_top
% 2.36/1.01      | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
% 2.36/1.01      inference(superposition,[status(thm)],[c_860,c_859]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_4870,plain,
% 2.36/1.01      ( k2_tarski(k6_domain_1(k1_zfmisc_1(sK2),k2_tarski(sK3,sK3)),k6_domain_1(k1_zfmisc_1(sK2),k2_tarski(sK3,sK3))) = k6_domain_1(k1_zfmisc_1(k1_zfmisc_1(sK2)),k6_domain_1(k1_zfmisc_1(sK2),k2_tarski(sK3,sK3)))
% 2.36/1.01      | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top
% 2.36/1.01      | v1_xboole_0(k1_zfmisc_1(sK2)) = iProver_top ),
% 2.36/1.01      inference(superposition,[status(thm)],[c_2322,c_2105]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_3,plain,
% 2.36/1.01      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 2.36/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_868,plain,
% 2.36/1.01      ( r1_tarski(X0,X1) = iProver_top
% 2.36/1.01      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 2.36/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_14,plain,
% 2.36/1.01      ( m1_subset_1(X0,X1)
% 2.36/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.36/1.01      | ~ r2_hidden(X0,X2) ),
% 2.36/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_861,plain,
% 2.36/1.01      ( m1_subset_1(X0,X1) = iProver_top
% 2.36/1.01      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 2.36/1.01      | r2_hidden(X0,X2) != iProver_top ),
% 2.36/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_2328,plain,
% 2.36/1.01      ( m1_subset_1(X0,sK2) = iProver_top
% 2.36/1.01      | r2_hidden(X0,k2_tarski(sK3,sK3)) != iProver_top ),
% 2.36/1.01      inference(superposition,[status(thm)],[c_2322,c_861]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_2461,plain,
% 2.36/1.01      ( m1_subset_1(sK1(k2_tarski(sK3,sK3),X0),sK2) = iProver_top
% 2.36/1.01      | r1_tarski(k2_tarski(sK3,sK3),X0) = iProver_top ),
% 2.36/1.01      inference(superposition,[status(thm)],[c_868,c_2328]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_2947,plain,
% 2.36/1.01      ( k2_tarski(sK1(k2_tarski(sK3,sK3),X0),sK1(k2_tarski(sK3,sK3),X0)) = k6_domain_1(sK2,sK1(k2_tarski(sK3,sK3),X0))
% 2.36/1.01      | r1_tarski(k2_tarski(sK3,sK3),X0) = iProver_top
% 2.36/1.01      | v1_xboole_0(sK2) = iProver_top ),
% 2.36/1.01      inference(superposition,[status(thm)],[c_2461,c_859]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_3106,plain,
% 2.36/1.01      ( r1_tarski(k2_tarski(sK3,sK3),X0) = iProver_top
% 2.36/1.01      | k2_tarski(sK1(k2_tarski(sK3,sK3),X0),sK1(k2_tarski(sK3,sK3),X0)) = k6_domain_1(sK2,sK1(k2_tarski(sK3,sK3),X0)) ),
% 2.36/1.01      inference(global_propositional_subsumption,[status(thm)],[c_2947,c_22]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_3107,plain,
% 2.36/1.01      ( k2_tarski(sK1(k2_tarski(sK3,sK3),X0),sK1(k2_tarski(sK3,sK3),X0)) = k6_domain_1(sK2,sK1(k2_tarski(sK3,sK3),X0))
% 2.36/1.01      | r1_tarski(k2_tarski(sK3,sK3),X0) = iProver_top ),
% 2.36/1.01      inference(renaming,[status(thm)],[c_3106]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_4,plain,
% 2.36/1.01      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 2.36/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_867,plain,
% 2.36/1.01      ( r1_tarski(X0,X1) != iProver_top
% 2.36/1.01      | r2_hidden(X2,X0) != iProver_top
% 2.36/1.01      | r2_hidden(X2,X1) = iProver_top ),
% 2.36/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_3112,plain,
% 2.36/1.01      ( k2_tarski(sK1(k2_tarski(sK3,sK3),X0),sK1(k2_tarski(sK3,sK3),X0)) = k6_domain_1(sK2,sK1(k2_tarski(sK3,sK3),X0))
% 2.36/1.01      | r2_hidden(X1,X0) = iProver_top
% 2.36/1.01      | r2_hidden(X1,k2_tarski(sK3,sK3)) != iProver_top ),
% 2.36/1.01      inference(superposition,[status(thm)],[c_3107,c_867]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_3397,plain,
% 2.36/1.01      ( k2_tarski(sK1(k2_tarski(sK3,sK3),X0),sK1(k2_tarski(sK3,sK3),X0)) = k6_domain_1(sK2,sK1(k2_tarski(sK3,sK3),X0))
% 2.36/1.01      | r1_tarski(k2_tarski(sK3,sK3),X1) = iProver_top
% 2.36/1.01      | r2_hidden(sK1(k2_tarski(sK3,sK3),X1),X0) = iProver_top ),
% 2.36/1.01      inference(superposition,[status(thm)],[c_868,c_3112]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_1,plain,
% 2.36/1.01      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.36/1.01      inference(cnf_transformation,[],[f44]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_870,plain,
% 2.36/1.01      ( r2_hidden(X0,X1) != iProver_top | v1_xboole_0(X1) != iProver_top ),
% 2.36/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_4242,plain,
% 2.36/1.01      ( k2_tarski(sK1(k2_tarski(sK3,sK3),X0),sK1(k2_tarski(sK3,sK3),X0)) = k6_domain_1(sK2,sK1(k2_tarski(sK3,sK3),X0))
% 2.36/1.01      | r1_tarski(k2_tarski(sK3,sK3),X1) = iProver_top
% 2.36/1.01      | v1_xboole_0(X0) != iProver_top ),
% 2.36/1.01      inference(superposition,[status(thm)],[c_3397,c_870]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_5292,plain,
% 2.36/1.01      ( k2_tarski(k6_domain_1(k1_zfmisc_1(sK2),k2_tarski(sK3,sK3)),k6_domain_1(k1_zfmisc_1(sK2),k2_tarski(sK3,sK3))) = k6_domain_1(k1_zfmisc_1(k1_zfmisc_1(sK2)),k6_domain_1(k1_zfmisc_1(sK2),k2_tarski(sK3,sK3)))
% 2.36/1.01      | k2_tarski(sK1(k2_tarski(sK3,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2))),sK1(k2_tarski(sK3,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2)))) = k6_domain_1(sK2,sK1(k2_tarski(sK3,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2))))
% 2.36/1.01      | r1_tarski(k2_tarski(sK3,sK3),X0) = iProver_top
% 2.36/1.01      | v1_xboole_0(k1_zfmisc_1(sK2)) = iProver_top ),
% 2.36/1.01      inference(superposition,[status(thm)],[c_4870,c_4242]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_5,plain,
% 2.36/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.36/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_866,plain,
% 2.36/1.01      ( X0 = X1
% 2.36/1.01      | r1_tarski(X1,X0) != iProver_top
% 2.36/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 2.36/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_5320,plain,
% 2.36/1.01      ( k2_tarski(k6_domain_1(k1_zfmisc_1(sK2),k2_tarski(sK3,sK3)),k6_domain_1(k1_zfmisc_1(sK2),k2_tarski(sK3,sK3))) = k6_domain_1(k1_zfmisc_1(k1_zfmisc_1(sK2)),k6_domain_1(k1_zfmisc_1(sK2),k2_tarski(sK3,sK3)))
% 2.36/1.01      | k2_tarski(sK1(k2_tarski(sK3,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2))),sK1(k2_tarski(sK3,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2)))) = k6_domain_1(sK2,sK1(k2_tarski(sK3,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2))))
% 2.36/1.01      | k2_tarski(sK3,sK3) = X0
% 2.36/1.01      | r1_tarski(X0,k2_tarski(sK3,sK3)) != iProver_top
% 2.36/1.01      | v1_xboole_0(k1_zfmisc_1(sK2)) = iProver_top ),
% 2.36/1.01      inference(superposition,[status(thm)],[c_5292,c_866]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_2793,plain,
% 2.36/1.01      ( ~ r1_tarski(X0,k2_tarski(sK3,sK3))
% 2.36/1.01      | ~ r1_tarski(k2_tarski(sK3,sK3),X0)
% 2.36/1.01      | k2_tarski(sK3,sK3) = X0 ),
% 2.36/1.01      inference(instantiation,[status(thm)],[c_5]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_2794,plain,
% 2.36/1.01      ( k2_tarski(sK3,sK3) = X0
% 2.36/1.01      | r1_tarski(X0,k2_tarski(sK3,sK3)) != iProver_top
% 2.36/1.01      | r1_tarski(k2_tarski(sK3,sK3),X0) != iProver_top ),
% 2.36/1.01      inference(predicate_to_equality,[status(thm)],[c_2793]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_5319,plain,
% 2.36/1.01      ( k2_tarski(k6_domain_1(k1_zfmisc_1(sK2),k2_tarski(sK3,sK3)),k6_domain_1(k1_zfmisc_1(sK2),k2_tarski(sK3,sK3))) = k6_domain_1(k1_zfmisc_1(k1_zfmisc_1(sK2)),k6_domain_1(k1_zfmisc_1(sK2),k2_tarski(sK3,sK3)))
% 2.36/1.01      | k2_tarski(sK1(k2_tarski(sK3,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2))),sK1(k2_tarski(sK3,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2)))) = k6_domain_1(sK2,sK1(k2_tarski(sK3,sK3),k1_zfmisc_1(k1_zfmisc_1(sK2))))
% 2.36/1.01      | r2_hidden(X0,X1) = iProver_top
% 2.36/1.01      | r2_hidden(X0,k2_tarski(sK3,sK3)) != iProver_top
% 2.36/1.01      | v1_xboole_0(k1_zfmisc_1(sK2)) = iProver_top ),
% 2.36/1.01      inference(superposition,[status(thm)],[c_5292,c_867]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_17,plain,
% 2.36/1.01      ( ~ v1_subset_1(X0,X1)
% 2.36/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.36/1.01      | ~ v1_zfmisc_1(X1)
% 2.36/1.01      | v1_xboole_0(X1)
% 2.36/1.01      | v1_xboole_0(X0) ),
% 2.36/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_11,plain,
% 2.36/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.36/1.01      | ~ v1_xboole_0(X1)
% 2.36/1.01      | v1_xboole_0(X0) ),
% 2.36/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_109,plain,
% 2.36/1.01      ( ~ v1_zfmisc_1(X1)
% 2.36/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.36/1.01      | ~ v1_subset_1(X0,X1)
% 2.36/1.01      | v1_xboole_0(X0) ),
% 2.36/1.01      inference(global_propositional_subsumption,[status(thm)],[c_17,c_11]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_110,plain,
% 2.36/1.01      ( ~ v1_subset_1(X0,X1)
% 2.36/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.36/1.01      | ~ v1_zfmisc_1(X1)
% 2.36/1.01      | v1_xboole_0(X0) ),
% 2.36/1.01      inference(renaming,[status(thm)],[c_109]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_12,plain,
% 2.36/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.36/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_155,plain,
% 2.36/1.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.36/1.01      inference(prop_impl,[status(thm)],[c_12]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_156,plain,
% 2.36/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.36/1.01      inference(renaming,[status(thm)],[c_155]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_191,plain,
% 2.36/1.01      ( ~ v1_subset_1(X0,X1)
% 2.36/1.01      | ~ r1_tarski(X0,X1)
% 2.36/1.01      | ~ v1_zfmisc_1(X1)
% 2.36/1.01      | v1_xboole_0(X0) ),
% 2.36/1.01      inference(bin_hyper_res,[status(thm)],[c_110,c_156]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_19,negated_conjecture,
% 2.36/1.01      ( v1_subset_1(k6_domain_1(sK2,sK3),sK2) ),
% 2.36/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_262,plain,
% 2.36/1.01      ( ~ r1_tarski(X0,X1)
% 2.36/1.01      | ~ v1_zfmisc_1(X1)
% 2.36/1.01      | v1_xboole_0(X0)
% 2.36/1.01      | k6_domain_1(sK2,sK3) != X0
% 2.36/1.01      | sK2 != X1 ),
% 2.36/1.01      inference(resolution_lifted,[status(thm)],[c_191,c_19]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_263,plain,
% 2.36/1.01      ( ~ r1_tarski(k6_domain_1(sK2,sK3),sK2)
% 2.36/1.01      | ~ v1_zfmisc_1(sK2)
% 2.36/1.01      | v1_xboole_0(k6_domain_1(sK2,sK3)) ),
% 2.36/1.01      inference(unflattening,[status(thm)],[c_262]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_18,negated_conjecture,
% 2.36/1.01      ( v1_zfmisc_1(sK2) ),
% 2.36/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_265,plain,
% 2.36/1.01      ( ~ r1_tarski(k6_domain_1(sK2,sK3),sK2)
% 2.36/1.01      | v1_xboole_0(k6_domain_1(sK2,sK3)) ),
% 2.36/1.01      inference(global_propositional_subsumption,[status(thm)],[c_263,c_18]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_855,plain,
% 2.36/1.01      ( r1_tarski(k6_domain_1(sK2,sK3),sK2) != iProver_top
% 2.36/1.01      | v1_xboole_0(k6_domain_1(sK2,sK3)) = iProver_top ),
% 2.36/1.01      inference(predicate_to_equality,[status(thm)],[c_265]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_25,plain,
% 2.36/1.01      ( v1_zfmisc_1(sK2) = iProver_top ),
% 2.36/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_264,plain,
% 2.36/1.01      ( r1_tarski(k6_domain_1(sK2,sK3),sK2) != iProver_top
% 2.36/1.01      | v1_zfmisc_1(sK2) != iProver_top
% 2.36/1.01      | v1_xboole_0(k6_domain_1(sK2,sK3)) = iProver_top ),
% 2.36/1.01      inference(predicate_to_equality,[status(thm)],[c_263]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_986,plain,
% 2.36/1.01      ( ~ m1_subset_1(k6_domain_1(sK2,sK3),k1_zfmisc_1(sK2))
% 2.36/1.01      | r1_tarski(k6_domain_1(sK2,sK3),sK2) ),
% 2.36/1.01      inference(instantiation,[status(thm)],[c_13]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_987,plain,
% 2.36/1.01      ( m1_subset_1(k6_domain_1(sK2,sK3),k1_zfmisc_1(sK2)) != iProver_top
% 2.36/1.01      | r1_tarski(k6_domain_1(sK2,sK3),sK2) = iProver_top ),
% 2.36/1.01      inference(predicate_to_equality,[status(thm)],[c_986]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_1008,plain,
% 2.36/1.01      ( m1_subset_1(k6_domain_1(sK2,sK3),k1_zfmisc_1(sK2))
% 2.36/1.01      | ~ m1_subset_1(sK3,sK2)
% 2.36/1.01      | v1_xboole_0(sK2) ),
% 2.36/1.01      inference(instantiation,[status(thm)],[c_15]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_1009,plain,
% 2.36/1.01      ( m1_subset_1(k6_domain_1(sK2,sK3),k1_zfmisc_1(sK2)) = iProver_top
% 2.36/1.01      | m1_subset_1(sK3,sK2) != iProver_top
% 2.36/1.01      | v1_xboole_0(sK2) = iProver_top ),
% 2.36/1.01      inference(predicate_to_equality,[status(thm)],[c_1008]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_1046,plain,
% 2.36/1.01      ( v1_xboole_0(k6_domain_1(sK2,sK3)) = iProver_top ),
% 2.36/1.01      inference(global_propositional_subsumption,
% 2.36/1.01                [status(thm)],
% 2.36/1.01                [c_855,c_22,c_23,c_25,c_264,c_987,c_1009]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_2257,plain,
% 2.36/1.01      ( v1_xboole_0(k2_tarski(sK3,sK3)) = iProver_top ),
% 2.36/1.01      inference(demodulation,[status(thm)],[c_2254,c_1046]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_4006,plain,
% 2.36/1.01      ( ~ r2_hidden(X0,k2_tarski(sK3,sK3))
% 2.36/1.01      | ~ v1_xboole_0(k2_tarski(sK3,sK3)) ),
% 2.36/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_4007,plain,
% 2.36/1.01      ( r2_hidden(X0,k2_tarski(sK3,sK3)) != iProver_top
% 2.36/1.01      | v1_xboole_0(k2_tarski(sK3,sK3)) != iProver_top ),
% 2.36/1.01      inference(predicate_to_equality,[status(thm)],[c_4006]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_5782,plain,
% 2.36/1.01      ( r2_hidden(X0,k2_tarski(sK3,sK3)) != iProver_top ),
% 2.36/1.01      inference(global_propositional_subsumption,
% 2.36/1.01                [status(thm)],
% 2.36/1.01                [c_5319,c_2257,c_4007]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_5790,plain,
% 2.36/1.01      ( r1_tarski(k2_tarski(sK3,sK3),X0) = iProver_top ),
% 2.36/1.01      inference(superposition,[status(thm)],[c_868,c_5782]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_5938,plain,
% 2.36/1.01      ( r1_tarski(X0,k2_tarski(sK3,sK3)) != iProver_top
% 2.36/1.01      | k2_tarski(sK3,sK3) = X0 ),
% 2.36/1.01      inference(global_propositional_subsumption,
% 2.36/1.01                [status(thm)],
% 2.36/1.01                [c_5320,c_2794,c_5790]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_5939,plain,
% 2.36/1.01      ( k2_tarski(sK3,sK3) = X0
% 2.36/1.01      | r1_tarski(X0,k2_tarski(sK3,sK3)) != iProver_top ),
% 2.36/1.01      inference(renaming,[status(thm)],[c_5938]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_5946,plain,
% 2.36/1.01      ( k2_tarski(sK3,sK3) = k1_xboole_0 ),
% 2.36/1.01      inference(superposition,[status(thm)],[c_1143,c_5939]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_8,plain,
% 2.36/1.01      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
% 2.36/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_9,plain,
% 2.36/1.01      ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,k2_tarski(X0,X0)))) != k1_xboole_0 ),
% 2.36/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_1281,plain,
% 2.36/1.01      ( k2_tarski(X0,X0) != k1_xboole_0 ),
% 2.36/1.01      inference(superposition,[status(thm)],[c_8,c_9]) ).
% 2.36/1.01  
% 2.36/1.01  cnf(c_6579,plain,
% 2.36/1.01      ( $false ),
% 2.36/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_5946,c_1281]) ).
% 2.36/1.01  
% 2.36/1.01  
% 2.36/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.36/1.01  
% 2.36/1.01  ------                               Statistics
% 2.36/1.01  
% 2.36/1.01  ------ General
% 2.36/1.01  
% 2.36/1.01  abstr_ref_over_cycles:                  0
% 2.36/1.01  abstr_ref_under_cycles:                 0
% 2.36/1.01  gc_basic_clause_elim:                   0
% 2.36/1.01  forced_gc_time:                         0
% 2.36/1.01  parsing_time:                           0.009
% 2.36/1.01  unif_index_cands_time:                  0.
% 2.36/1.01  unif_index_add_time:                    0.
% 2.36/1.01  orderings_time:                         0.
% 2.36/1.01  out_proof_time:                         0.011
% 2.36/1.01  total_time:                             0.203
% 2.36/1.01  num_of_symbols:                         47
% 2.36/1.01  num_of_terms:                           5556
% 2.36/1.01  
% 2.36/1.01  ------ Preprocessing
% 2.36/1.01  
% 2.36/1.01  num_of_splits:                          0
% 2.36/1.01  num_of_split_atoms:                     0
% 2.36/1.01  num_of_reused_defs:                     0
% 2.36/1.01  num_eq_ax_congr_red:                    23
% 2.36/1.01  num_of_sem_filtered_clauses:            1
% 2.36/1.01  num_of_subtypes:                        0
% 2.36/1.01  monotx_restored_types:                  0
% 2.36/1.01  sat_num_of_epr_types:                   0
% 2.36/1.01  sat_num_of_non_cyclic_types:            0
% 2.36/1.01  sat_guarded_non_collapsed_types:        0
% 2.36/1.01  num_pure_diseq_elim:                    0
% 2.36/1.01  simp_replaced_by:                       0
% 2.36/1.01  res_preprocessed:                       97
% 2.36/1.01  prep_upred:                             0
% 2.36/1.01  prep_unflattend:                        2
% 2.36/1.01  smt_new_axioms:                         0
% 2.36/1.01  pred_elim_cands:                        4
% 2.36/1.01  pred_elim:                              2
% 2.36/1.01  pred_elim_cl:                           2
% 2.36/1.01  pred_elim_cycles:                       4
% 2.36/1.01  merged_defs:                            8
% 2.36/1.01  merged_defs_ncl:                        0
% 2.36/1.01  bin_hyper_res:                          10
% 2.36/1.01  prep_cycles:                            4
% 2.36/1.01  pred_elim_time:                         0.
% 2.36/1.01  splitting_time:                         0.
% 2.36/1.01  sem_filter_time:                        0.
% 2.36/1.01  monotx_time:                            0.001
% 2.36/1.01  subtype_inf_time:                       0.
% 2.36/1.01  
% 2.36/1.01  ------ Problem properties
% 2.36/1.01  
% 2.36/1.01  clauses:                                19
% 2.36/1.01  conjectures:                            2
% 2.36/1.01  epr:                                    7
% 2.36/1.01  horn:                                   15
% 2.36/1.01  ground:                                 3
% 2.36/1.01  unary:                                  6
% 2.36/1.01  binary:                                 7
% 2.36/1.01  lits:                                   38
% 2.36/1.01  lits_eq:                                4
% 2.36/1.01  fd_pure:                                0
% 2.36/1.01  fd_pseudo:                              0
% 2.36/1.01  fd_cond:                                0
% 2.36/1.01  fd_pseudo_cond:                         1
% 2.36/1.01  ac_symbols:                             0
% 2.36/1.01  
% 2.36/1.01  ------ Propositional Solver
% 2.36/1.01  
% 2.36/1.01  prop_solver_calls:                      28
% 2.36/1.01  prop_fast_solver_calls:                 678
% 2.36/1.01  smt_solver_calls:                       0
% 2.36/1.01  smt_fast_solver_calls:                  0
% 2.36/1.01  prop_num_of_clauses:                    2489
% 2.36/1.01  prop_preprocess_simplified:             6371
% 2.36/1.01  prop_fo_subsumed:                       29
% 2.36/1.01  prop_solver_time:                       0.
% 2.36/1.01  smt_solver_time:                        0.
% 2.36/1.01  smt_fast_solver_time:                   0.
% 2.36/1.01  prop_fast_solver_time:                  0.
% 2.36/1.01  prop_unsat_core_time:                   0.
% 2.36/1.01  
% 2.36/1.01  ------ QBF
% 2.36/1.01  
% 2.36/1.01  qbf_q_res:                              0
% 2.36/1.01  qbf_num_tautologies:                    0
% 2.36/1.01  qbf_prep_cycles:                        0
% 2.36/1.01  
% 2.36/1.01  ------ BMC1
% 2.36/1.01  
% 2.36/1.01  bmc1_current_bound:                     -1
% 2.36/1.01  bmc1_last_solved_bound:                 -1
% 2.36/1.01  bmc1_unsat_core_size:                   -1
% 2.36/1.01  bmc1_unsat_core_parents_size:           -1
% 2.36/1.01  bmc1_merge_next_fun:                    0
% 2.36/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.36/1.01  
% 2.36/1.01  ------ Instantiation
% 2.36/1.01  
% 2.36/1.01  inst_num_of_clauses:                    743
% 2.36/1.01  inst_num_in_passive:                    128
% 2.36/1.01  inst_num_in_active:                     364
% 2.36/1.01  inst_num_in_unprocessed:                251
% 2.36/1.01  inst_num_of_loops:                      410
% 2.36/1.01  inst_num_of_learning_restarts:          0
% 2.36/1.01  inst_num_moves_active_passive:          44
% 2.36/1.01  inst_lit_activity:                      0
% 2.36/1.01  inst_lit_activity_moves:                0
% 2.36/1.01  inst_num_tautologies:                   0
% 2.36/1.01  inst_num_prop_implied:                  0
% 2.36/1.01  inst_num_existing_simplified:           0
% 2.36/1.01  inst_num_eq_res_simplified:             0
% 2.36/1.01  inst_num_child_elim:                    0
% 2.36/1.01  inst_num_of_dismatching_blockings:      293
% 2.36/1.01  inst_num_of_non_proper_insts:           803
% 2.36/1.01  inst_num_of_duplicates:                 0
% 2.36/1.01  inst_inst_num_from_inst_to_res:         0
% 2.36/1.01  inst_dismatching_checking_time:         0.
% 2.36/1.01  
% 2.36/1.01  ------ Resolution
% 2.36/1.01  
% 2.36/1.01  res_num_of_clauses:                     0
% 2.36/1.01  res_num_in_passive:                     0
% 2.36/1.01  res_num_in_active:                      0
% 2.36/1.01  res_num_of_loops:                       101
% 2.36/1.01  res_forward_subset_subsumed:            75
% 2.36/1.01  res_backward_subset_subsumed:           0
% 2.36/1.01  res_forward_subsumed:                   0
% 2.36/1.01  res_backward_subsumed:                  0
% 2.36/1.01  res_forward_subsumption_resolution:     0
% 2.36/1.01  res_backward_subsumption_resolution:    0
% 2.36/1.01  res_clause_to_clause_subsumption:       522
% 2.36/1.01  res_orphan_elimination:                 0
% 2.36/1.01  res_tautology_del:                      91
% 2.36/1.01  res_num_eq_res_simplified:              0
% 2.36/1.01  res_num_sel_changes:                    0
% 2.36/1.01  res_moves_from_active_to_pass:          0
% 2.36/1.01  
% 2.36/1.01  ------ Superposition
% 2.36/1.01  
% 2.36/1.01  sup_time_total:                         0.
% 2.36/1.01  sup_time_generating:                    0.
% 2.36/1.01  sup_time_sim_full:                      0.
% 2.36/1.01  sup_time_sim_immed:                     0.
% 2.36/1.01  
% 2.36/1.01  sup_num_of_clauses:                     122
% 2.36/1.01  sup_num_in_active:                      72
% 2.36/1.01  sup_num_in_passive:                     50
% 2.36/1.01  sup_num_of_loops:                       80
% 2.36/1.01  sup_fw_superposition:                   89
% 2.36/1.01  sup_bw_superposition:                   124
% 2.36/1.01  sup_immediate_simplified:               43
% 2.36/1.01  sup_given_eliminated:                   1
% 2.36/1.01  comparisons_done:                       0
% 2.36/1.01  comparisons_avoided:                    38
% 2.36/1.01  
% 2.36/1.01  ------ Simplifications
% 2.36/1.01  
% 2.36/1.01  
% 2.36/1.01  sim_fw_subset_subsumed:                 40
% 2.36/1.01  sim_bw_subset_subsumed:                 12
% 2.36/1.01  sim_fw_subsumed:                        4
% 2.36/1.01  sim_bw_subsumed:                        0
% 2.36/1.01  sim_fw_subsumption_res:                 5
% 2.36/1.01  sim_bw_subsumption_res:                 0
% 2.36/1.01  sim_tautology_del:                      7
% 2.36/1.01  sim_eq_tautology_del:                   18
% 2.36/1.01  sim_eq_res_simp:                        0
% 2.36/1.01  sim_fw_demodulated:                     0
% 2.36/1.01  sim_bw_demodulated:                     2
% 2.36/1.01  sim_light_normalised:                   1
% 2.36/1.01  sim_joinable_taut:                      0
% 2.36/1.01  sim_joinable_simp:                      0
% 2.36/1.01  sim_ac_normalised:                      0
% 2.36/1.01  sim_smt_subsumption:                    0
% 2.36/1.01  
%------------------------------------------------------------------------------
