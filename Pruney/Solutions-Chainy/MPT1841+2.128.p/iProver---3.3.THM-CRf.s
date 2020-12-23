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
% DateTime   : Thu Dec  3 12:25:13 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 295 expanded)
%              Number of clauses        :   53 (  93 expanded)
%              Number of leaves         :   19 (  71 expanded)
%              Depth                    :   19
%              Number of atoms          :  227 ( 802 expanded)
%              Number of equality atoms :   92 ( 154 expanded)
%              Maximal formula depth    :    8 (   3 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
     => ( v1_zfmisc_1(X0)
        & v1_subset_1(k6_domain_1(X0,sK1),X0)
        & m1_subset_1(sK1,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_zfmisc_1(X0)
            & v1_subset_1(k6_domain_1(X0,X1),X0)
            & m1_subset_1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( v1_zfmisc_1(sK0)
          & v1_subset_1(k6_domain_1(sK0,X1),sK0)
          & m1_subset_1(X1,sK0) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f33,f32])).

fof(f53,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f52,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
         => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
          | v1_xboole_0(k3_xboole_0(X0,X1)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
          | v1_xboole_0(k3_xboole_0(X0,X1)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | v1_xboole_0(k3_xboole_0(X0,X1))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f55,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X1,X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f50,f57])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f37,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f10])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f41,f39])).

fof(f59,plain,(
    ! [X0,X1] : k1_xboole_0 != k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,k1_enumset1(X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f44,f56,f57])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f36,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f36,f56])).

fof(f12,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f54,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_663,plain,
    ( m1_subset_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_665,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_100,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_101,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_100])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_204,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_xboole_0(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_101,c_4])).

cnf(c_661,plain,
    ( k3_xboole_0(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_204])).

cnf(c_1820,plain,
    ( k3_xboole_0(k6_domain_1(X0,X1),X0) = k6_domain_1(X0,X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_665,c_661])).

cnf(c_3373,plain,
    ( k3_xboole_0(k6_domain_1(sK0,sK1),sK0) = k6_domain_1(sK0,sK1)
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_663,c_1820])).

cnf(c_16,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_742,plain,
    ( m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(sK0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1316,plain,
    ( ~ m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(X0))
    | k3_xboole_0(k6_domain_1(sK0,sK1),X0) = k6_domain_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_204])).

cnf(c_1322,plain,
    ( ~ m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | k3_xboole_0(k6_domain_1(sK0,sK1),sK0) = k6_domain_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1316])).

cnf(c_3471,plain,
    ( k3_xboole_0(k6_domain_1(sK0,sK1),sK0) = k6_domain_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3373,c_16,c_15,c_742,c_1322])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_12,plain,
    ( r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | v1_xboole_0(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_13,negated_conjecture,
    ( v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_182,plain,
    ( r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(k3_xboole_0(X0,X1))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_13])).

cnf(c_183,plain,
    ( r1_tarski(sK0,X0)
    | v1_xboole_0(k3_xboole_0(sK0,X0))
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_182])).

cnf(c_187,plain,
    ( v1_xboole_0(k3_xboole_0(sK0,X0))
    | r1_tarski(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_183,c_16])).

cnf(c_188,plain,
    ( r1_tarski(sK0,X0)
    | v1_xboole_0(k3_xboole_0(sK0,X0)) ),
    inference(renaming,[status(thm)],[c_187])).

cnf(c_225,plain,
    ( v1_xboole_0(k3_xboole_0(sK0,X0))
    | X0 != X1
    | k3_xboole_0(X2,X1) = X2
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_188])).

cnf(c_226,plain,
    ( v1_xboole_0(k3_xboole_0(sK0,X0))
    | k3_xboole_0(sK0,X0) = sK0 ),
    inference(unflattening,[status(thm)],[c_225])).

cnf(c_659,plain,
    ( k3_xboole_0(sK0,X0) = sK0
    | v1_xboole_0(k3_xboole_0(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_226])).

cnf(c_959,plain,
    ( k3_xboole_0(sK0,X0) = sK0
    | v1_xboole_0(k3_xboole_0(X0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_659])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_666,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1140,plain,
    ( k3_xboole_0(X0,sK0) = k1_xboole_0
    | k3_xboole_0(sK0,X0) = sK0 ),
    inference(superposition,[status(thm)],[c_959,c_666])).

cnf(c_1248,plain,
    ( k3_xboole_0(X0,sK0) = sK0
    | k3_xboole_0(X0,sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1140,c_0])).

cnf(c_3492,plain,
    ( k6_domain_1(sK0,sK1) = sK0
    | k3_xboole_0(k6_domain_1(sK0,sK1),sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3471,c_1248])).

cnf(c_3511,plain,
    ( k6_domain_1(sK0,sK1) = sK0
    | k6_domain_1(sK0,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3492,c_3471])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_664,plain,
    ( k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0)
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1718,plain,
    ( k1_enumset1(sK1,sK1,sK1) = k6_domain_1(sK0,sK1)
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_663,c_664])).

cnf(c_750,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(sK0)
    | k1_enumset1(sK1,sK1,sK1) = k6_domain_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1843,plain,
    ( k1_enumset1(sK1,sK1,sK1) = k6_domain_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1718,c_16,c_15,c_750])).

cnf(c_2,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_5,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,k1_enumset1(X0,X0,X0)))) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1027,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0))) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2,c_5])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_684,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1,c_2])).

cnf(c_1768,plain,
    ( k1_enumset1(X0,X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1027,c_684])).

cnf(c_1846,plain,
    ( k6_domain_1(sK0,sK1) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1843,c_1768])).

cnf(c_7,plain,
    ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_14,negated_conjecture,
    ( v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_176,plain,
    ( k6_domain_1(sK0,sK1) != k2_subset_1(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_14])).

cnf(c_177,plain,
    ( k6_domain_1(sK0,sK1) != k2_subset_1(sK0) ),
    inference(unflattening,[status(thm)],[c_176])).

cnf(c_6,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_675,plain,
    ( k6_domain_1(sK0,sK1) != sK0 ),
    inference(demodulation,[status(thm)],[c_177,c_6])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3511,c_1846,c_675])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:22:06 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.08/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/0.96  
% 2.08/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.08/0.96  
% 2.08/0.96  ------  iProver source info
% 2.08/0.96  
% 2.08/0.96  git: date: 2020-06-30 10:37:57 +0100
% 2.08/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.08/0.96  git: non_committed_changes: false
% 2.08/0.96  git: last_make_outside_of_git: false
% 2.08/0.96  
% 2.08/0.96  ------ 
% 2.08/0.96  
% 2.08/0.96  ------ Input Options
% 2.08/0.96  
% 2.08/0.96  --out_options                           all
% 2.08/0.96  --tptp_safe_out                         true
% 2.08/0.96  --problem_path                          ""
% 2.08/0.96  --include_path                          ""
% 2.08/0.96  --clausifier                            res/vclausify_rel
% 2.08/0.96  --clausifier_options                    --mode clausify
% 2.08/0.96  --stdin                                 false
% 2.08/0.96  --stats_out                             all
% 2.08/0.96  
% 2.08/0.96  ------ General Options
% 2.08/0.96  
% 2.08/0.96  --fof                                   false
% 2.08/0.96  --time_out_real                         305.
% 2.08/0.96  --time_out_virtual                      -1.
% 2.08/0.96  --symbol_type_check                     false
% 2.08/0.96  --clausify_out                          false
% 2.08/0.96  --sig_cnt_out                           false
% 2.08/0.96  --trig_cnt_out                          false
% 2.08/0.96  --trig_cnt_out_tolerance                1.
% 2.08/0.96  --trig_cnt_out_sk_spl                   false
% 2.08/0.96  --abstr_cl_out                          false
% 2.08/0.96  
% 2.08/0.96  ------ Global Options
% 2.08/0.96  
% 2.08/0.96  --schedule                              default
% 2.08/0.96  --add_important_lit                     false
% 2.08/0.96  --prop_solver_per_cl                    1000
% 2.08/0.96  --min_unsat_core                        false
% 2.08/0.96  --soft_assumptions                      false
% 2.08/0.96  --soft_lemma_size                       3
% 2.08/0.96  --prop_impl_unit_size                   0
% 2.08/0.96  --prop_impl_unit                        []
% 2.08/0.96  --share_sel_clauses                     true
% 2.08/0.96  --reset_solvers                         false
% 2.08/0.96  --bc_imp_inh                            [conj_cone]
% 2.08/0.96  --conj_cone_tolerance                   3.
% 2.08/0.96  --extra_neg_conj                        none
% 2.08/0.96  --large_theory_mode                     true
% 2.08/0.96  --prolific_symb_bound                   200
% 2.08/0.96  --lt_threshold                          2000
% 2.08/0.96  --clause_weak_htbl                      true
% 2.08/0.96  --gc_record_bc_elim                     false
% 2.08/0.96  
% 2.08/0.96  ------ Preprocessing Options
% 2.08/0.96  
% 2.08/0.96  --preprocessing_flag                    true
% 2.08/0.96  --time_out_prep_mult                    0.1
% 2.08/0.96  --splitting_mode                        input
% 2.08/0.96  --splitting_grd                         true
% 2.08/0.96  --splitting_cvd                         false
% 2.08/0.96  --splitting_cvd_svl                     false
% 2.08/0.96  --splitting_nvd                         32
% 2.08/0.96  --sub_typing                            true
% 2.08/0.96  --prep_gs_sim                           true
% 2.08/0.96  --prep_unflatten                        true
% 2.08/0.96  --prep_res_sim                          true
% 2.08/0.96  --prep_upred                            true
% 2.08/0.96  --prep_sem_filter                       exhaustive
% 2.08/0.96  --prep_sem_filter_out                   false
% 2.08/0.96  --pred_elim                             true
% 2.08/0.96  --res_sim_input                         true
% 2.08/0.96  --eq_ax_congr_red                       true
% 2.08/0.96  --pure_diseq_elim                       true
% 2.08/0.96  --brand_transform                       false
% 2.08/0.96  --non_eq_to_eq                          false
% 2.08/0.96  --prep_def_merge                        true
% 2.08/0.96  --prep_def_merge_prop_impl              false
% 2.08/0.96  --prep_def_merge_mbd                    true
% 2.08/0.96  --prep_def_merge_tr_red                 false
% 2.08/0.96  --prep_def_merge_tr_cl                  false
% 2.08/0.96  --smt_preprocessing                     true
% 2.08/0.96  --smt_ac_axioms                         fast
% 2.08/0.96  --preprocessed_out                      false
% 2.08/0.96  --preprocessed_stats                    false
% 2.08/0.96  
% 2.08/0.96  ------ Abstraction refinement Options
% 2.08/0.96  
% 2.08/0.96  --abstr_ref                             []
% 2.08/0.96  --abstr_ref_prep                        false
% 2.08/0.96  --abstr_ref_until_sat                   false
% 2.08/0.96  --abstr_ref_sig_restrict                funpre
% 2.08/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.08/0.96  --abstr_ref_under                       []
% 2.08/0.96  
% 2.08/0.96  ------ SAT Options
% 2.08/0.96  
% 2.08/0.96  --sat_mode                              false
% 2.08/0.96  --sat_fm_restart_options                ""
% 2.08/0.96  --sat_gr_def                            false
% 2.08/0.96  --sat_epr_types                         true
% 2.08/0.96  --sat_non_cyclic_types                  false
% 2.08/0.96  --sat_finite_models                     false
% 2.08/0.96  --sat_fm_lemmas                         false
% 2.08/0.96  --sat_fm_prep                           false
% 2.08/0.96  --sat_fm_uc_incr                        true
% 2.08/0.96  --sat_out_model                         small
% 2.08/0.96  --sat_out_clauses                       false
% 2.08/0.96  
% 2.08/0.96  ------ QBF Options
% 2.08/0.96  
% 2.08/0.96  --qbf_mode                              false
% 2.08/0.96  --qbf_elim_univ                         false
% 2.08/0.96  --qbf_dom_inst                          none
% 2.08/0.96  --qbf_dom_pre_inst                      false
% 2.08/0.96  --qbf_sk_in                             false
% 2.08/0.96  --qbf_pred_elim                         true
% 2.08/0.96  --qbf_split                             512
% 2.08/0.96  
% 2.08/0.96  ------ BMC1 Options
% 2.08/0.96  
% 2.08/0.96  --bmc1_incremental                      false
% 2.08/0.96  --bmc1_axioms                           reachable_all
% 2.08/0.96  --bmc1_min_bound                        0
% 2.08/0.96  --bmc1_max_bound                        -1
% 2.08/0.96  --bmc1_max_bound_default                -1
% 2.08/0.96  --bmc1_symbol_reachability              true
% 2.08/0.96  --bmc1_property_lemmas                  false
% 2.08/0.96  --bmc1_k_induction                      false
% 2.08/0.96  --bmc1_non_equiv_states                 false
% 2.08/0.96  --bmc1_deadlock                         false
% 2.08/0.96  --bmc1_ucm                              false
% 2.08/0.96  --bmc1_add_unsat_core                   none
% 2.08/0.96  --bmc1_unsat_core_children              false
% 2.08/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.08/0.96  --bmc1_out_stat                         full
% 2.08/0.96  --bmc1_ground_init                      false
% 2.08/0.96  --bmc1_pre_inst_next_state              false
% 2.08/0.96  --bmc1_pre_inst_state                   false
% 2.08/0.96  --bmc1_pre_inst_reach_state             false
% 2.08/0.96  --bmc1_out_unsat_core                   false
% 2.08/0.96  --bmc1_aig_witness_out                  false
% 2.08/0.96  --bmc1_verbose                          false
% 2.08/0.96  --bmc1_dump_clauses_tptp                false
% 2.08/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.08/0.96  --bmc1_dump_file                        -
% 2.08/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.08/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.08/0.96  --bmc1_ucm_extend_mode                  1
% 2.08/0.96  --bmc1_ucm_init_mode                    2
% 2.08/0.96  --bmc1_ucm_cone_mode                    none
% 2.08/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.08/0.96  --bmc1_ucm_relax_model                  4
% 2.08/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.08/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.08/0.96  --bmc1_ucm_layered_model                none
% 2.08/0.96  --bmc1_ucm_max_lemma_size               10
% 2.08/0.96  
% 2.08/0.96  ------ AIG Options
% 2.08/0.96  
% 2.08/0.96  --aig_mode                              false
% 2.08/0.96  
% 2.08/0.96  ------ Instantiation Options
% 2.08/0.96  
% 2.08/0.96  --instantiation_flag                    true
% 2.08/0.96  --inst_sos_flag                         false
% 2.08/0.96  --inst_sos_phase                        true
% 2.08/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.08/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.08/0.96  --inst_lit_sel_side                     num_symb
% 2.08/0.96  --inst_solver_per_active                1400
% 2.08/0.96  --inst_solver_calls_frac                1.
% 2.08/0.96  --inst_passive_queue_type               priority_queues
% 2.08/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.08/0.96  --inst_passive_queues_freq              [25;2]
% 2.08/0.96  --inst_dismatching                      true
% 2.08/0.96  --inst_eager_unprocessed_to_passive     true
% 2.08/0.96  --inst_prop_sim_given                   true
% 2.08/0.96  --inst_prop_sim_new                     false
% 2.08/0.96  --inst_subs_new                         false
% 2.08/0.96  --inst_eq_res_simp                      false
% 2.08/0.96  --inst_subs_given                       false
% 2.08/0.96  --inst_orphan_elimination               true
% 2.08/0.96  --inst_learning_loop_flag               true
% 2.08/0.96  --inst_learning_start                   3000
% 2.08/0.96  --inst_learning_factor                  2
% 2.08/0.96  --inst_start_prop_sim_after_learn       3
% 2.08/0.96  --inst_sel_renew                        solver
% 2.08/0.96  --inst_lit_activity_flag                true
% 2.08/0.96  --inst_restr_to_given                   false
% 2.08/0.96  --inst_activity_threshold               500
% 2.08/0.96  --inst_out_proof                        true
% 2.08/0.96  
% 2.08/0.96  ------ Resolution Options
% 2.08/0.96  
% 2.08/0.96  --resolution_flag                       true
% 2.08/0.96  --res_lit_sel                           adaptive
% 2.08/0.96  --res_lit_sel_side                      none
% 2.08/0.96  --res_ordering                          kbo
% 2.08/0.96  --res_to_prop_solver                    active
% 2.08/0.96  --res_prop_simpl_new                    false
% 2.08/0.96  --res_prop_simpl_given                  true
% 2.08/0.96  --res_passive_queue_type                priority_queues
% 2.08/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.08/0.96  --res_passive_queues_freq               [15;5]
% 2.08/0.96  --res_forward_subs                      full
% 2.08/0.96  --res_backward_subs                     full
% 2.08/0.96  --res_forward_subs_resolution           true
% 2.08/0.96  --res_backward_subs_resolution          true
% 2.08/0.96  --res_orphan_elimination                true
% 2.08/0.96  --res_time_limit                        2.
% 2.08/0.96  --res_out_proof                         true
% 2.08/0.96  
% 2.08/0.96  ------ Superposition Options
% 2.08/0.96  
% 2.08/0.96  --superposition_flag                    true
% 2.08/0.96  --sup_passive_queue_type                priority_queues
% 2.08/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.08/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.08/0.96  --demod_completeness_check              fast
% 2.08/0.96  --demod_use_ground                      true
% 2.08/0.96  --sup_to_prop_solver                    passive
% 2.08/0.96  --sup_prop_simpl_new                    true
% 2.08/0.96  --sup_prop_simpl_given                  true
% 2.08/0.96  --sup_fun_splitting                     false
% 2.08/0.96  --sup_smt_interval                      50000
% 2.08/0.96  
% 2.08/0.96  ------ Superposition Simplification Setup
% 2.08/0.96  
% 2.08/0.96  --sup_indices_passive                   []
% 2.08/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.08/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/0.96  --sup_full_bw                           [BwDemod]
% 2.08/0.96  --sup_immed_triv                        [TrivRules]
% 2.08/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.08/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/0.96  --sup_immed_bw_main                     []
% 2.08/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.08/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/0.96  
% 2.08/0.96  ------ Combination Options
% 2.08/0.96  
% 2.08/0.96  --comb_res_mult                         3
% 2.08/0.96  --comb_sup_mult                         2
% 2.08/0.96  --comb_inst_mult                        10
% 2.08/0.96  
% 2.08/0.96  ------ Debug Options
% 2.08/0.96  
% 2.08/0.96  --dbg_backtrace                         false
% 2.08/0.96  --dbg_dump_prop_clauses                 false
% 2.08/0.96  --dbg_dump_prop_clauses_file            -
% 2.08/0.96  --dbg_out_stat                          false
% 2.08/0.96  ------ Parsing...
% 2.08/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.08/0.96  
% 2.08/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.08/0.96  
% 2.08/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.08/0.96  
% 2.08/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.08/0.96  ------ Proving...
% 2.08/0.96  ------ Problem Properties 
% 2.08/0.96  
% 2.08/0.96  
% 2.08/0.96  clauses                                 14
% 2.08/0.96  conjectures                             2
% 2.08/0.96  EPR                                     3
% 2.08/0.96  Horn                                    10
% 2.08/0.96  unary                                   8
% 2.08/0.96  binary                                  4
% 2.08/0.96  lits                                    22
% 2.08/0.96  lits eq                                 10
% 2.08/0.96  fd_pure                                 0
% 2.08/0.96  fd_pseudo                               0
% 2.08/0.96  fd_cond                                 1
% 2.08/0.96  fd_pseudo_cond                          0
% 2.08/0.96  AC symbols                              0
% 2.08/0.96  
% 2.08/0.96  ------ Schedule dynamic 5 is on 
% 2.08/0.96  
% 2.08/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.08/0.96  
% 2.08/0.96  
% 2.08/0.96  ------ 
% 2.08/0.96  Current options:
% 2.08/0.96  ------ 
% 2.08/0.96  
% 2.08/0.96  ------ Input Options
% 2.08/0.96  
% 2.08/0.96  --out_options                           all
% 2.08/0.96  --tptp_safe_out                         true
% 2.08/0.96  --problem_path                          ""
% 2.08/0.96  --include_path                          ""
% 2.08/0.96  --clausifier                            res/vclausify_rel
% 2.08/0.96  --clausifier_options                    --mode clausify
% 2.08/0.96  --stdin                                 false
% 2.08/0.96  --stats_out                             all
% 2.08/0.96  
% 2.08/0.96  ------ General Options
% 2.08/0.96  
% 2.08/0.96  --fof                                   false
% 2.08/0.96  --time_out_real                         305.
% 2.08/0.96  --time_out_virtual                      -1.
% 2.08/0.96  --symbol_type_check                     false
% 2.08/0.96  --clausify_out                          false
% 2.08/0.96  --sig_cnt_out                           false
% 2.08/0.96  --trig_cnt_out                          false
% 2.08/0.96  --trig_cnt_out_tolerance                1.
% 2.08/0.96  --trig_cnt_out_sk_spl                   false
% 2.08/0.96  --abstr_cl_out                          false
% 2.08/0.96  
% 2.08/0.96  ------ Global Options
% 2.08/0.96  
% 2.08/0.96  --schedule                              default
% 2.08/0.96  --add_important_lit                     false
% 2.08/0.96  --prop_solver_per_cl                    1000
% 2.08/0.96  --min_unsat_core                        false
% 2.08/0.96  --soft_assumptions                      false
% 2.08/0.96  --soft_lemma_size                       3
% 2.08/0.96  --prop_impl_unit_size                   0
% 2.08/0.96  --prop_impl_unit                        []
% 2.08/0.96  --share_sel_clauses                     true
% 2.08/0.96  --reset_solvers                         false
% 2.08/0.96  --bc_imp_inh                            [conj_cone]
% 2.08/0.96  --conj_cone_tolerance                   3.
% 2.08/0.97  --extra_neg_conj                        none
% 2.08/0.97  --large_theory_mode                     true
% 2.08/0.97  --prolific_symb_bound                   200
% 2.08/0.97  --lt_threshold                          2000
% 2.08/0.97  --clause_weak_htbl                      true
% 2.08/0.97  --gc_record_bc_elim                     false
% 2.08/0.97  
% 2.08/0.97  ------ Preprocessing Options
% 2.08/0.97  
% 2.08/0.97  --preprocessing_flag                    true
% 2.08/0.97  --time_out_prep_mult                    0.1
% 2.08/0.97  --splitting_mode                        input
% 2.08/0.97  --splitting_grd                         true
% 2.08/0.97  --splitting_cvd                         false
% 2.08/0.97  --splitting_cvd_svl                     false
% 2.08/0.97  --splitting_nvd                         32
% 2.08/0.97  --sub_typing                            true
% 2.08/0.97  --prep_gs_sim                           true
% 2.08/0.97  --prep_unflatten                        true
% 2.08/0.97  --prep_res_sim                          true
% 2.08/0.97  --prep_upred                            true
% 2.08/0.97  --prep_sem_filter                       exhaustive
% 2.08/0.97  --prep_sem_filter_out                   false
% 2.08/0.97  --pred_elim                             true
% 2.08/0.97  --res_sim_input                         true
% 2.08/0.97  --eq_ax_congr_red                       true
% 2.08/0.97  --pure_diseq_elim                       true
% 2.08/0.97  --brand_transform                       false
% 2.08/0.97  --non_eq_to_eq                          false
% 2.08/0.97  --prep_def_merge                        true
% 2.08/0.97  --prep_def_merge_prop_impl              false
% 2.08/0.97  --prep_def_merge_mbd                    true
% 2.08/0.97  --prep_def_merge_tr_red                 false
% 2.08/0.97  --prep_def_merge_tr_cl                  false
% 2.08/0.97  --smt_preprocessing                     true
% 2.08/0.97  --smt_ac_axioms                         fast
% 2.08/0.97  --preprocessed_out                      false
% 2.08/0.97  --preprocessed_stats                    false
% 2.08/0.97  
% 2.08/0.97  ------ Abstraction refinement Options
% 2.08/0.97  
% 2.08/0.97  --abstr_ref                             []
% 2.08/0.97  --abstr_ref_prep                        false
% 2.08/0.97  --abstr_ref_until_sat                   false
% 2.08/0.97  --abstr_ref_sig_restrict                funpre
% 2.08/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.08/0.97  --abstr_ref_under                       []
% 2.08/0.97  
% 2.08/0.97  ------ SAT Options
% 2.08/0.97  
% 2.08/0.97  --sat_mode                              false
% 2.08/0.97  --sat_fm_restart_options                ""
% 2.08/0.97  --sat_gr_def                            false
% 2.08/0.97  --sat_epr_types                         true
% 2.08/0.97  --sat_non_cyclic_types                  false
% 2.08/0.97  --sat_finite_models                     false
% 2.08/0.97  --sat_fm_lemmas                         false
% 2.08/0.97  --sat_fm_prep                           false
% 2.08/0.97  --sat_fm_uc_incr                        true
% 2.08/0.97  --sat_out_model                         small
% 2.08/0.97  --sat_out_clauses                       false
% 2.08/0.97  
% 2.08/0.97  ------ QBF Options
% 2.08/0.97  
% 2.08/0.97  --qbf_mode                              false
% 2.08/0.97  --qbf_elim_univ                         false
% 2.08/0.97  --qbf_dom_inst                          none
% 2.08/0.97  --qbf_dom_pre_inst                      false
% 2.08/0.97  --qbf_sk_in                             false
% 2.08/0.97  --qbf_pred_elim                         true
% 2.08/0.97  --qbf_split                             512
% 2.08/0.97  
% 2.08/0.97  ------ BMC1 Options
% 2.08/0.97  
% 2.08/0.97  --bmc1_incremental                      false
% 2.08/0.97  --bmc1_axioms                           reachable_all
% 2.08/0.97  --bmc1_min_bound                        0
% 2.08/0.97  --bmc1_max_bound                        -1
% 2.08/0.97  --bmc1_max_bound_default                -1
% 2.08/0.97  --bmc1_symbol_reachability              true
% 2.08/0.97  --bmc1_property_lemmas                  false
% 2.08/0.97  --bmc1_k_induction                      false
% 2.08/0.97  --bmc1_non_equiv_states                 false
% 2.08/0.97  --bmc1_deadlock                         false
% 2.08/0.97  --bmc1_ucm                              false
% 2.08/0.97  --bmc1_add_unsat_core                   none
% 2.08/0.97  --bmc1_unsat_core_children              false
% 2.08/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.08/0.97  --bmc1_out_stat                         full
% 2.08/0.97  --bmc1_ground_init                      false
% 2.08/0.97  --bmc1_pre_inst_next_state              false
% 2.08/0.97  --bmc1_pre_inst_state                   false
% 2.08/0.97  --bmc1_pre_inst_reach_state             false
% 2.08/0.97  --bmc1_out_unsat_core                   false
% 2.08/0.97  --bmc1_aig_witness_out                  false
% 2.08/0.97  --bmc1_verbose                          false
% 2.08/0.97  --bmc1_dump_clauses_tptp                false
% 2.08/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.08/0.97  --bmc1_dump_file                        -
% 2.08/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.08/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.08/0.97  --bmc1_ucm_extend_mode                  1
% 2.08/0.97  --bmc1_ucm_init_mode                    2
% 2.08/0.97  --bmc1_ucm_cone_mode                    none
% 2.08/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.08/0.97  --bmc1_ucm_relax_model                  4
% 2.08/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.08/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.08/0.97  --bmc1_ucm_layered_model                none
% 2.08/0.97  --bmc1_ucm_max_lemma_size               10
% 2.08/0.97  
% 2.08/0.97  ------ AIG Options
% 2.08/0.97  
% 2.08/0.97  --aig_mode                              false
% 2.08/0.97  
% 2.08/0.97  ------ Instantiation Options
% 2.08/0.97  
% 2.08/0.97  --instantiation_flag                    true
% 2.08/0.97  --inst_sos_flag                         false
% 2.08/0.97  --inst_sos_phase                        true
% 2.08/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.08/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.08/0.97  --inst_lit_sel_side                     none
% 2.08/0.97  --inst_solver_per_active                1400
% 2.08/0.97  --inst_solver_calls_frac                1.
% 2.08/0.97  --inst_passive_queue_type               priority_queues
% 2.08/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.08/0.97  --inst_passive_queues_freq              [25;2]
% 2.08/0.97  --inst_dismatching                      true
% 2.08/0.97  --inst_eager_unprocessed_to_passive     true
% 2.08/0.97  --inst_prop_sim_given                   true
% 2.08/0.97  --inst_prop_sim_new                     false
% 2.08/0.97  --inst_subs_new                         false
% 2.08/0.97  --inst_eq_res_simp                      false
% 2.08/0.97  --inst_subs_given                       false
% 2.08/0.97  --inst_orphan_elimination               true
% 2.08/0.97  --inst_learning_loop_flag               true
% 2.08/0.97  --inst_learning_start                   3000
% 2.08/0.97  --inst_learning_factor                  2
% 2.08/0.97  --inst_start_prop_sim_after_learn       3
% 2.08/0.97  --inst_sel_renew                        solver
% 2.08/0.97  --inst_lit_activity_flag                true
% 2.08/0.97  --inst_restr_to_given                   false
% 2.08/0.97  --inst_activity_threshold               500
% 2.08/0.97  --inst_out_proof                        true
% 2.08/0.97  
% 2.08/0.97  ------ Resolution Options
% 2.08/0.97  
% 2.08/0.97  --resolution_flag                       false
% 2.08/0.97  --res_lit_sel                           adaptive
% 2.08/0.97  --res_lit_sel_side                      none
% 2.08/0.97  --res_ordering                          kbo
% 2.08/0.97  --res_to_prop_solver                    active
% 2.08/0.97  --res_prop_simpl_new                    false
% 2.08/0.97  --res_prop_simpl_given                  true
% 2.08/0.97  --res_passive_queue_type                priority_queues
% 2.08/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.08/0.97  --res_passive_queues_freq               [15;5]
% 2.08/0.97  --res_forward_subs                      full
% 2.08/0.97  --res_backward_subs                     full
% 2.08/0.97  --res_forward_subs_resolution           true
% 2.08/0.97  --res_backward_subs_resolution          true
% 2.08/0.97  --res_orphan_elimination                true
% 2.08/0.97  --res_time_limit                        2.
% 2.08/0.97  --res_out_proof                         true
% 2.08/0.97  
% 2.08/0.97  ------ Superposition Options
% 2.08/0.97  
% 2.08/0.97  --superposition_flag                    true
% 2.08/0.97  --sup_passive_queue_type                priority_queues
% 2.08/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.08/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.08/0.97  --demod_completeness_check              fast
% 2.08/0.97  --demod_use_ground                      true
% 2.08/0.97  --sup_to_prop_solver                    passive
% 2.08/0.97  --sup_prop_simpl_new                    true
% 2.08/0.97  --sup_prop_simpl_given                  true
% 2.08/0.97  --sup_fun_splitting                     false
% 2.08/0.97  --sup_smt_interval                      50000
% 2.08/0.97  
% 2.08/0.97  ------ Superposition Simplification Setup
% 2.08/0.97  
% 2.08/0.97  --sup_indices_passive                   []
% 2.08/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.08/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/0.97  --sup_full_bw                           [BwDemod]
% 2.08/0.97  --sup_immed_triv                        [TrivRules]
% 2.08/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.08/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/0.97  --sup_immed_bw_main                     []
% 2.08/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.08/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/0.97  
% 2.08/0.97  ------ Combination Options
% 2.08/0.97  
% 2.08/0.97  --comb_res_mult                         3
% 2.08/0.97  --comb_sup_mult                         2
% 2.08/0.97  --comb_inst_mult                        10
% 2.08/0.97  
% 2.08/0.97  ------ Debug Options
% 2.08/0.97  
% 2.08/0.97  --dbg_backtrace                         false
% 2.08/0.97  --dbg_dump_prop_clauses                 false
% 2.08/0.97  --dbg_dump_prop_clauses_file            -
% 2.08/0.97  --dbg_out_stat                          false
% 2.08/0.97  
% 2.08/0.97  
% 2.08/0.97  
% 2.08/0.97  
% 2.08/0.97  ------ Proving...
% 2.08/0.97  
% 2.08/0.97  
% 2.08/0.97  % SZS status Theorem for theBenchmark.p
% 2.08/0.97  
% 2.08/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.08/0.97  
% 2.08/0.97  fof(f17,conjecture,(
% 2.08/0.97    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 2.08/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.97  
% 2.08/0.97  fof(f18,negated_conjecture,(
% 2.08/0.97    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 2.08/0.97    inference(negated_conjecture,[],[f17])).
% 2.08/0.97  
% 2.08/0.97  fof(f29,plain,(
% 2.08/0.97    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 2.08/0.97    inference(ennf_transformation,[],[f18])).
% 2.08/0.97  
% 2.08/0.97  fof(f30,plain,(
% 2.08/0.97    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 2.08/0.97    inference(flattening,[],[f29])).
% 2.08/0.97  
% 2.08/0.97  fof(f33,plain,(
% 2.08/0.97    ( ! [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) => (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,sK1),X0) & m1_subset_1(sK1,X0))) )),
% 2.08/0.97    introduced(choice_axiom,[])).
% 2.08/0.97  
% 2.08/0.97  fof(f32,plain,(
% 2.08/0.97    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 2.08/0.97    introduced(choice_axiom,[])).
% 2.08/0.97  
% 2.08/0.97  fof(f34,plain,(
% 2.08/0.97    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 2.08/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f33,f32])).
% 2.08/0.97  
% 2.08/0.97  fof(f53,plain,(
% 2.08/0.97    m1_subset_1(sK1,sK0)),
% 2.08/0.97    inference(cnf_transformation,[],[f34])).
% 2.08/0.97  
% 2.08/0.97  fof(f14,axiom,(
% 2.08/0.97    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.08/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.97  
% 2.08/0.97  fof(f23,plain,(
% 2.08/0.97    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.08/0.97    inference(ennf_transformation,[],[f14])).
% 2.08/0.97  
% 2.08/0.97  fof(f24,plain,(
% 2.08/0.97    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.08/0.97    inference(flattening,[],[f23])).
% 2.08/0.97  
% 2.08/0.97  fof(f49,plain,(
% 2.08/0.97    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.08/0.97    inference(cnf_transformation,[],[f24])).
% 2.08/0.97  
% 2.08/0.97  fof(f13,axiom,(
% 2.08/0.97    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.08/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.97  
% 2.08/0.97  fof(f31,plain,(
% 2.08/0.97    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.08/0.97    inference(nnf_transformation,[],[f13])).
% 2.08/0.97  
% 2.08/0.97  fof(f47,plain,(
% 2.08/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.08/0.97    inference(cnf_transformation,[],[f31])).
% 2.08/0.97  
% 2.08/0.97  fof(f6,axiom,(
% 2.08/0.97    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.08/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.97  
% 2.08/0.97  fof(f22,plain,(
% 2.08/0.97    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.08/0.97    inference(ennf_transformation,[],[f6])).
% 2.08/0.97  
% 2.08/0.97  fof(f40,plain,(
% 2.08/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.08/0.97    inference(cnf_transformation,[],[f22])).
% 2.08/0.97  
% 2.08/0.97  fof(f52,plain,(
% 2.08/0.97    ~v1_xboole_0(sK0)),
% 2.08/0.97    inference(cnf_transformation,[],[f34])).
% 2.08/0.97  
% 2.08/0.97  fof(f1,axiom,(
% 2.08/0.97    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.08/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.97  
% 2.08/0.97  fof(f35,plain,(
% 2.08/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.08/0.97    inference(cnf_transformation,[],[f1])).
% 2.08/0.97  
% 2.08/0.97  fof(f16,axiom,(
% 2.08/0.97    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 2.08/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.97  
% 2.08/0.97  fof(f27,plain,(
% 2.08/0.97    ! [X0] : (! [X1] : (r1_tarski(X0,X1) | v1_xboole_0(k3_xboole_0(X0,X1))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 2.08/0.97    inference(ennf_transformation,[],[f16])).
% 2.08/0.97  
% 2.08/0.97  fof(f28,plain,(
% 2.08/0.97    ! [X0] : (! [X1] : (r1_tarski(X0,X1) | v1_xboole_0(k3_xboole_0(X0,X1))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 2.08/0.97    inference(flattening,[],[f27])).
% 2.08/0.97  
% 2.08/0.97  fof(f51,plain,(
% 2.08/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | v1_xboole_0(k3_xboole_0(X0,X1)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 2.08/0.97    inference(cnf_transformation,[],[f28])).
% 2.08/0.97  
% 2.08/0.97  fof(f55,plain,(
% 2.08/0.97    v1_zfmisc_1(sK0)),
% 2.08/0.97    inference(cnf_transformation,[],[f34])).
% 2.08/0.97  
% 2.08/0.97  fof(f4,axiom,(
% 2.08/0.97    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.08/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.97  
% 2.08/0.97  fof(f21,plain,(
% 2.08/0.97    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.08/0.97    inference(ennf_transformation,[],[f4])).
% 2.08/0.97  
% 2.08/0.97  fof(f38,plain,(
% 2.08/0.97    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.08/0.97    inference(cnf_transformation,[],[f21])).
% 2.08/0.97  
% 2.08/0.97  fof(f15,axiom,(
% 2.08/0.97    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.08/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.97  
% 2.08/0.97  fof(f25,plain,(
% 2.08/0.97    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.08/0.97    inference(ennf_transformation,[],[f15])).
% 2.08/0.97  
% 2.08/0.97  fof(f26,plain,(
% 2.08/0.97    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.08/0.97    inference(flattening,[],[f25])).
% 2.08/0.97  
% 2.08/0.97  fof(f50,plain,(
% 2.08/0.97    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.08/0.97    inference(cnf_transformation,[],[f26])).
% 2.08/0.97  
% 2.08/0.97  fof(f8,axiom,(
% 2.08/0.97    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.08/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.97  
% 2.08/0.97  fof(f42,plain,(
% 2.08/0.97    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.08/0.97    inference(cnf_transformation,[],[f8])).
% 2.08/0.97  
% 2.08/0.97  fof(f9,axiom,(
% 2.08/0.97    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.08/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.97  
% 2.08/0.97  fof(f43,plain,(
% 2.08/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.08/0.97    inference(cnf_transformation,[],[f9])).
% 2.08/0.97  
% 2.08/0.97  fof(f57,plain,(
% 2.08/0.97    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 2.08/0.97    inference(definition_unfolding,[],[f42,f43])).
% 2.08/0.97  
% 2.08/0.97  fof(f60,plain,(
% 2.08/0.97    ( ! [X0,X1] : (k1_enumset1(X1,X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.08/0.97    inference(definition_unfolding,[],[f50,f57])).
% 2.08/0.97  
% 2.08/0.97  fof(f3,axiom,(
% 2.08/0.97    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.08/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.97  
% 2.08/0.97  fof(f20,plain,(
% 2.08/0.97    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.08/0.97    inference(rectify,[],[f3])).
% 2.08/0.97  
% 2.08/0.97  fof(f37,plain,(
% 2.08/0.97    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.08/0.97    inference(cnf_transformation,[],[f20])).
% 2.08/0.97  
% 2.08/0.97  fof(f10,axiom,(
% 2.08/0.97    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 2.08/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.97  
% 2.08/0.97  fof(f44,plain,(
% 2.08/0.97    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 2.08/0.97    inference(cnf_transformation,[],[f10])).
% 2.08/0.97  
% 2.08/0.97  fof(f7,axiom,(
% 2.08/0.97    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.08/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.97  
% 2.08/0.97  fof(f41,plain,(
% 2.08/0.97    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.08/0.97    inference(cnf_transformation,[],[f7])).
% 2.08/0.97  
% 2.08/0.97  fof(f5,axiom,(
% 2.08/0.97    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.08/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.97  
% 2.08/0.97  fof(f39,plain,(
% 2.08/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.08/0.97    inference(cnf_transformation,[],[f5])).
% 2.08/0.97  
% 2.08/0.97  fof(f56,plain,(
% 2.08/0.97    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 2.08/0.97    inference(definition_unfolding,[],[f41,f39])).
% 2.08/0.97  
% 2.08/0.97  fof(f59,plain,(
% 2.08/0.97    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,k1_enumset1(X0,X0,X0))))) )),
% 2.08/0.97    inference(definition_unfolding,[],[f44,f56,f57])).
% 2.08/0.97  
% 2.08/0.97  fof(f2,axiom,(
% 2.08/0.97    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.08/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.97  
% 2.08/0.97  fof(f19,plain,(
% 2.08/0.97    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.08/0.97    inference(rectify,[],[f2])).
% 2.08/0.97  
% 2.08/0.97  fof(f36,plain,(
% 2.08/0.97    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.08/0.97    inference(cnf_transformation,[],[f19])).
% 2.08/0.97  
% 2.08/0.97  fof(f58,plain,(
% 2.08/0.97    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0) )),
% 2.08/0.97    inference(definition_unfolding,[],[f36,f56])).
% 2.08/0.97  
% 2.08/0.97  fof(f12,axiom,(
% 2.08/0.97    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 2.08/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.97  
% 2.08/0.97  fof(f46,plain,(
% 2.08/0.97    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 2.08/0.97    inference(cnf_transformation,[],[f12])).
% 2.08/0.97  
% 2.08/0.97  fof(f54,plain,(
% 2.08/0.97    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 2.08/0.97    inference(cnf_transformation,[],[f34])).
% 2.08/0.97  
% 2.08/0.97  fof(f11,axiom,(
% 2.08/0.97    ! [X0] : k2_subset_1(X0) = X0),
% 2.08/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.97  
% 2.08/0.97  fof(f45,plain,(
% 2.08/0.97    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.08/0.97    inference(cnf_transformation,[],[f11])).
% 2.08/0.97  
% 2.08/0.97  cnf(c_15,negated_conjecture,
% 2.08/0.97      ( m1_subset_1(sK1,sK0) ),
% 2.08/0.97      inference(cnf_transformation,[],[f53]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_663,plain,
% 2.08/0.97      ( m1_subset_1(sK1,sK0) = iProver_top ),
% 2.08/0.97      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_10,plain,
% 2.08/0.97      ( ~ m1_subset_1(X0,X1)
% 2.08/0.97      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 2.08/0.97      | v1_xboole_0(X1) ),
% 2.08/0.97      inference(cnf_transformation,[],[f49]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_665,plain,
% 2.08/0.97      ( m1_subset_1(X0,X1) != iProver_top
% 2.08/0.97      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
% 2.08/0.97      | v1_xboole_0(X1) = iProver_top ),
% 2.08/0.97      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_9,plain,
% 2.08/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.08/0.97      inference(cnf_transformation,[],[f47]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_100,plain,
% 2.08/0.97      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.08/0.97      inference(prop_impl,[status(thm)],[c_9]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_101,plain,
% 2.08/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.08/0.97      inference(renaming,[status(thm)],[c_100]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_4,plain,
% 2.08/0.97      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 2.08/0.97      inference(cnf_transformation,[],[f40]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_204,plain,
% 2.08/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | k3_xboole_0(X0,X1) = X0 ),
% 2.08/0.97      inference(resolution,[status(thm)],[c_101,c_4]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_661,plain,
% 2.08/0.97      ( k3_xboole_0(X0,X1) = X0
% 2.08/0.97      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 2.08/0.97      inference(predicate_to_equality,[status(thm)],[c_204]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_1820,plain,
% 2.08/0.97      ( k3_xboole_0(k6_domain_1(X0,X1),X0) = k6_domain_1(X0,X1)
% 2.08/0.97      | m1_subset_1(X1,X0) != iProver_top
% 2.08/0.97      | v1_xboole_0(X0) = iProver_top ),
% 2.08/0.97      inference(superposition,[status(thm)],[c_665,c_661]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_3373,plain,
% 2.08/0.97      ( k3_xboole_0(k6_domain_1(sK0,sK1),sK0) = k6_domain_1(sK0,sK1)
% 2.08/0.97      | v1_xboole_0(sK0) = iProver_top ),
% 2.08/0.97      inference(superposition,[status(thm)],[c_663,c_1820]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_16,negated_conjecture,
% 2.08/0.97      ( ~ v1_xboole_0(sK0) ),
% 2.08/0.97      inference(cnf_transformation,[],[f52]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_742,plain,
% 2.08/0.97      ( m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
% 2.08/0.97      | ~ m1_subset_1(sK1,sK0)
% 2.08/0.97      | v1_xboole_0(sK0) ),
% 2.08/0.97      inference(instantiation,[status(thm)],[c_10]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_1316,plain,
% 2.08/0.97      ( ~ m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(X0))
% 2.08/0.97      | k3_xboole_0(k6_domain_1(sK0,sK1),X0) = k6_domain_1(sK0,sK1) ),
% 2.08/0.97      inference(instantiation,[status(thm)],[c_204]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_1322,plain,
% 2.08/0.97      ( ~ m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
% 2.08/0.97      | k3_xboole_0(k6_domain_1(sK0,sK1),sK0) = k6_domain_1(sK0,sK1) ),
% 2.08/0.97      inference(instantiation,[status(thm)],[c_1316]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_3471,plain,
% 2.08/0.97      ( k3_xboole_0(k6_domain_1(sK0,sK1),sK0) = k6_domain_1(sK0,sK1) ),
% 2.08/0.97      inference(global_propositional_subsumption,
% 2.08/0.97                [status(thm)],
% 2.08/0.97                [c_3373,c_16,c_15,c_742,c_1322]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_0,plain,
% 2.08/0.97      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 2.08/0.97      inference(cnf_transformation,[],[f35]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_12,plain,
% 2.08/0.97      ( r1_tarski(X0,X1)
% 2.08/0.97      | ~ v1_zfmisc_1(X0)
% 2.08/0.97      | v1_xboole_0(X0)
% 2.08/0.97      | v1_xboole_0(k3_xboole_0(X0,X1)) ),
% 2.08/0.97      inference(cnf_transformation,[],[f51]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_13,negated_conjecture,
% 2.08/0.97      ( v1_zfmisc_1(sK0) ),
% 2.08/0.97      inference(cnf_transformation,[],[f55]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_182,plain,
% 2.08/0.97      ( r1_tarski(X0,X1)
% 2.08/0.97      | v1_xboole_0(X0)
% 2.08/0.97      | v1_xboole_0(k3_xboole_0(X0,X1))
% 2.08/0.97      | sK0 != X0 ),
% 2.08/0.97      inference(resolution_lifted,[status(thm)],[c_12,c_13]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_183,plain,
% 2.08/0.97      ( r1_tarski(sK0,X0)
% 2.08/0.97      | v1_xboole_0(k3_xboole_0(sK0,X0))
% 2.08/0.97      | v1_xboole_0(sK0) ),
% 2.08/0.97      inference(unflattening,[status(thm)],[c_182]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_187,plain,
% 2.08/0.97      ( v1_xboole_0(k3_xboole_0(sK0,X0)) | r1_tarski(sK0,X0) ),
% 2.08/0.97      inference(global_propositional_subsumption,
% 2.08/0.97                [status(thm)],
% 2.08/0.97                [c_183,c_16]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_188,plain,
% 2.08/0.97      ( r1_tarski(sK0,X0) | v1_xboole_0(k3_xboole_0(sK0,X0)) ),
% 2.08/0.97      inference(renaming,[status(thm)],[c_187]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_225,plain,
% 2.08/0.97      ( v1_xboole_0(k3_xboole_0(sK0,X0))
% 2.08/0.97      | X0 != X1
% 2.08/0.97      | k3_xboole_0(X2,X1) = X2
% 2.08/0.97      | sK0 != X2 ),
% 2.08/0.97      inference(resolution_lifted,[status(thm)],[c_4,c_188]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_226,plain,
% 2.08/0.97      ( v1_xboole_0(k3_xboole_0(sK0,X0)) | k3_xboole_0(sK0,X0) = sK0 ),
% 2.08/0.97      inference(unflattening,[status(thm)],[c_225]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_659,plain,
% 2.08/0.97      ( k3_xboole_0(sK0,X0) = sK0
% 2.08/0.97      | v1_xboole_0(k3_xboole_0(sK0,X0)) = iProver_top ),
% 2.08/0.97      inference(predicate_to_equality,[status(thm)],[c_226]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_959,plain,
% 2.08/0.97      ( k3_xboole_0(sK0,X0) = sK0
% 2.08/0.97      | v1_xboole_0(k3_xboole_0(X0,sK0)) = iProver_top ),
% 2.08/0.97      inference(superposition,[status(thm)],[c_0,c_659]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_3,plain,
% 2.08/0.97      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.08/0.97      inference(cnf_transformation,[],[f38]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_666,plain,
% 2.08/0.97      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.08/0.97      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_1140,plain,
% 2.08/0.97      ( k3_xboole_0(X0,sK0) = k1_xboole_0 | k3_xboole_0(sK0,X0) = sK0 ),
% 2.08/0.97      inference(superposition,[status(thm)],[c_959,c_666]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_1248,plain,
% 2.08/0.97      ( k3_xboole_0(X0,sK0) = sK0 | k3_xboole_0(X0,sK0) = k1_xboole_0 ),
% 2.08/0.97      inference(superposition,[status(thm)],[c_1140,c_0]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_3492,plain,
% 2.08/0.97      ( k6_domain_1(sK0,sK1) = sK0
% 2.08/0.97      | k3_xboole_0(k6_domain_1(sK0,sK1),sK0) = k1_xboole_0 ),
% 2.08/0.97      inference(superposition,[status(thm)],[c_3471,c_1248]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_3511,plain,
% 2.08/0.97      ( k6_domain_1(sK0,sK1) = sK0 | k6_domain_1(sK0,sK1) = k1_xboole_0 ),
% 2.08/0.97      inference(demodulation,[status(thm)],[c_3492,c_3471]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_11,plain,
% 2.08/0.97      ( ~ m1_subset_1(X0,X1)
% 2.08/0.97      | v1_xboole_0(X1)
% 2.08/0.97      | k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0) ),
% 2.08/0.97      inference(cnf_transformation,[],[f60]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_664,plain,
% 2.08/0.97      ( k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0)
% 2.08/0.97      | m1_subset_1(X0,X1) != iProver_top
% 2.08/0.97      | v1_xboole_0(X1) = iProver_top ),
% 2.08/0.97      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_1718,plain,
% 2.08/0.97      ( k1_enumset1(sK1,sK1,sK1) = k6_domain_1(sK0,sK1)
% 2.08/0.97      | v1_xboole_0(sK0) = iProver_top ),
% 2.08/0.97      inference(superposition,[status(thm)],[c_663,c_664]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_750,plain,
% 2.08/0.97      ( ~ m1_subset_1(sK1,sK0)
% 2.08/0.97      | v1_xboole_0(sK0)
% 2.08/0.97      | k1_enumset1(sK1,sK1,sK1) = k6_domain_1(sK0,sK1) ),
% 2.08/0.97      inference(instantiation,[status(thm)],[c_11]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_1843,plain,
% 2.08/0.97      ( k1_enumset1(sK1,sK1,sK1) = k6_domain_1(sK0,sK1) ),
% 2.08/0.97      inference(global_propositional_subsumption,
% 2.08/0.97                [status(thm)],
% 2.08/0.97                [c_1718,c_16,c_15,c_750]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_2,plain,
% 2.08/0.97      ( k3_xboole_0(X0,X0) = X0 ),
% 2.08/0.97      inference(cnf_transformation,[],[f37]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_5,plain,
% 2.08/0.97      ( k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,k1_enumset1(X0,X0,X0)))) != k1_xboole_0 ),
% 2.08/0.97      inference(cnf_transformation,[],[f59]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_1027,plain,
% 2.08/0.97      ( k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0))) != k1_xboole_0 ),
% 2.08/0.97      inference(superposition,[status(thm)],[c_2,c_5]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_1,plain,
% 2.08/0.97      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
% 2.08/0.97      inference(cnf_transformation,[],[f58]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_684,plain,
% 2.08/0.97      ( k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
% 2.08/0.97      inference(light_normalisation,[status(thm)],[c_1,c_2]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_1768,plain,
% 2.08/0.97      ( k1_enumset1(X0,X0,X0) != k1_xboole_0 ),
% 2.08/0.97      inference(demodulation,[status(thm)],[c_1027,c_684]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_1846,plain,
% 2.08/0.97      ( k6_domain_1(sK0,sK1) != k1_xboole_0 ),
% 2.08/0.97      inference(superposition,[status(thm)],[c_1843,c_1768]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_7,plain,
% 2.08/0.97      ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
% 2.08/0.97      inference(cnf_transformation,[],[f46]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_14,negated_conjecture,
% 2.08/0.97      ( v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
% 2.08/0.97      inference(cnf_transformation,[],[f54]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_176,plain,
% 2.08/0.97      ( k6_domain_1(sK0,sK1) != k2_subset_1(X0) | sK0 != X0 ),
% 2.08/0.97      inference(resolution_lifted,[status(thm)],[c_7,c_14]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_177,plain,
% 2.08/0.97      ( k6_domain_1(sK0,sK1) != k2_subset_1(sK0) ),
% 2.08/0.97      inference(unflattening,[status(thm)],[c_176]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_6,plain,
% 2.08/0.97      ( k2_subset_1(X0) = X0 ),
% 2.08/0.97      inference(cnf_transformation,[],[f45]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(c_675,plain,
% 2.08/0.97      ( k6_domain_1(sK0,sK1) != sK0 ),
% 2.08/0.97      inference(demodulation,[status(thm)],[c_177,c_6]) ).
% 2.08/0.97  
% 2.08/0.97  cnf(contradiction,plain,
% 2.08/0.97      ( $false ),
% 2.08/0.97      inference(minisat,[status(thm)],[c_3511,c_1846,c_675]) ).
% 2.08/0.97  
% 2.08/0.97  
% 2.08/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.08/0.97  
% 2.08/0.97  ------                               Statistics
% 2.08/0.97  
% 2.08/0.97  ------ General
% 2.08/0.97  
% 2.08/0.97  abstr_ref_over_cycles:                  0
% 2.08/0.97  abstr_ref_under_cycles:                 0
% 2.08/0.97  gc_basic_clause_elim:                   0
% 2.08/0.97  forced_gc_time:                         0
% 2.08/0.97  parsing_time:                           0.01
% 2.08/0.97  unif_index_cands_time:                  0.
% 2.08/0.97  unif_index_add_time:                    0.
% 2.08/0.97  orderings_time:                         0.
% 2.08/0.97  out_proof_time:                         0.007
% 2.08/0.97  total_time:                             0.135
% 2.08/0.97  num_of_symbols:                         45
% 2.08/0.97  num_of_terms:                           3034
% 2.08/0.97  
% 2.08/0.97  ------ Preprocessing
% 2.08/0.97  
% 2.08/0.97  num_of_splits:                          0
% 2.08/0.97  num_of_split_atoms:                     0
% 2.08/0.97  num_of_reused_defs:                     0
% 2.08/0.97  num_eq_ax_congr_red:                    16
% 2.08/0.97  num_of_sem_filtered_clauses:            1
% 2.08/0.97  num_of_subtypes:                        0
% 2.08/0.97  monotx_restored_types:                  0
% 2.08/0.97  sat_num_of_epr_types:                   0
% 2.08/0.97  sat_num_of_non_cyclic_types:            0
% 2.08/0.97  sat_guarded_non_collapsed_types:        0
% 2.08/0.97  num_pure_diseq_elim:                    0
% 2.08/0.97  simp_replaced_by:                       0
% 2.08/0.97  res_preprocessed:                       76
% 2.08/0.97  prep_upred:                             0
% 2.08/0.97  prep_unflattend:                        18
% 2.08/0.97  smt_new_axioms:                         0
% 2.08/0.97  pred_elim_cands:                        2
% 2.08/0.97  pred_elim:                              3
% 2.08/0.97  pred_elim_cl:                           3
% 2.08/0.97  pred_elim_cycles:                       5
% 2.08/0.97  merged_defs:                            2
% 2.08/0.97  merged_defs_ncl:                        0
% 2.08/0.97  bin_hyper_res:                          2
% 2.08/0.97  prep_cycles:                            4
% 2.08/0.97  pred_elim_time:                         0.003
% 2.08/0.97  splitting_time:                         0.
% 2.08/0.97  sem_filter_time:                        0.
% 2.08/0.97  monotx_time:                            0.
% 2.08/0.97  subtype_inf_time:                       0.
% 2.08/0.97  
% 2.08/0.97  ------ Problem properties
% 2.08/0.97  
% 2.08/0.97  clauses:                                14
% 2.08/0.97  conjectures:                            2
% 2.08/0.97  epr:                                    3
% 2.08/0.97  horn:                                   10
% 2.08/0.97  ground:                                 3
% 2.08/0.97  unary:                                  8
% 2.08/0.97  binary:                                 4
% 2.08/0.97  lits:                                   22
% 2.08/0.97  lits_eq:                                10
% 2.08/0.97  fd_pure:                                0
% 2.08/0.97  fd_pseudo:                              0
% 2.08/0.97  fd_cond:                                1
% 2.08/0.97  fd_pseudo_cond:                         0
% 2.08/0.97  ac_symbols:                             0
% 2.08/0.97  
% 2.08/0.97  ------ Propositional Solver
% 2.08/0.97  
% 2.08/0.97  prop_solver_calls:                      27
% 2.08/0.97  prop_fast_solver_calls:                 424
% 2.08/0.97  smt_solver_calls:                       0
% 2.08/0.97  smt_fast_solver_calls:                  0
% 2.08/0.97  prop_num_of_clauses:                    1274
% 2.08/0.97  prop_preprocess_simplified:             4109
% 2.08/0.97  prop_fo_subsumed:                       5
% 2.08/0.97  prop_solver_time:                       0.
% 2.08/0.97  smt_solver_time:                        0.
% 2.08/0.97  smt_fast_solver_time:                   0.
% 2.08/0.97  prop_fast_solver_time:                  0.
% 2.08/0.97  prop_unsat_core_time:                   0.
% 2.08/0.97  
% 2.08/0.97  ------ QBF
% 2.08/0.97  
% 2.08/0.97  qbf_q_res:                              0
% 2.08/0.97  qbf_num_tautologies:                    0
% 2.08/0.97  qbf_prep_cycles:                        0
% 2.08/0.97  
% 2.08/0.97  ------ BMC1
% 2.08/0.97  
% 2.08/0.97  bmc1_current_bound:                     -1
% 2.08/0.97  bmc1_last_solved_bound:                 -1
% 2.08/0.97  bmc1_unsat_core_size:                   -1
% 2.08/0.97  bmc1_unsat_core_parents_size:           -1
% 2.08/0.97  bmc1_merge_next_fun:                    0
% 2.08/0.97  bmc1_unsat_core_clauses_time:           0.
% 2.08/0.97  
% 2.08/0.97  ------ Instantiation
% 2.08/0.97  
% 2.08/0.97  inst_num_of_clauses:                    444
% 2.08/0.97  inst_num_in_passive:                    176
% 2.08/0.97  inst_num_in_active:                     213
% 2.08/0.97  inst_num_in_unprocessed:                55
% 2.08/0.97  inst_num_of_loops:                      240
% 2.08/0.97  inst_num_of_learning_restarts:          0
% 2.08/0.97  inst_num_moves_active_passive:          25
% 2.08/0.97  inst_lit_activity:                      0
% 2.08/0.97  inst_lit_activity_moves:                0
% 2.08/0.97  inst_num_tautologies:                   0
% 2.08/0.97  inst_num_prop_implied:                  0
% 2.08/0.97  inst_num_existing_simplified:           0
% 2.08/0.97  inst_num_eq_res_simplified:             0
% 2.08/0.97  inst_num_child_elim:                    0
% 2.08/0.97  inst_num_of_dismatching_blockings:      80
% 2.08/0.97  inst_num_of_non_proper_insts:           348
% 2.08/0.97  inst_num_of_duplicates:                 0
% 2.08/0.97  inst_inst_num_from_inst_to_res:         0
% 2.08/0.97  inst_dismatching_checking_time:         0.
% 2.08/0.97  
% 2.08/0.97  ------ Resolution
% 2.08/0.97  
% 2.08/0.97  res_num_of_clauses:                     0
% 2.08/0.97  res_num_in_passive:                     0
% 2.08/0.97  res_num_in_active:                      0
% 2.08/0.97  res_num_of_loops:                       80
% 2.08/0.97  res_forward_subset_subsumed:            28
% 2.08/0.97  res_backward_subset_subsumed:           0
% 2.08/0.97  res_forward_subsumed:                   0
% 2.08/0.97  res_backward_subsumed:                  0
% 2.08/0.97  res_forward_subsumption_resolution:     0
% 2.08/0.97  res_backward_subsumption_resolution:    0
% 2.08/0.97  res_clause_to_clause_subsumption:       339
% 2.08/0.97  res_orphan_elimination:                 0
% 2.08/0.97  res_tautology_del:                      30
% 2.08/0.97  res_num_eq_res_simplified:              0
% 2.08/0.97  res_num_sel_changes:                    0
% 2.08/0.97  res_moves_from_active_to_pass:          0
% 2.08/0.97  
% 2.08/0.97  ------ Superposition
% 2.08/0.97  
% 2.08/0.97  sup_time_total:                         0.
% 2.08/0.97  sup_time_generating:                    0.
% 2.08/0.97  sup_time_sim_full:                      0.
% 2.08/0.97  sup_time_sim_immed:                     0.
% 2.08/0.97  
% 2.08/0.97  sup_num_of_clauses:                     79
% 2.08/0.97  sup_num_in_active:                      45
% 2.08/0.97  sup_num_in_passive:                     34
% 2.08/0.97  sup_num_of_loops:                       46
% 2.08/0.97  sup_fw_superposition:                   96
% 2.08/0.97  sup_bw_superposition:                   88
% 2.08/0.97  sup_immediate_simplified:               28
% 2.08/0.97  sup_given_eliminated:                   0
% 2.08/0.97  comparisons_done:                       0
% 2.08/0.97  comparisons_avoided:                    24
% 2.08/0.97  
% 2.08/0.97  ------ Simplifications
% 2.08/0.97  
% 2.08/0.97  
% 2.08/0.97  sim_fw_subset_subsumed:                 8
% 2.08/0.97  sim_bw_subset_subsumed:                 1
% 2.08/0.97  sim_fw_subsumed:                        6
% 2.08/0.97  sim_bw_subsumed:                        0
% 2.08/0.97  sim_fw_subsumption_res:                 0
% 2.08/0.97  sim_bw_subsumption_res:                 0
% 2.08/0.97  sim_tautology_del:                      1
% 2.08/0.97  sim_eq_tautology_del:                   6
% 2.08/0.97  sim_eq_res_simp:                        0
% 2.08/0.97  sim_fw_demodulated:                     11
% 2.08/0.97  sim_bw_demodulated:                     3
% 2.08/0.97  sim_light_normalised:                   5
% 2.08/0.97  sim_joinable_taut:                      0
% 2.08/0.97  sim_joinable_simp:                      0
% 2.08/0.97  sim_ac_normalised:                      0
% 2.08/0.97  sim_smt_subsumption:                    0
% 2.08/0.97  
%------------------------------------------------------------------------------
