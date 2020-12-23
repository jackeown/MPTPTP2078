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
% DateTime   : Thu Dec  3 11:55:48 EST 2020

% Result     : Theorem 7.78s
% Output     : CNFRefutation 7.78s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 367 expanded)
%              Number of clauses        :   79 ( 142 expanded)
%              Number of leaves         :   15 (  70 expanded)
%              Depth                    :   22
%              Number of atoms          :  309 ( 925 expanded)
%              Number of equality atoms :  103 ( 149 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
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
    inference(ennf_transformation,[],[f1])).

fof(f33,plain,(
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

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
   => ( ~ m1_subset_1(k6_relset_1(sK4,sK2,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ~ m1_subset_1(k6_relset_1(sK4,sK2,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f32,f42])).

fof(f64,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f65,plain,(
    ~ m1_subset_1(k6_relset_1(sK4,sK2,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_13,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_787,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_14,plain,
    ( r1_tarski(k8_relat_1(X0,X1),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_786,plain,
    ( r1_tarski(k8_relat_1(X0,X1),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_799,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_798,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3770,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_799,c_798])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_779,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_12,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_788,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3572,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(sK4,sK2)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_779,c_788])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_791,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4260,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK4,sK2)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK4,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3572,c_791])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1034,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK4,sK2)) ),
    inference(resolution,[status(thm)],[c_11,c_21])).

cnf(c_2457,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK4,sK2))
    | ~ r2_hidden(X0,sK5) ),
    inference(resolution,[status(thm)],[c_2,c_1034])).

cnf(c_2458,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK4,sK2)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2457])).

cnf(c_4346,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X0,k2_zfmisc_1(sK4,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4260,c_2458])).

cnf(c_4347,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK4,sK2)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_4346])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_800,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4352,plain,
    ( r2_hidden(sK0(X0,k2_zfmisc_1(sK4,sK2)),sK5) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(sK4,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4347,c_800])).

cnf(c_9311,plain,
    ( r1_tarski(X0,k2_zfmisc_1(sK4,sK2)) = iProver_top
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3770,c_4352])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_790,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_783,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2203,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_790,c_783])).

cnf(c_10603,plain,
    ( k1_relset_1(sK4,sK2,X0) = k1_relat_1(X0)
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_9311,c_2203])).

cnf(c_15160,plain,
    ( k1_relset_1(sK4,sK2,k8_relat_1(X0,sK5)) = k1_relat_1(k8_relat_1(X0,sK5))
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_786,c_10603])).

cnf(c_22,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_967,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_968,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_967])).

cnf(c_16874,plain,
    ( k1_relset_1(sK4,sK2,k8_relat_1(X0,sK5)) = k1_relat_1(k8_relat_1(X0,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15160,c_22,c_968])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_784,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_16880,plain,
    ( m1_subset_1(k8_relat_1(X0,sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | m1_subset_1(k1_relat_1(k8_relat_1(X0,sK5)),k1_zfmisc_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_16874,c_784])).

cnf(c_1035,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK4,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1034])).

cnf(c_1099,plain,
    ( r1_tarski(k8_relat_1(X0,sK5),sK5)
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1105,plain,
    ( r1_tarski(k8_relat_1(X0,sK5),sK5) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1099])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1139,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | r1_tarski(X0,k2_zfmisc_1(X2,X3)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3391,plain,
    ( r1_tarski(X0,k2_zfmisc_1(sK4,sK2))
    | ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,k2_zfmisc_1(sK4,sK2)) ),
    inference(instantiation,[status(thm)],[c_1139])).

cnf(c_7385,plain,
    ( r1_tarski(k8_relat_1(X0,sK5),k2_zfmisc_1(sK4,sK2))
    | ~ r1_tarski(k8_relat_1(X0,sK5),sK5)
    | ~ r1_tarski(sK5,k2_zfmisc_1(sK4,sK2)) ),
    inference(instantiation,[status(thm)],[c_3391])).

cnf(c_7386,plain,
    ( r1_tarski(k8_relat_1(X0,sK5),k2_zfmisc_1(sK4,sK2)) = iProver_top
    | r1_tarski(k8_relat_1(X0,sK5),sK5) != iProver_top
    | r1_tarski(sK5,k2_zfmisc_1(sK4,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7385])).

cnf(c_962,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_18282,plain,
    ( m1_subset_1(k8_relat_1(X0,sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | ~ r1_tarski(k8_relat_1(X0,sK5),k2_zfmisc_1(sK4,sK2)) ),
    inference(instantiation,[status(thm)],[c_962])).

cnf(c_18283,plain,
    ( m1_subset_1(k8_relat_1(X0,sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top
    | r1_tarski(k8_relat_1(X0,sK5),k2_zfmisc_1(sK4,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18282])).

cnf(c_19331,plain,
    ( m1_subset_1(k1_relat_1(k8_relat_1(X0,sK5)),k1_zfmisc_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16880,c_22,c_968,c_1035,c_1105,c_7386,c_18283])).

cnf(c_789,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_19339,plain,
    ( r1_tarski(k1_relat_1(k8_relat_1(X0,sK5)),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_19331,c_789])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k6_relset_1(X1,X2,X3,X0) = k8_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_782,plain,
    ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2178,plain,
    ( k6_relset_1(sK4,sK2,X0,sK5) = k8_relat_1(X0,sK5) ),
    inference(superposition,[status(thm)],[c_779,c_782])).

cnf(c_19,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_781,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_20,negated_conjecture,
    ( ~ m1_subset_1(k6_relset_1(sK4,sK2,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_780,plain,
    ( m1_subset_1(k6_relset_1(sK4,sK2,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1282,plain,
    ( r1_tarski(k1_relat_1(k6_relset_1(sK4,sK2,sK3,sK5)),sK4) != iProver_top
    | r1_tarski(k2_relat_1(k6_relset_1(sK4,sK2,sK3,sK5)),sK3) != iProver_top
    | v1_relat_1(k6_relset_1(sK4,sK2,sK3,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_781,c_780])).

cnf(c_2802,plain,
    ( r1_tarski(k1_relat_1(k8_relat_1(sK3,sK5)),sK4) != iProver_top
    | r1_tarski(k2_relat_1(k8_relat_1(sK3,sK5)),sK3) != iProver_top
    | v1_relat_1(k8_relat_1(sK3,sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2178,c_1282])).

cnf(c_20999,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(sK3,sK5)),sK3) != iProver_top
    | v1_relat_1(k8_relat_1(sK3,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19339,c_2802])).

cnf(c_785,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1526,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_790,c_785])).

cnf(c_10599,plain,
    ( r1_tarski(X0,sK5) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9311,c_1526])).

cnf(c_15085,plain,
    ( v1_relat_1(k8_relat_1(X0,sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_786,c_10599])).

cnf(c_2575,plain,
    ( r1_tarski(X0,k2_zfmisc_1(sK4,sK2))
    | ~ r1_tarski(X0,sK5) ),
    inference(resolution,[status(thm)],[c_3,c_1034])).

cnf(c_1547,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_15,c_10])).

cnf(c_2838,plain,
    ( ~ r1_tarski(X0,sK5)
    | v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_2575,c_1547])).

cnf(c_3064,plain,
    ( v1_relat_1(k8_relat_1(X0,sK5))
    | ~ v1_relat_1(sK5) ),
    inference(resolution,[status(thm)],[c_2838,c_14])).

cnf(c_3065,plain,
    ( v1_relat_1(k8_relat_1(X0,sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3064])).

cnf(c_16726,plain,
    ( v1_relat_1(k8_relat_1(X0,sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15085,c_22,c_968,c_3065])).

cnf(c_21900,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(sK3,sK5)),sK3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_20999,c_16726])).

cnf(c_21902,plain,
    ( v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_787,c_21900])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21902,c_968,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:28:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.78/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.78/1.48  
% 7.78/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.78/1.48  
% 7.78/1.48  ------  iProver source info
% 7.78/1.48  
% 7.78/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.78/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.78/1.48  git: non_committed_changes: false
% 7.78/1.48  git: last_make_outside_of_git: false
% 7.78/1.48  
% 7.78/1.48  ------ 
% 7.78/1.48  ------ Parsing...
% 7.78/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.78/1.48  
% 7.78/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.78/1.48  
% 7.78/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.78/1.48  
% 7.78/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.78/1.48  ------ Proving...
% 7.78/1.48  ------ Problem Properties 
% 7.78/1.48  
% 7.78/1.48  
% 7.78/1.48  clauses                                 22
% 7.78/1.48  conjectures                             2
% 7.78/1.48  EPR                                     3
% 7.78/1.48  Horn                                    19
% 7.78/1.48  unary                                   3
% 7.78/1.48  binary                                  12
% 7.78/1.48  lits                                    49
% 7.78/1.48  lits eq                                 4
% 7.78/1.48  fd_pure                                 0
% 7.78/1.48  fd_pseudo                               0
% 7.78/1.48  fd_cond                                 0
% 7.78/1.48  fd_pseudo_cond                          2
% 7.78/1.48  AC symbols                              0
% 7.78/1.48  
% 7.78/1.48  ------ Input Options Time Limit: Unbounded
% 7.78/1.48  
% 7.78/1.48  
% 7.78/1.48  ------ 
% 7.78/1.48  Current options:
% 7.78/1.48  ------ 
% 7.78/1.48  
% 7.78/1.48  
% 7.78/1.48  
% 7.78/1.48  
% 7.78/1.48  ------ Proving...
% 7.78/1.48  
% 7.78/1.48  
% 7.78/1.48  % SZS status Theorem for theBenchmark.p
% 7.78/1.48  
% 7.78/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.78/1.48  
% 7.78/1.48  fof(f8,axiom,(
% 7.78/1.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0))),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f24,plain,(
% 7.78/1.48    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 7.78/1.48    inference(ennf_transformation,[],[f8])).
% 7.78/1.48  
% 7.78/1.48  fof(f57,plain,(
% 7.78/1.48    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f24])).
% 7.78/1.48  
% 7.78/1.48  fof(f9,axiom,(
% 7.78/1.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f25,plain,(
% 7.78/1.48    ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 7.78/1.48    inference(ennf_transformation,[],[f9])).
% 7.78/1.48  
% 7.78/1.48  fof(f58,plain,(
% 7.78/1.48    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f25])).
% 7.78/1.48  
% 7.78/1.48  fof(f1,axiom,(
% 7.78/1.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f17,plain,(
% 7.78/1.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.78/1.48    inference(ennf_transformation,[],[f1])).
% 7.78/1.48  
% 7.78/1.48  fof(f33,plain,(
% 7.78/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.78/1.48    inference(nnf_transformation,[],[f17])).
% 7.78/1.48  
% 7.78/1.48  fof(f34,plain,(
% 7.78/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.78/1.48    inference(rectify,[],[f33])).
% 7.78/1.48  
% 7.78/1.48  fof(f35,plain,(
% 7.78/1.48    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.78/1.48    introduced(choice_axiom,[])).
% 7.78/1.48  
% 7.78/1.48  fof(f36,plain,(
% 7.78/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.78/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 7.78/1.48  
% 7.78/1.48  fof(f45,plain,(
% 7.78/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f36])).
% 7.78/1.48  
% 7.78/1.48  fof(f44,plain,(
% 7.78/1.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f36])).
% 7.78/1.48  
% 7.78/1.48  fof(f15,conjecture,(
% 7.78/1.48    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f16,negated_conjecture,(
% 7.78/1.48    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))),
% 7.78/1.48    inference(negated_conjecture,[],[f15])).
% 7.78/1.48  
% 7.78/1.48  fof(f32,plain,(
% 7.78/1.48    ? [X0,X1,X2,X3] : (~m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 7.78/1.48    inference(ennf_transformation,[],[f16])).
% 7.78/1.48  
% 7.78/1.48  fof(f42,plain,(
% 7.78/1.48    ? [X0,X1,X2,X3] : (~m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) => (~m1_subset_1(k6_relset_1(sK4,sK2,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))))),
% 7.78/1.48    introduced(choice_axiom,[])).
% 7.78/1.48  
% 7.78/1.48  fof(f43,plain,(
% 7.78/1.48    ~m1_subset_1(k6_relset_1(sK4,sK2,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))),
% 7.78/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f32,f42])).
% 7.78/1.48  
% 7.78/1.48  fof(f64,plain,(
% 7.78/1.48    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))),
% 7.78/1.48    inference(cnf_transformation,[],[f43])).
% 7.78/1.48  
% 7.78/1.48  fof(f7,axiom,(
% 7.78/1.48    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f22,plain,(
% 7.78/1.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 7.78/1.48    inference(ennf_transformation,[],[f7])).
% 7.78/1.48  
% 7.78/1.48  fof(f23,plain,(
% 7.78/1.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.78/1.48    inference(flattening,[],[f22])).
% 7.78/1.48  
% 7.78/1.48  fof(f56,plain,(
% 7.78/1.48    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f23])).
% 7.78/1.48  
% 7.78/1.48  fof(f5,axiom,(
% 7.78/1.48    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f20,plain,(
% 7.78/1.48    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 7.78/1.48    inference(ennf_transformation,[],[f5])).
% 7.78/1.48  
% 7.78/1.48  fof(f21,plain,(
% 7.78/1.48    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 7.78/1.48    inference(flattening,[],[f20])).
% 7.78/1.48  
% 7.78/1.48  fof(f53,plain,(
% 7.78/1.48    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f21])).
% 7.78/1.48  
% 7.78/1.48  fof(f6,axiom,(
% 7.78/1.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f41,plain,(
% 7.78/1.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.78/1.48    inference(nnf_transformation,[],[f6])).
% 7.78/1.48  
% 7.78/1.48  fof(f54,plain,(
% 7.78/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.78/1.48    inference(cnf_transformation,[],[f41])).
% 7.78/1.48  
% 7.78/1.48  fof(f46,plain,(
% 7.78/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f36])).
% 7.78/1.48  
% 7.78/1.48  fof(f55,plain,(
% 7.78/1.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f41])).
% 7.78/1.48  
% 7.78/1.48  fof(f12,axiom,(
% 7.78/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f28,plain,(
% 7.78/1.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.78/1.48    inference(ennf_transformation,[],[f12])).
% 7.78/1.48  
% 7.78/1.48  fof(f61,plain,(
% 7.78/1.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.78/1.48    inference(cnf_transformation,[],[f28])).
% 7.78/1.48  
% 7.78/1.48  fof(f10,axiom,(
% 7.78/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f26,plain,(
% 7.78/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.78/1.48    inference(ennf_transformation,[],[f10])).
% 7.78/1.48  
% 7.78/1.48  fof(f59,plain,(
% 7.78/1.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.78/1.48    inference(cnf_transformation,[],[f26])).
% 7.78/1.48  
% 7.78/1.48  fof(f11,axiom,(
% 7.78/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f27,plain,(
% 7.78/1.48    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.78/1.48    inference(ennf_transformation,[],[f11])).
% 7.78/1.48  
% 7.78/1.48  fof(f60,plain,(
% 7.78/1.48    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.78/1.48    inference(cnf_transformation,[],[f27])).
% 7.78/1.48  
% 7.78/1.48  fof(f2,axiom,(
% 7.78/1.48    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f18,plain,(
% 7.78/1.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.78/1.48    inference(ennf_transformation,[],[f2])).
% 7.78/1.48  
% 7.78/1.48  fof(f19,plain,(
% 7.78/1.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.78/1.48    inference(flattening,[],[f18])).
% 7.78/1.48  
% 7.78/1.48  fof(f47,plain,(
% 7.78/1.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f19])).
% 7.78/1.48  
% 7.78/1.48  fof(f13,axiom,(
% 7.78/1.48    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3))),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f29,plain,(
% 7.78/1.48    ! [X0,X1,X2,X3] : (k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.78/1.48    inference(ennf_transformation,[],[f13])).
% 7.78/1.48  
% 7.78/1.48  fof(f62,plain,(
% 7.78/1.48    ( ! [X2,X0,X3,X1] : (k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.78/1.48    inference(cnf_transformation,[],[f29])).
% 7.78/1.48  
% 7.78/1.48  fof(f14,axiom,(
% 7.78/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.78/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.48  
% 7.78/1.48  fof(f30,plain,(
% 7.78/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 7.78/1.48    inference(ennf_transformation,[],[f14])).
% 7.78/1.48  
% 7.78/1.48  fof(f31,plain,(
% 7.78/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 7.78/1.48    inference(flattening,[],[f30])).
% 7.78/1.48  
% 7.78/1.48  fof(f63,plain,(
% 7.78/1.48    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 7.78/1.48    inference(cnf_transformation,[],[f31])).
% 7.78/1.48  
% 7.78/1.48  fof(f65,plain,(
% 7.78/1.48    ~m1_subset_1(k6_relset_1(sK4,sK2,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))),
% 7.78/1.48    inference(cnf_transformation,[],[f43])).
% 7.78/1.48  
% 7.78/1.48  cnf(c_13,plain,
% 7.78/1.48      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~ v1_relat_1(X1) ),
% 7.78/1.48      inference(cnf_transformation,[],[f57]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_787,plain,
% 7.78/1.48      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) = iProver_top
% 7.78/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_14,plain,
% 7.78/1.48      ( r1_tarski(k8_relat_1(X0,X1),X1) | ~ v1_relat_1(X1) ),
% 7.78/1.48      inference(cnf_transformation,[],[f58]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_786,plain,
% 7.78/1.48      ( r1_tarski(k8_relat_1(X0,X1),X1) = iProver_top
% 7.78/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1,plain,
% 7.78/1.48      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.78/1.48      inference(cnf_transformation,[],[f45]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_799,plain,
% 7.78/1.48      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 7.78/1.48      | r1_tarski(X0,X1) = iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_2,plain,
% 7.78/1.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.78/1.48      inference(cnf_transformation,[],[f44]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_798,plain,
% 7.78/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.78/1.48      | r2_hidden(X0,X2) = iProver_top
% 7.78/1.48      | r1_tarski(X1,X2) != iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_3770,plain,
% 7.78/1.48      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 7.78/1.48      | r1_tarski(X0,X2) != iProver_top
% 7.78/1.48      | r1_tarski(X0,X1) = iProver_top ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_799,c_798]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_21,negated_conjecture,
% 7.78/1.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
% 7.78/1.48      inference(cnf_transformation,[],[f64]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_779,plain,
% 7.78/1.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_12,plain,
% 7.78/1.48      ( m1_subset_1(X0,X1)
% 7.78/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.78/1.48      | ~ r2_hidden(X0,X2) ),
% 7.78/1.48      inference(cnf_transformation,[],[f56]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_788,plain,
% 7.78/1.48      ( m1_subset_1(X0,X1) = iProver_top
% 7.78/1.48      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 7.78/1.48      | r2_hidden(X0,X2) != iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_3572,plain,
% 7.78/1.48      ( m1_subset_1(X0,k2_zfmisc_1(sK4,sK2)) = iProver_top
% 7.78/1.48      | r2_hidden(X0,sK5) != iProver_top ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_779,c_788]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_9,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.78/1.48      inference(cnf_transformation,[],[f53]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_791,plain,
% 7.78/1.48      ( m1_subset_1(X0,X1) != iProver_top
% 7.78/1.48      | r2_hidden(X0,X1) = iProver_top
% 7.78/1.48      | v1_xboole_0(X1) = iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_4260,plain,
% 7.78/1.48      ( r2_hidden(X0,k2_zfmisc_1(sK4,sK2)) = iProver_top
% 7.78/1.48      | r2_hidden(X0,sK5) != iProver_top
% 7.78/1.48      | v1_xboole_0(k2_zfmisc_1(sK4,sK2)) = iProver_top ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_3572,c_791]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_11,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.78/1.48      inference(cnf_transformation,[],[f54]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1034,plain,
% 7.78/1.48      ( r1_tarski(sK5,k2_zfmisc_1(sK4,sK2)) ),
% 7.78/1.48      inference(resolution,[status(thm)],[c_11,c_21]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_2457,plain,
% 7.78/1.48      ( r2_hidden(X0,k2_zfmisc_1(sK4,sK2)) | ~ r2_hidden(X0,sK5) ),
% 7.78/1.48      inference(resolution,[status(thm)],[c_2,c_1034]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_2458,plain,
% 7.78/1.48      ( r2_hidden(X0,k2_zfmisc_1(sK4,sK2)) = iProver_top
% 7.78/1.48      | r2_hidden(X0,sK5) != iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_2457]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_4346,plain,
% 7.78/1.48      ( r2_hidden(X0,sK5) != iProver_top
% 7.78/1.48      | r2_hidden(X0,k2_zfmisc_1(sK4,sK2)) = iProver_top ),
% 7.78/1.48      inference(global_propositional_subsumption,
% 7.78/1.48                [status(thm)],
% 7.78/1.48                [c_4260,c_2458]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_4347,plain,
% 7.78/1.48      ( r2_hidden(X0,k2_zfmisc_1(sK4,sK2)) = iProver_top
% 7.78/1.48      | r2_hidden(X0,sK5) != iProver_top ),
% 7.78/1.48      inference(renaming,[status(thm)],[c_4346]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_0,plain,
% 7.78/1.48      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.78/1.48      inference(cnf_transformation,[],[f46]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_800,plain,
% 7.78/1.48      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 7.78/1.48      | r1_tarski(X0,X1) = iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_4352,plain,
% 7.78/1.48      ( r2_hidden(sK0(X0,k2_zfmisc_1(sK4,sK2)),sK5) != iProver_top
% 7.78/1.48      | r1_tarski(X0,k2_zfmisc_1(sK4,sK2)) = iProver_top ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_4347,c_800]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_9311,plain,
% 7.78/1.48      ( r1_tarski(X0,k2_zfmisc_1(sK4,sK2)) = iProver_top
% 7.78/1.48      | r1_tarski(X0,sK5) != iProver_top ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_3770,c_4352]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_10,plain,
% 7.78/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.78/1.48      inference(cnf_transformation,[],[f55]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_790,plain,
% 7.78/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.78/1.48      | r1_tarski(X0,X1) != iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_17,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.78/1.48      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.78/1.48      inference(cnf_transformation,[],[f61]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_783,plain,
% 7.78/1.48      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.78/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_2203,plain,
% 7.78/1.48      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.78/1.48      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_790,c_783]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_10603,plain,
% 7.78/1.48      ( k1_relset_1(sK4,sK2,X0) = k1_relat_1(X0)
% 7.78/1.48      | r1_tarski(X0,sK5) != iProver_top ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_9311,c_2203]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_15160,plain,
% 7.78/1.48      ( k1_relset_1(sK4,sK2,k8_relat_1(X0,sK5)) = k1_relat_1(k8_relat_1(X0,sK5))
% 7.78/1.48      | v1_relat_1(sK5) != iProver_top ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_786,c_10603]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_22,plain,
% 7.78/1.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_15,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.78/1.48      | v1_relat_1(X0) ),
% 7.78/1.48      inference(cnf_transformation,[],[f59]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_967,plain,
% 7.78/1.48      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 7.78/1.48      | v1_relat_1(sK5) ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_15]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_968,plain,
% 7.78/1.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 7.78/1.48      | v1_relat_1(sK5) = iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_967]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_16874,plain,
% 7.78/1.48      ( k1_relset_1(sK4,sK2,k8_relat_1(X0,sK5)) = k1_relat_1(k8_relat_1(X0,sK5)) ),
% 7.78/1.48      inference(global_propositional_subsumption,
% 7.78/1.48                [status(thm)],
% 7.78/1.48                [c_15160,c_22,c_968]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_16,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.78/1.48      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 7.78/1.48      inference(cnf_transformation,[],[f60]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_784,plain,
% 7.78/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.78/1.48      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_16880,plain,
% 7.78/1.48      ( m1_subset_1(k8_relat_1(X0,sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 7.78/1.48      | m1_subset_1(k1_relat_1(k8_relat_1(X0,sK5)),k1_zfmisc_1(sK4)) = iProver_top ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_16874,c_784]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1035,plain,
% 7.78/1.48      ( r1_tarski(sK5,k2_zfmisc_1(sK4,sK2)) = iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_1034]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1099,plain,
% 7.78/1.48      ( r1_tarski(k8_relat_1(X0,sK5),sK5) | ~ v1_relat_1(sK5) ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_14]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1105,plain,
% 7.78/1.48      ( r1_tarski(k8_relat_1(X0,sK5),sK5) = iProver_top
% 7.78/1.48      | v1_relat_1(sK5) != iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_1099]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_3,plain,
% 7.78/1.48      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 7.78/1.48      inference(cnf_transformation,[],[f47]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1139,plain,
% 7.78/1.48      ( ~ r1_tarski(X0,X1)
% 7.78/1.48      | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
% 7.78/1.48      | r1_tarski(X0,k2_zfmisc_1(X2,X3)) ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_3]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_3391,plain,
% 7.78/1.48      ( r1_tarski(X0,k2_zfmisc_1(sK4,sK2))
% 7.78/1.48      | ~ r1_tarski(X0,sK5)
% 7.78/1.48      | ~ r1_tarski(sK5,k2_zfmisc_1(sK4,sK2)) ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_1139]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_7385,plain,
% 7.78/1.48      ( r1_tarski(k8_relat_1(X0,sK5),k2_zfmisc_1(sK4,sK2))
% 7.78/1.48      | ~ r1_tarski(k8_relat_1(X0,sK5),sK5)
% 7.78/1.48      | ~ r1_tarski(sK5,k2_zfmisc_1(sK4,sK2)) ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_3391]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_7386,plain,
% 7.78/1.48      ( r1_tarski(k8_relat_1(X0,sK5),k2_zfmisc_1(sK4,sK2)) = iProver_top
% 7.78/1.48      | r1_tarski(k8_relat_1(X0,sK5),sK5) != iProver_top
% 7.78/1.48      | r1_tarski(sK5,k2_zfmisc_1(sK4,sK2)) != iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_7385]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_962,plain,
% 7.78/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.78/1.48      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_10]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_18282,plain,
% 7.78/1.48      ( m1_subset_1(k8_relat_1(X0,sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 7.78/1.48      | ~ r1_tarski(k8_relat_1(X0,sK5),k2_zfmisc_1(sK4,sK2)) ),
% 7.78/1.48      inference(instantiation,[status(thm)],[c_962]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_18283,plain,
% 7.78/1.48      ( m1_subset_1(k8_relat_1(X0,sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top
% 7.78/1.48      | r1_tarski(k8_relat_1(X0,sK5),k2_zfmisc_1(sK4,sK2)) != iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_18282]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_19331,plain,
% 7.78/1.48      ( m1_subset_1(k1_relat_1(k8_relat_1(X0,sK5)),k1_zfmisc_1(sK4)) = iProver_top ),
% 7.78/1.48      inference(global_propositional_subsumption,
% 7.78/1.48                [status(thm)],
% 7.78/1.48                [c_16880,c_22,c_968,c_1035,c_1105,c_7386,c_18283]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_789,plain,
% 7.78/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.78/1.48      | r1_tarski(X0,X1) = iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_19339,plain,
% 7.78/1.48      ( r1_tarski(k1_relat_1(k8_relat_1(X0,sK5)),sK4) = iProver_top ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_19331,c_789]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_18,plain,
% 7.78/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.78/1.48      | k6_relset_1(X1,X2,X3,X0) = k8_relat_1(X3,X0) ),
% 7.78/1.48      inference(cnf_transformation,[],[f62]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_782,plain,
% 7.78/1.48      ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
% 7.78/1.48      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_2178,plain,
% 7.78/1.48      ( k6_relset_1(sK4,sK2,X0,sK5) = k8_relat_1(X0,sK5) ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_779,c_782]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_19,plain,
% 7.78/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.78/1.48      | ~ r1_tarski(k1_relat_1(X0),X1)
% 7.78/1.48      | ~ r1_tarski(k2_relat_1(X0),X2)
% 7.78/1.48      | ~ v1_relat_1(X0) ),
% 7.78/1.48      inference(cnf_transformation,[],[f63]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_781,plain,
% 7.78/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 7.78/1.48      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.78/1.48      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 7.78/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_20,negated_conjecture,
% 7.78/1.48      ( ~ m1_subset_1(k6_relset_1(sK4,sK2,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
% 7.78/1.48      inference(cnf_transformation,[],[f65]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_780,plain,
% 7.78/1.48      ( m1_subset_1(k6_relset_1(sK4,sK2,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1282,plain,
% 7.78/1.48      ( r1_tarski(k1_relat_1(k6_relset_1(sK4,sK2,sK3,sK5)),sK4) != iProver_top
% 7.78/1.48      | r1_tarski(k2_relat_1(k6_relset_1(sK4,sK2,sK3,sK5)),sK3) != iProver_top
% 7.78/1.48      | v1_relat_1(k6_relset_1(sK4,sK2,sK3,sK5)) != iProver_top ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_781,c_780]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_2802,plain,
% 7.78/1.48      ( r1_tarski(k1_relat_1(k8_relat_1(sK3,sK5)),sK4) != iProver_top
% 7.78/1.48      | r1_tarski(k2_relat_1(k8_relat_1(sK3,sK5)),sK3) != iProver_top
% 7.78/1.48      | v1_relat_1(k8_relat_1(sK3,sK5)) != iProver_top ),
% 7.78/1.48      inference(demodulation,[status(thm)],[c_2178,c_1282]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_20999,plain,
% 7.78/1.48      ( r1_tarski(k2_relat_1(k8_relat_1(sK3,sK5)),sK3) != iProver_top
% 7.78/1.48      | v1_relat_1(k8_relat_1(sK3,sK5)) != iProver_top ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_19339,c_2802]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_785,plain,
% 7.78/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.78/1.48      | v1_relat_1(X0) = iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1526,plain,
% 7.78/1.48      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 7.78/1.48      | v1_relat_1(X0) = iProver_top ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_790,c_785]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_10599,plain,
% 7.78/1.48      ( r1_tarski(X0,sK5) != iProver_top | v1_relat_1(X0) = iProver_top ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_9311,c_1526]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_15085,plain,
% 7.78/1.48      ( v1_relat_1(k8_relat_1(X0,sK5)) = iProver_top
% 7.78/1.48      | v1_relat_1(sK5) != iProver_top ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_786,c_10599]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_2575,plain,
% 7.78/1.48      ( r1_tarski(X0,k2_zfmisc_1(sK4,sK2)) | ~ r1_tarski(X0,sK5) ),
% 7.78/1.48      inference(resolution,[status(thm)],[c_3,c_1034]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_1547,plain,
% 7.78/1.48      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) | v1_relat_1(X0) ),
% 7.78/1.48      inference(resolution,[status(thm)],[c_15,c_10]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_2838,plain,
% 7.78/1.48      ( ~ r1_tarski(X0,sK5) | v1_relat_1(X0) ),
% 7.78/1.48      inference(resolution,[status(thm)],[c_2575,c_1547]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_3064,plain,
% 7.78/1.48      ( v1_relat_1(k8_relat_1(X0,sK5)) | ~ v1_relat_1(sK5) ),
% 7.78/1.48      inference(resolution,[status(thm)],[c_2838,c_14]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_3065,plain,
% 7.78/1.48      ( v1_relat_1(k8_relat_1(X0,sK5)) = iProver_top
% 7.78/1.48      | v1_relat_1(sK5) != iProver_top ),
% 7.78/1.48      inference(predicate_to_equality,[status(thm)],[c_3064]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_16726,plain,
% 7.78/1.48      ( v1_relat_1(k8_relat_1(X0,sK5)) = iProver_top ),
% 7.78/1.48      inference(global_propositional_subsumption,
% 7.78/1.48                [status(thm)],
% 7.78/1.48                [c_15085,c_22,c_968,c_3065]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_21900,plain,
% 7.78/1.48      ( r1_tarski(k2_relat_1(k8_relat_1(sK3,sK5)),sK3) != iProver_top ),
% 7.78/1.48      inference(forward_subsumption_resolution,
% 7.78/1.48                [status(thm)],
% 7.78/1.48                [c_20999,c_16726]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(c_21902,plain,
% 7.78/1.48      ( v1_relat_1(sK5) != iProver_top ),
% 7.78/1.48      inference(superposition,[status(thm)],[c_787,c_21900]) ).
% 7.78/1.48  
% 7.78/1.48  cnf(contradiction,plain,
% 7.78/1.48      ( $false ),
% 7.78/1.48      inference(minisat,[status(thm)],[c_21902,c_968,c_22]) ).
% 7.78/1.48  
% 7.78/1.48  
% 7.78/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.78/1.48  
% 7.78/1.48  ------                               Statistics
% 7.78/1.48  
% 7.78/1.48  ------ Selected
% 7.78/1.48  
% 7.78/1.48  total_time:                             0.615
% 7.78/1.48  
%------------------------------------------------------------------------------
