%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:55:59 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 300 expanded)
%              Number of clauses        :   66 ( 122 expanded)
%              Number of leaves         :   17 (  58 expanded)
%              Depth                    :   15
%              Number of atoms          :  262 ( 708 expanded)
%              Number of equality atoms :  131 ( 369 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
          & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f41,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1)
        | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f45,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1)
          | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
        | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
      | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f45])).

fof(f68,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f58,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f69,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
    | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_970,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_973,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1526,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_970,c_973])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_975,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1637,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1526,c_975])).

cnf(c_23,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1795,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1637,c_23])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_984,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1800,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1795,c_984])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_977,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1342,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_970,c_977])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_979,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1546,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1342,c_979])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_978,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3073,plain,
    ( r1_tarski(k2_relat_1(sK2),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X0)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1546,c_978])).

cnf(c_1134,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1135,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1134])).

cnf(c_3218,plain,
    ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X0)) = iProver_top
    | r1_tarski(k2_relat_1(sK2),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3073,c_23,c_1135])).

cnf(c_3219,plain,
    ( r1_tarski(k2_relat_1(sK2),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3218])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_988,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3228,plain,
    ( k10_relat_1(sK2,X0) = k1_relat_1(sK2)
    | r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2)) != iProver_top
    | r1_tarski(k2_relat_1(sK2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3219,c_988])).

cnf(c_10,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1194,plain,
    ( r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1201,plain,
    ( r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1194])).

cnf(c_6019,plain,
    ( k10_relat_1(sK2,X0) = k1_relat_1(sK2)
    | r1_tarski(k2_relat_1(sK2),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3228,c_23,c_1135,c_1201])).

cnf(c_6029,plain,
    ( k10_relat_1(sK2,sK1) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1800,c_6019])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_983,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1545,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1342,c_983])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_981,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3113,plain,
    ( r1_tarski(k2_relat_1(sK2),k9_relat_1(sK2,X0)) = iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1545,c_981])).

cnf(c_3140,plain,
    ( r1_tarski(k2_relat_1(sK2),k9_relat_1(sK2,sK0)) = iProver_top
    | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3113])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_974,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2006,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_970,c_974])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_976,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2286,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2006,c_976])).

cnf(c_2612,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2286,c_23])).

cnf(c_2617,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2612,c_984])).

cnf(c_21,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)
    | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1636,plain,
    ( k8_relset_1(sK0,sK1,sK2,sK1) != k1_relset_1(sK0,sK1,sK2)
    | k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1526,c_21])).

cnf(c_2285,plain,
    ( k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2)
    | k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2006,c_1636])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_971,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2130,plain,
    ( k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_970,c_971])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_972,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2161,plain,
    ( k7_relset_1(sK0,sK1,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_970,c_972])).

cnf(c_2495,plain,
    ( k10_relat_1(sK2,sK1) != k1_relat_1(sK2)
    | k9_relat_1(sK2,sK0) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2285,c_2130,c_2161])).

cnf(c_8,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,k1_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_982,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,k1_relat_1(X0))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1720,plain,
    ( r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1545,c_982])).

cnf(c_1889,plain,
    ( r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1720,c_23,c_1135])).

cnf(c_2038,plain,
    ( k9_relat_1(sK2,X0) = k2_relat_1(sK2)
    | r1_tarski(k2_relat_1(sK2),k9_relat_1(sK2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1889,c_988])).

cnf(c_2072,plain,
    ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2)
    | r1_tarski(k2_relat_1(sK2),k9_relat_1(sK2,sK0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2038])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6029,c_3140,c_2617,c_2495,c_2072,c_1135,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.07  % Command    : iproveropt_run.sh %d %s
% 0.08/0.26  % Computer   : n006.cluster.edu
% 0.08/0.26  % Model      : x86_64 x86_64
% 0.08/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.26  % Memory     : 8042.1875MB
% 0.08/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.26  % CPULimit   : 60
% 0.08/0.26  % WCLimit    : 600
% 0.08/0.26  % DateTime   : Tue Dec  1 11:24:07 EST 2020
% 0.08/0.26  % CPUTime    : 
% 0.08/0.26  % Running in FOF mode
% 3.03/0.83  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.03/0.83  
% 3.03/0.83  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.03/0.83  
% 3.03/0.83  ------  iProver source info
% 3.03/0.83  
% 3.03/0.83  git: date: 2020-06-30 10:37:57 +0100
% 3.03/0.83  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.03/0.83  git: non_committed_changes: false
% 3.03/0.83  git: last_make_outside_of_git: false
% 3.03/0.83  
% 3.03/0.83  ------ 
% 3.03/0.83  
% 3.03/0.83  ------ Input Options
% 3.03/0.83  
% 3.03/0.83  --out_options                           all
% 3.03/0.83  --tptp_safe_out                         true
% 3.03/0.83  --problem_path                          ""
% 3.03/0.83  --include_path                          ""
% 3.03/0.83  --clausifier                            res/vclausify_rel
% 3.03/0.83  --clausifier_options                    --mode clausify
% 3.03/0.83  --stdin                                 false
% 3.03/0.83  --stats_out                             all
% 3.03/0.83  
% 3.03/0.83  ------ General Options
% 3.03/0.83  
% 3.03/0.83  --fof                                   false
% 3.03/0.83  --time_out_real                         305.
% 3.03/0.83  --time_out_virtual                      -1.
% 3.03/0.83  --symbol_type_check                     false
% 3.03/0.83  --clausify_out                          false
% 3.03/0.83  --sig_cnt_out                           false
% 3.03/0.83  --trig_cnt_out                          false
% 3.03/0.83  --trig_cnt_out_tolerance                1.
% 3.03/0.83  --trig_cnt_out_sk_spl                   false
% 3.03/0.83  --abstr_cl_out                          false
% 3.03/0.83  
% 3.03/0.83  ------ Global Options
% 3.03/0.83  
% 3.03/0.83  --schedule                              default
% 3.03/0.83  --add_important_lit                     false
% 3.03/0.83  --prop_solver_per_cl                    1000
% 3.03/0.83  --min_unsat_core                        false
% 3.03/0.83  --soft_assumptions                      false
% 3.03/0.83  --soft_lemma_size                       3
% 3.03/0.83  --prop_impl_unit_size                   0
% 3.03/0.83  --prop_impl_unit                        []
% 3.03/0.83  --share_sel_clauses                     true
% 3.03/0.83  --reset_solvers                         false
% 3.03/0.83  --bc_imp_inh                            [conj_cone]
% 3.03/0.83  --conj_cone_tolerance                   3.
% 3.03/0.83  --extra_neg_conj                        none
% 3.03/0.83  --large_theory_mode                     true
% 3.03/0.83  --prolific_symb_bound                   200
% 3.03/0.83  --lt_threshold                          2000
% 3.03/0.83  --clause_weak_htbl                      true
% 3.03/0.83  --gc_record_bc_elim                     false
% 3.03/0.83  
% 3.03/0.83  ------ Preprocessing Options
% 3.03/0.83  
% 3.03/0.83  --preprocessing_flag                    true
% 3.03/0.83  --time_out_prep_mult                    0.1
% 3.03/0.83  --splitting_mode                        input
% 3.03/0.83  --splitting_grd                         true
% 3.03/0.83  --splitting_cvd                         false
% 3.03/0.83  --splitting_cvd_svl                     false
% 3.03/0.83  --splitting_nvd                         32
% 3.03/0.83  --sub_typing                            true
% 3.03/0.83  --prep_gs_sim                           true
% 3.03/0.83  --prep_unflatten                        true
% 3.03/0.83  --prep_res_sim                          true
% 3.03/0.83  --prep_upred                            true
% 3.03/0.83  --prep_sem_filter                       exhaustive
% 3.03/0.83  --prep_sem_filter_out                   false
% 3.03/0.83  --pred_elim                             true
% 3.03/0.83  --res_sim_input                         true
% 3.03/0.83  --eq_ax_congr_red                       true
% 3.03/0.83  --pure_diseq_elim                       true
% 3.03/0.83  --brand_transform                       false
% 3.03/0.83  --non_eq_to_eq                          false
% 3.03/0.83  --prep_def_merge                        true
% 3.03/0.83  --prep_def_merge_prop_impl              false
% 3.03/0.83  --prep_def_merge_mbd                    true
% 3.03/0.83  --prep_def_merge_tr_red                 false
% 3.03/0.83  --prep_def_merge_tr_cl                  false
% 3.03/0.83  --smt_preprocessing                     true
% 3.03/0.83  --smt_ac_axioms                         fast
% 3.03/0.83  --preprocessed_out                      false
% 3.03/0.83  --preprocessed_stats                    false
% 3.03/0.83  
% 3.03/0.83  ------ Abstraction refinement Options
% 3.03/0.83  
% 3.03/0.83  --abstr_ref                             []
% 3.03/0.83  --abstr_ref_prep                        false
% 3.03/0.83  --abstr_ref_until_sat                   false
% 3.03/0.83  --abstr_ref_sig_restrict                funpre
% 3.03/0.83  --abstr_ref_af_restrict_to_split_sk     false
% 3.03/0.83  --abstr_ref_under                       []
% 3.03/0.83  
% 3.03/0.83  ------ SAT Options
% 3.03/0.83  
% 3.03/0.83  --sat_mode                              false
% 3.03/0.83  --sat_fm_restart_options                ""
% 3.03/0.83  --sat_gr_def                            false
% 3.03/0.83  --sat_epr_types                         true
% 3.03/0.83  --sat_non_cyclic_types                  false
% 3.03/0.83  --sat_finite_models                     false
% 3.03/0.83  --sat_fm_lemmas                         false
% 3.03/0.83  --sat_fm_prep                           false
% 3.03/0.83  --sat_fm_uc_incr                        true
% 3.03/0.83  --sat_out_model                         small
% 3.03/0.83  --sat_out_clauses                       false
% 3.03/0.83  
% 3.03/0.83  ------ QBF Options
% 3.03/0.83  
% 3.03/0.83  --qbf_mode                              false
% 3.03/0.83  --qbf_elim_univ                         false
% 3.03/0.83  --qbf_dom_inst                          none
% 3.03/0.83  --qbf_dom_pre_inst                      false
% 3.03/0.83  --qbf_sk_in                             false
% 3.03/0.83  --qbf_pred_elim                         true
% 3.03/0.83  --qbf_split                             512
% 3.03/0.83  
% 3.03/0.83  ------ BMC1 Options
% 3.03/0.83  
% 3.03/0.83  --bmc1_incremental                      false
% 3.03/0.83  --bmc1_axioms                           reachable_all
% 3.03/0.83  --bmc1_min_bound                        0
% 3.03/0.83  --bmc1_max_bound                        -1
% 3.03/0.83  --bmc1_max_bound_default                -1
% 3.03/0.83  --bmc1_symbol_reachability              true
% 3.03/0.83  --bmc1_property_lemmas                  false
% 3.03/0.83  --bmc1_k_induction                      false
% 3.03/0.83  --bmc1_non_equiv_states                 false
% 3.03/0.83  --bmc1_deadlock                         false
% 3.03/0.83  --bmc1_ucm                              false
% 3.03/0.83  --bmc1_add_unsat_core                   none
% 3.03/0.83  --bmc1_unsat_core_children              false
% 3.03/0.83  --bmc1_unsat_core_extrapolate_axioms    false
% 3.03/0.83  --bmc1_out_stat                         full
% 3.03/0.83  --bmc1_ground_init                      false
% 3.03/0.83  --bmc1_pre_inst_next_state              false
% 3.03/0.83  --bmc1_pre_inst_state                   false
% 3.03/0.83  --bmc1_pre_inst_reach_state             false
% 3.03/0.83  --bmc1_out_unsat_core                   false
% 3.03/0.83  --bmc1_aig_witness_out                  false
% 3.03/0.83  --bmc1_verbose                          false
% 3.03/0.83  --bmc1_dump_clauses_tptp                false
% 3.03/0.83  --bmc1_dump_unsat_core_tptp             false
% 3.03/0.83  --bmc1_dump_file                        -
% 3.03/0.83  --bmc1_ucm_expand_uc_limit              128
% 3.03/0.83  --bmc1_ucm_n_expand_iterations          6
% 3.03/0.83  --bmc1_ucm_extend_mode                  1
% 3.03/0.83  --bmc1_ucm_init_mode                    2
% 3.03/0.83  --bmc1_ucm_cone_mode                    none
% 3.03/0.83  --bmc1_ucm_reduced_relation_type        0
% 3.03/0.83  --bmc1_ucm_relax_model                  4
% 3.03/0.83  --bmc1_ucm_full_tr_after_sat            true
% 3.03/0.83  --bmc1_ucm_expand_neg_assumptions       false
% 3.03/0.83  --bmc1_ucm_layered_model                none
% 3.03/0.83  --bmc1_ucm_max_lemma_size               10
% 3.03/0.83  
% 3.03/0.83  ------ AIG Options
% 3.03/0.83  
% 3.03/0.83  --aig_mode                              false
% 3.03/0.83  
% 3.03/0.83  ------ Instantiation Options
% 3.03/0.83  
% 3.03/0.83  --instantiation_flag                    true
% 3.03/0.83  --inst_sos_flag                         false
% 3.03/0.83  --inst_sos_phase                        true
% 3.03/0.83  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.03/0.83  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.03/0.83  --inst_lit_sel_side                     num_symb
% 3.03/0.83  --inst_solver_per_active                1400
% 3.03/0.83  --inst_solver_calls_frac                1.
% 3.03/0.83  --inst_passive_queue_type               priority_queues
% 3.03/0.83  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.03/0.83  --inst_passive_queues_freq              [25;2]
% 3.03/0.83  --inst_dismatching                      true
% 3.03/0.83  --inst_eager_unprocessed_to_passive     true
% 3.03/0.83  --inst_prop_sim_given                   true
% 3.03/0.83  --inst_prop_sim_new                     false
% 3.03/0.83  --inst_subs_new                         false
% 3.03/0.83  --inst_eq_res_simp                      false
% 3.03/0.83  --inst_subs_given                       false
% 3.03/0.83  --inst_orphan_elimination               true
% 3.03/0.83  --inst_learning_loop_flag               true
% 3.03/0.83  --inst_learning_start                   3000
% 3.03/0.83  --inst_learning_factor                  2
% 3.03/0.83  --inst_start_prop_sim_after_learn       3
% 3.03/0.83  --inst_sel_renew                        solver
% 3.03/0.83  --inst_lit_activity_flag                true
% 3.03/0.83  --inst_restr_to_given                   false
% 3.03/0.83  --inst_activity_threshold               500
% 3.03/0.83  --inst_out_proof                        true
% 3.03/0.83  
% 3.03/0.83  ------ Resolution Options
% 3.03/0.83  
% 3.03/0.83  --resolution_flag                       true
% 3.03/0.83  --res_lit_sel                           adaptive
% 3.03/0.83  --res_lit_sel_side                      none
% 3.03/0.83  --res_ordering                          kbo
% 3.03/0.83  --res_to_prop_solver                    active
% 3.03/0.83  --res_prop_simpl_new                    false
% 3.03/0.83  --res_prop_simpl_given                  true
% 3.03/0.83  --res_passive_queue_type                priority_queues
% 3.03/0.83  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.03/0.83  --res_passive_queues_freq               [15;5]
% 3.03/0.83  --res_forward_subs                      full
% 3.03/0.83  --res_backward_subs                     full
% 3.03/0.83  --res_forward_subs_resolution           true
% 3.03/0.83  --res_backward_subs_resolution          true
% 3.03/0.83  --res_orphan_elimination                true
% 3.03/0.83  --res_time_limit                        2.
% 3.03/0.83  --res_out_proof                         true
% 3.03/0.83  
% 3.03/0.83  ------ Superposition Options
% 3.03/0.83  
% 3.03/0.83  --superposition_flag                    true
% 3.03/0.83  --sup_passive_queue_type                priority_queues
% 3.03/0.83  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.03/0.83  --sup_passive_queues_freq               [8;1;4]
% 3.03/0.83  --demod_completeness_check              fast
% 3.03/0.83  --demod_use_ground                      true
% 3.03/0.83  --sup_to_prop_solver                    passive
% 3.03/0.83  --sup_prop_simpl_new                    true
% 3.03/0.83  --sup_prop_simpl_given                  true
% 3.03/0.83  --sup_fun_splitting                     false
% 3.03/0.83  --sup_smt_interval                      50000
% 3.03/0.83  
% 3.03/0.83  ------ Superposition Simplification Setup
% 3.03/0.83  
% 3.03/0.83  --sup_indices_passive                   []
% 3.03/0.83  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/0.83  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/0.83  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/0.83  --sup_full_triv                         [TrivRules;PropSubs]
% 3.03/0.83  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/0.83  --sup_full_bw                           [BwDemod]
% 3.03/0.83  --sup_immed_triv                        [TrivRules]
% 3.03/0.83  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.03/0.83  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/0.83  --sup_immed_bw_main                     []
% 3.03/0.83  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/0.83  --sup_input_triv                        [Unflattening;TrivRules]
% 3.03/0.83  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/0.83  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/0.83  
% 3.03/0.83  ------ Combination Options
% 3.03/0.83  
% 3.03/0.83  --comb_res_mult                         3
% 3.03/0.83  --comb_sup_mult                         2
% 3.03/0.83  --comb_inst_mult                        10
% 3.03/0.83  
% 3.03/0.83  ------ Debug Options
% 3.03/0.83  
% 3.03/0.83  --dbg_backtrace                         false
% 3.03/0.83  --dbg_dump_prop_clauses                 false
% 3.03/0.83  --dbg_dump_prop_clauses_file            -
% 3.03/0.83  --dbg_out_stat                          false
% 3.03/0.83  ------ Parsing...
% 3.03/0.83  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.03/0.83  
% 3.03/0.83  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.03/0.83  
% 3.03/0.83  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.03/0.83  
% 3.03/0.83  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.03/0.83  ------ Proving...
% 3.03/0.83  ------ Problem Properties 
% 3.03/0.83  
% 3.03/0.83  
% 3.03/0.83  clauses                                 22
% 3.03/0.83  conjectures                             2
% 3.03/0.83  EPR                                     4
% 3.03/0.83  Horn                                    22
% 3.03/0.83  unary                                   2
% 3.03/0.83  binary                                  14
% 3.03/0.83  lits                                    48
% 3.03/0.83  lits eq                                 9
% 3.03/0.83  fd_pure                                 0
% 3.03/0.83  fd_pseudo                               0
% 3.03/0.83  fd_cond                                 0
% 3.03/0.83  fd_pseudo_cond                          1
% 3.03/0.83  AC symbols                              0
% 3.03/0.83  
% 3.03/0.83  ------ Schedule dynamic 5 is on 
% 3.03/0.83  
% 3.03/0.83  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.03/0.83  
% 3.03/0.83  
% 3.03/0.83  ------ 
% 3.03/0.83  Current options:
% 3.03/0.83  ------ 
% 3.03/0.83  
% 3.03/0.83  ------ Input Options
% 3.03/0.83  
% 3.03/0.83  --out_options                           all
% 3.03/0.83  --tptp_safe_out                         true
% 3.03/0.83  --problem_path                          ""
% 3.03/0.83  --include_path                          ""
% 3.03/0.83  --clausifier                            res/vclausify_rel
% 3.03/0.83  --clausifier_options                    --mode clausify
% 3.03/0.83  --stdin                                 false
% 3.03/0.83  --stats_out                             all
% 3.03/0.83  
% 3.03/0.83  ------ General Options
% 3.03/0.83  
% 3.03/0.83  --fof                                   false
% 3.03/0.83  --time_out_real                         305.
% 3.03/0.83  --time_out_virtual                      -1.
% 3.03/0.83  --symbol_type_check                     false
% 3.03/0.83  --clausify_out                          false
% 3.03/0.83  --sig_cnt_out                           false
% 3.03/0.83  --trig_cnt_out                          false
% 3.03/0.83  --trig_cnt_out_tolerance                1.
% 3.03/0.83  --trig_cnt_out_sk_spl                   false
% 3.03/0.83  --abstr_cl_out                          false
% 3.03/0.83  
% 3.03/0.83  ------ Global Options
% 3.03/0.83  
% 3.03/0.83  --schedule                              default
% 3.03/0.83  --add_important_lit                     false
% 3.03/0.83  --prop_solver_per_cl                    1000
% 3.03/0.83  --min_unsat_core                        false
% 3.03/0.83  --soft_assumptions                      false
% 3.03/0.83  --soft_lemma_size                       3
% 3.03/0.83  --prop_impl_unit_size                   0
% 3.03/0.83  --prop_impl_unit                        []
% 3.03/0.83  --share_sel_clauses                     true
% 3.03/0.83  --reset_solvers                         false
% 3.03/0.83  --bc_imp_inh                            [conj_cone]
% 3.03/0.83  --conj_cone_tolerance                   3.
% 3.03/0.83  --extra_neg_conj                        none
% 3.03/0.83  --large_theory_mode                     true
% 3.03/0.83  --prolific_symb_bound                   200
% 3.03/0.83  --lt_threshold                          2000
% 3.03/0.83  --clause_weak_htbl                      true
% 3.03/0.83  --gc_record_bc_elim                     false
% 3.03/0.83  
% 3.03/0.83  ------ Preprocessing Options
% 3.03/0.83  
% 3.03/0.83  --preprocessing_flag                    true
% 3.03/0.83  --time_out_prep_mult                    0.1
% 3.03/0.83  --splitting_mode                        input
% 3.03/0.83  --splitting_grd                         true
% 3.03/0.83  --splitting_cvd                         false
% 3.03/0.83  --splitting_cvd_svl                     false
% 3.03/0.83  --splitting_nvd                         32
% 3.03/0.83  --sub_typing                            true
% 3.03/0.83  --prep_gs_sim                           true
% 3.03/0.83  --prep_unflatten                        true
% 3.03/0.83  --prep_res_sim                          true
% 3.03/0.83  --prep_upred                            true
% 3.03/0.83  --prep_sem_filter                       exhaustive
% 3.03/0.83  --prep_sem_filter_out                   false
% 3.03/0.83  --pred_elim                             true
% 3.03/0.83  --res_sim_input                         true
% 3.03/0.83  --eq_ax_congr_red                       true
% 3.03/0.83  --pure_diseq_elim                       true
% 3.03/0.83  --brand_transform                       false
% 3.03/0.83  --non_eq_to_eq                          false
% 3.03/0.83  --prep_def_merge                        true
% 3.03/0.83  --prep_def_merge_prop_impl              false
% 3.03/0.83  --prep_def_merge_mbd                    true
% 3.03/0.83  --prep_def_merge_tr_red                 false
% 3.03/0.83  --prep_def_merge_tr_cl                  false
% 3.03/0.83  --smt_preprocessing                     true
% 3.03/0.83  --smt_ac_axioms                         fast
% 3.03/0.83  --preprocessed_out                      false
% 3.03/0.83  --preprocessed_stats                    false
% 3.03/0.83  
% 3.03/0.83  ------ Abstraction refinement Options
% 3.03/0.83  
% 3.03/0.83  --abstr_ref                             []
% 3.03/0.83  --abstr_ref_prep                        false
% 3.03/0.83  --abstr_ref_until_sat                   false
% 3.03/0.83  --abstr_ref_sig_restrict                funpre
% 3.03/0.83  --abstr_ref_af_restrict_to_split_sk     false
% 3.03/0.83  --abstr_ref_under                       []
% 3.03/0.83  
% 3.03/0.83  ------ SAT Options
% 3.03/0.83  
% 3.03/0.83  --sat_mode                              false
% 3.03/0.83  --sat_fm_restart_options                ""
% 3.03/0.83  --sat_gr_def                            false
% 3.03/0.83  --sat_epr_types                         true
% 3.03/0.83  --sat_non_cyclic_types                  false
% 3.03/0.83  --sat_finite_models                     false
% 3.03/0.83  --sat_fm_lemmas                         false
% 3.03/0.83  --sat_fm_prep                           false
% 3.03/0.83  --sat_fm_uc_incr                        true
% 3.03/0.83  --sat_out_model                         small
% 3.03/0.83  --sat_out_clauses                       false
% 3.03/0.83  
% 3.03/0.83  ------ QBF Options
% 3.03/0.83  
% 3.03/0.83  --qbf_mode                              false
% 3.03/0.83  --qbf_elim_univ                         false
% 3.03/0.83  --qbf_dom_inst                          none
% 3.03/0.83  --qbf_dom_pre_inst                      false
% 3.03/0.83  --qbf_sk_in                             false
% 3.03/0.83  --qbf_pred_elim                         true
% 3.03/0.83  --qbf_split                             512
% 3.03/0.83  
% 3.03/0.83  ------ BMC1 Options
% 3.03/0.83  
% 3.03/0.83  --bmc1_incremental                      false
% 3.03/0.83  --bmc1_axioms                           reachable_all
% 3.03/0.83  --bmc1_min_bound                        0
% 3.03/0.83  --bmc1_max_bound                        -1
% 3.03/0.83  --bmc1_max_bound_default                -1
% 3.03/0.83  --bmc1_symbol_reachability              true
% 3.03/0.83  --bmc1_property_lemmas                  false
% 3.03/0.83  --bmc1_k_induction                      false
% 3.03/0.83  --bmc1_non_equiv_states                 false
% 3.03/0.83  --bmc1_deadlock                         false
% 3.03/0.83  --bmc1_ucm                              false
% 3.03/0.83  --bmc1_add_unsat_core                   none
% 3.03/0.83  --bmc1_unsat_core_children              false
% 3.03/0.83  --bmc1_unsat_core_extrapolate_axioms    false
% 3.03/0.83  --bmc1_out_stat                         full
% 3.03/0.83  --bmc1_ground_init                      false
% 3.03/0.83  --bmc1_pre_inst_next_state              false
% 3.03/0.83  --bmc1_pre_inst_state                   false
% 3.03/0.83  --bmc1_pre_inst_reach_state             false
% 3.03/0.83  --bmc1_out_unsat_core                   false
% 3.03/0.83  --bmc1_aig_witness_out                  false
% 3.03/0.83  --bmc1_verbose                          false
% 3.03/0.83  --bmc1_dump_clauses_tptp                false
% 3.03/0.83  --bmc1_dump_unsat_core_tptp             false
% 3.03/0.83  --bmc1_dump_file                        -
% 3.03/0.83  --bmc1_ucm_expand_uc_limit              128
% 3.03/0.83  --bmc1_ucm_n_expand_iterations          6
% 3.03/0.83  --bmc1_ucm_extend_mode                  1
% 3.03/0.83  --bmc1_ucm_init_mode                    2
% 3.03/0.83  --bmc1_ucm_cone_mode                    none
% 3.03/0.83  --bmc1_ucm_reduced_relation_type        0
% 3.03/0.83  --bmc1_ucm_relax_model                  4
% 3.03/0.83  --bmc1_ucm_full_tr_after_sat            true
% 3.03/0.83  --bmc1_ucm_expand_neg_assumptions       false
% 3.03/0.83  --bmc1_ucm_layered_model                none
% 3.03/0.83  --bmc1_ucm_max_lemma_size               10
% 3.03/0.83  
% 3.03/0.83  ------ AIG Options
% 3.03/0.83  
% 3.03/0.83  --aig_mode                              false
% 3.03/0.83  
% 3.03/0.83  ------ Instantiation Options
% 3.03/0.83  
% 3.03/0.83  --instantiation_flag                    true
% 3.03/0.83  --inst_sos_flag                         false
% 3.03/0.83  --inst_sos_phase                        true
% 3.03/0.83  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.03/0.83  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.03/0.83  --inst_lit_sel_side                     none
% 3.03/0.83  --inst_solver_per_active                1400
% 3.03/0.83  --inst_solver_calls_frac                1.
% 3.03/0.83  --inst_passive_queue_type               priority_queues
% 3.03/0.83  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.03/0.83  --inst_passive_queues_freq              [25;2]
% 3.03/0.83  --inst_dismatching                      true
% 3.03/0.83  --inst_eager_unprocessed_to_passive     true
% 3.03/0.83  --inst_prop_sim_given                   true
% 3.03/0.83  --inst_prop_sim_new                     false
% 3.03/0.83  --inst_subs_new                         false
% 3.03/0.83  --inst_eq_res_simp                      false
% 3.03/0.83  --inst_subs_given                       false
% 3.03/0.83  --inst_orphan_elimination               true
% 3.03/0.83  --inst_learning_loop_flag               true
% 3.03/0.83  --inst_learning_start                   3000
% 3.03/0.83  --inst_learning_factor                  2
% 3.03/0.83  --inst_start_prop_sim_after_learn       3
% 3.03/0.83  --inst_sel_renew                        solver
% 3.03/0.83  --inst_lit_activity_flag                true
% 3.03/0.83  --inst_restr_to_given                   false
% 3.03/0.83  --inst_activity_threshold               500
% 3.03/0.83  --inst_out_proof                        true
% 3.03/0.83  
% 3.03/0.83  ------ Resolution Options
% 3.03/0.83  
% 3.03/0.83  --resolution_flag                       false
% 3.03/0.83  --res_lit_sel                           adaptive
% 3.03/0.83  --res_lit_sel_side                      none
% 3.03/0.83  --res_ordering                          kbo
% 3.03/0.83  --res_to_prop_solver                    active
% 3.03/0.83  --res_prop_simpl_new                    false
% 3.03/0.83  --res_prop_simpl_given                  true
% 3.03/0.83  --res_passive_queue_type                priority_queues
% 3.03/0.83  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.03/0.83  --res_passive_queues_freq               [15;5]
% 3.03/0.83  --res_forward_subs                      full
% 3.03/0.83  --res_backward_subs                     full
% 3.03/0.83  --res_forward_subs_resolution           true
% 3.03/0.83  --res_backward_subs_resolution          true
% 3.03/0.83  --res_orphan_elimination                true
% 3.03/0.83  --res_time_limit                        2.
% 3.03/0.83  --res_out_proof                         true
% 3.03/0.83  
% 3.03/0.83  ------ Superposition Options
% 3.03/0.83  
% 3.03/0.83  --superposition_flag                    true
% 3.03/0.83  --sup_passive_queue_type                priority_queues
% 3.03/0.83  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.03/0.83  --sup_passive_queues_freq               [8;1;4]
% 3.03/0.83  --demod_completeness_check              fast
% 3.03/0.83  --demod_use_ground                      true
% 3.03/0.83  --sup_to_prop_solver                    passive
% 3.03/0.83  --sup_prop_simpl_new                    true
% 3.03/0.83  --sup_prop_simpl_given                  true
% 3.03/0.83  --sup_fun_splitting                     false
% 3.03/0.83  --sup_smt_interval                      50000
% 3.03/0.83  
% 3.03/0.83  ------ Superposition Simplification Setup
% 3.03/0.83  
% 3.03/0.83  --sup_indices_passive                   []
% 3.03/0.83  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/0.83  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/0.83  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/0.83  --sup_full_triv                         [TrivRules;PropSubs]
% 3.03/0.83  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/0.83  --sup_full_bw                           [BwDemod]
% 3.03/0.83  --sup_immed_triv                        [TrivRules]
% 3.03/0.83  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.03/0.83  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/0.83  --sup_immed_bw_main                     []
% 3.03/0.83  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/0.83  --sup_input_triv                        [Unflattening;TrivRules]
% 3.03/0.83  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/0.83  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/0.83  
% 3.03/0.83  ------ Combination Options
% 3.03/0.83  
% 3.03/0.83  --comb_res_mult                         3
% 3.03/0.83  --comb_sup_mult                         2
% 3.03/0.83  --comb_inst_mult                        10
% 3.03/0.83  
% 3.03/0.83  ------ Debug Options
% 3.03/0.83  
% 3.03/0.83  --dbg_backtrace                         false
% 3.03/0.83  --dbg_dump_prop_clauses                 false
% 3.03/0.83  --dbg_dump_prop_clauses_file            -
% 3.03/0.83  --dbg_out_stat                          false
% 3.03/0.83  
% 3.03/0.83  
% 3.03/0.83  
% 3.03/0.83  
% 3.03/0.83  ------ Proving...
% 3.03/0.83  
% 3.03/0.83  
% 3.03/0.83  % SZS status Theorem for theBenchmark.p
% 3.03/0.83  
% 3.03/0.83  % SZS output start CNFRefutation for theBenchmark.p
% 3.03/0.83  
% 3.03/0.83  fof(f19,conjecture,(
% 3.03/0.83    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 3.03/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/0.83  
% 3.03/0.83  fof(f20,negated_conjecture,(
% 3.03/0.83    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 3.03/0.83    inference(negated_conjecture,[],[f19])).
% 3.03/0.83  
% 3.03/0.83  fof(f41,plain,(
% 3.03/0.83    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1) | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.03/0.83    inference(ennf_transformation,[],[f20])).
% 3.03/0.83  
% 3.03/0.83  fof(f45,plain,(
% 3.03/0.83    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1) | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 3.03/0.83    introduced(choice_axiom,[])).
% 3.03/0.83  
% 3.03/0.83  fof(f46,plain,(
% 3.03/0.83    (k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.03/0.83    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f45])).
% 3.03/0.83  
% 3.03/0.83  fof(f68,plain,(
% 3.03/0.83    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.03/0.83    inference(cnf_transformation,[],[f46])).
% 3.03/0.83  
% 3.03/0.83  fof(f16,axiom,(
% 3.03/0.83    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.03/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/0.83  
% 3.03/0.83  fof(f38,plain,(
% 3.03/0.83    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.03/0.83    inference(ennf_transformation,[],[f16])).
% 3.03/0.83  
% 3.03/0.83  fof(f65,plain,(
% 3.03/0.83    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.03/0.83    inference(cnf_transformation,[],[f38])).
% 3.03/0.83  
% 3.03/0.83  fof(f14,axiom,(
% 3.03/0.83    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 3.03/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/0.83  
% 3.03/0.83  fof(f36,plain,(
% 3.03/0.83    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.03/0.83    inference(ennf_transformation,[],[f14])).
% 3.03/0.83  
% 3.03/0.83  fof(f63,plain,(
% 3.03/0.83    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.03/0.83    inference(cnf_transformation,[],[f36])).
% 3.03/0.83  
% 3.03/0.83  fof(f3,axiom,(
% 3.03/0.83    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.03/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/0.83  
% 3.03/0.83  fof(f44,plain,(
% 3.03/0.83    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.03/0.83    inference(nnf_transformation,[],[f3])).
% 3.03/0.83  
% 3.03/0.83  fof(f51,plain,(
% 3.03/0.83    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.03/0.83    inference(cnf_transformation,[],[f44])).
% 3.03/0.83  
% 3.03/0.83  fof(f12,axiom,(
% 3.03/0.83    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.03/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/0.83  
% 3.03/0.83  fof(f34,plain,(
% 3.03/0.83    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.03/0.83    inference(ennf_transformation,[],[f12])).
% 3.03/0.83  
% 3.03/0.83  fof(f61,plain,(
% 3.03/0.83    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.03/0.83    inference(cnf_transformation,[],[f34])).
% 3.03/0.83  
% 3.03/0.83  fof(f9,axiom,(
% 3.03/0.83    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 3.03/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/0.83  
% 3.03/0.83  fof(f29,plain,(
% 3.03/0.83    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.03/0.83    inference(ennf_transformation,[],[f9])).
% 3.03/0.83  
% 3.03/0.83  fof(f58,plain,(
% 3.03/0.83    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.03/0.83    inference(cnf_transformation,[],[f29])).
% 3.03/0.83  
% 3.03/0.83  fof(f10,axiom,(
% 3.03/0.83    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 3.03/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/0.83  
% 3.03/0.83  fof(f30,plain,(
% 3.03/0.83    ! [X0,X1,X2] : ((r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 3.03/0.83    inference(ennf_transformation,[],[f10])).
% 3.03/0.83  
% 3.03/0.83  fof(f31,plain,(
% 3.03/0.83    ! [X0,X1,X2] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 3.03/0.83    inference(flattening,[],[f30])).
% 3.03/0.83  
% 3.03/0.83  fof(f59,plain,(
% 3.03/0.83    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 3.03/0.83    inference(cnf_transformation,[],[f31])).
% 3.03/0.83  
% 3.03/0.83  fof(f1,axiom,(
% 3.03/0.83    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.03/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/0.83  
% 3.03/0.83  fof(f42,plain,(
% 3.03/0.83    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.03/0.83    inference(nnf_transformation,[],[f1])).
% 3.03/0.83  
% 3.03/0.83  fof(f43,plain,(
% 3.03/0.83    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.03/0.83    inference(flattening,[],[f42])).
% 3.03/0.83  
% 3.03/0.83  fof(f49,plain,(
% 3.03/0.83    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.03/0.83    inference(cnf_transformation,[],[f43])).
% 3.03/0.83  
% 3.03/0.83  fof(f8,axiom,(
% 3.03/0.83    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 3.03/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/0.83  
% 3.03/0.83  fof(f28,plain,(
% 3.03/0.83    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.03/0.83    inference(ennf_transformation,[],[f8])).
% 3.03/0.83  
% 3.03/0.83  fof(f57,plain,(
% 3.03/0.83    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.03/0.83    inference(cnf_transformation,[],[f28])).
% 3.03/0.83  
% 3.03/0.83  fof(f5,axiom,(
% 3.03/0.83    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 3.03/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/0.83  
% 3.03/0.83  fof(f24,plain,(
% 3.03/0.83    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 3.03/0.83    inference(ennf_transformation,[],[f5])).
% 3.03/0.83  
% 3.03/0.83  fof(f54,plain,(
% 3.03/0.83    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.03/0.83    inference(cnf_transformation,[],[f24])).
% 3.03/0.83  
% 3.03/0.83  fof(f7,axiom,(
% 3.03/0.83    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 3.03/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/0.83  
% 3.03/0.83  fof(f26,plain,(
% 3.03/0.83    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 3.03/0.83    inference(ennf_transformation,[],[f7])).
% 3.03/0.83  
% 3.03/0.83  fof(f27,plain,(
% 3.03/0.83    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 3.03/0.83    inference(flattening,[],[f26])).
% 3.03/0.83  
% 3.03/0.83  fof(f56,plain,(
% 3.03/0.83    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 3.03/0.83    inference(cnf_transformation,[],[f27])).
% 3.03/0.83  
% 3.03/0.83  fof(f15,axiom,(
% 3.03/0.83    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.03/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/0.83  
% 3.03/0.83  fof(f37,plain,(
% 3.03/0.83    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.03/0.83    inference(ennf_transformation,[],[f15])).
% 3.03/0.83  
% 3.03/0.83  fof(f64,plain,(
% 3.03/0.83    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.03/0.83    inference(cnf_transformation,[],[f37])).
% 3.03/0.83  
% 3.03/0.83  fof(f13,axiom,(
% 3.03/0.83    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.03/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/0.83  
% 3.03/0.83  fof(f35,plain,(
% 3.03/0.83    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.03/0.83    inference(ennf_transformation,[],[f13])).
% 3.03/0.83  
% 3.03/0.83  fof(f62,plain,(
% 3.03/0.83    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.03/0.83    inference(cnf_transformation,[],[f35])).
% 3.03/0.83  
% 3.03/0.83  fof(f69,plain,(
% 3.03/0.83    k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)),
% 3.03/0.83    inference(cnf_transformation,[],[f46])).
% 3.03/0.83  
% 3.03/0.83  fof(f18,axiom,(
% 3.03/0.83    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 3.03/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/0.83  
% 3.03/0.83  fof(f40,plain,(
% 3.03/0.83    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.03/0.83    inference(ennf_transformation,[],[f18])).
% 3.03/0.83  
% 3.03/0.83  fof(f67,plain,(
% 3.03/0.83    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.03/0.83    inference(cnf_transformation,[],[f40])).
% 3.03/0.83  
% 3.03/0.83  fof(f17,axiom,(
% 3.03/0.83    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.03/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/0.83  
% 3.03/0.83  fof(f39,plain,(
% 3.03/0.83    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.03/0.83    inference(ennf_transformation,[],[f17])).
% 3.03/0.83  
% 3.03/0.83  fof(f66,plain,(
% 3.03/0.83    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.03/0.83    inference(cnf_transformation,[],[f39])).
% 3.03/0.83  
% 3.03/0.83  fof(f6,axiom,(
% 3.03/0.83    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))))),
% 3.03/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/0.83  
% 3.03/0.83  fof(f25,plain,(
% 3.03/0.83    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.03/0.83    inference(ennf_transformation,[],[f6])).
% 3.03/0.83  
% 3.03/0.83  fof(f55,plain,(
% 3.03/0.83    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 3.03/0.83    inference(cnf_transformation,[],[f25])).
% 3.03/0.83  
% 3.03/0.83  cnf(c_22,negated_conjecture,
% 3.03/0.83      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.03/0.83      inference(cnf_transformation,[],[f68]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_970,plain,
% 3.03/0.83      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.03/0.83      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_18,plain,
% 3.03/0.83      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/0.83      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.03/0.83      inference(cnf_transformation,[],[f65]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_973,plain,
% 3.03/0.83      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.03/0.83      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.03/0.83      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_1526,plain,
% 3.03/0.83      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.03/0.83      inference(superposition,[status(thm)],[c_970,c_973]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_16,plain,
% 3.03/0.83      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/0.83      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 3.03/0.83      inference(cnf_transformation,[],[f63]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_975,plain,
% 3.03/0.83      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.03/0.83      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 3.03/0.83      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_1637,plain,
% 3.03/0.83      ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top
% 3.03/0.83      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 3.03/0.83      inference(superposition,[status(thm)],[c_1526,c_975]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_23,plain,
% 3.03/0.83      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.03/0.83      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_1795,plain,
% 3.03/0.83      ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top ),
% 3.03/0.83      inference(global_propositional_subsumption,
% 3.03/0.83                [status(thm)],
% 3.03/0.83                [c_1637,c_23]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_5,plain,
% 3.03/0.83      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.03/0.83      inference(cnf_transformation,[],[f51]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_984,plain,
% 3.03/0.83      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.03/0.83      | r1_tarski(X0,X1) = iProver_top ),
% 3.03/0.83      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_1800,plain,
% 3.03/0.83      ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
% 3.03/0.83      inference(superposition,[status(thm)],[c_1795,c_984]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_14,plain,
% 3.03/0.83      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/0.83      | v1_relat_1(X0) ),
% 3.03/0.83      inference(cnf_transformation,[],[f61]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_977,plain,
% 3.03/0.83      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.03/0.83      | v1_relat_1(X0) = iProver_top ),
% 3.03/0.83      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_1342,plain,
% 3.03/0.83      ( v1_relat_1(sK2) = iProver_top ),
% 3.03/0.83      inference(superposition,[status(thm)],[c_970,c_977]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_11,plain,
% 3.03/0.83      ( ~ v1_relat_1(X0)
% 3.03/0.83      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 3.03/0.83      inference(cnf_transformation,[],[f58]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_979,plain,
% 3.03/0.83      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 3.03/0.83      | v1_relat_1(X0) != iProver_top ),
% 3.03/0.83      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_1546,plain,
% 3.03/0.83      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 3.03/0.83      inference(superposition,[status(thm)],[c_1342,c_979]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_12,plain,
% 3.03/0.83      ( ~ r1_tarski(X0,X1)
% 3.03/0.83      | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
% 3.03/0.83      | ~ v1_relat_1(X2) ),
% 3.03/0.83      inference(cnf_transformation,[],[f59]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_978,plain,
% 3.03/0.83      ( r1_tarski(X0,X1) != iProver_top
% 3.03/0.83      | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = iProver_top
% 3.03/0.83      | v1_relat_1(X2) != iProver_top ),
% 3.03/0.83      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_3073,plain,
% 3.03/0.83      ( r1_tarski(k2_relat_1(sK2),X0) != iProver_top
% 3.03/0.83      | r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X0)) = iProver_top
% 3.03/0.83      | v1_relat_1(sK2) != iProver_top ),
% 3.03/0.83      inference(superposition,[status(thm)],[c_1546,c_978]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_1134,plain,
% 3.03/0.83      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.03/0.83      | v1_relat_1(sK2) ),
% 3.03/0.83      inference(instantiation,[status(thm)],[c_14]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_1135,plain,
% 3.03/0.83      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.03/0.83      | v1_relat_1(sK2) = iProver_top ),
% 3.03/0.83      inference(predicate_to_equality,[status(thm)],[c_1134]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_3218,plain,
% 3.03/0.83      ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X0)) = iProver_top
% 3.03/0.83      | r1_tarski(k2_relat_1(sK2),X0) != iProver_top ),
% 3.03/0.83      inference(global_propositional_subsumption,
% 3.03/0.83                [status(thm)],
% 3.03/0.83                [c_3073,c_23,c_1135]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_3219,plain,
% 3.03/0.83      ( r1_tarski(k2_relat_1(sK2),X0) != iProver_top
% 3.03/0.83      | r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X0)) = iProver_top ),
% 3.03/0.83      inference(renaming,[status(thm)],[c_3218]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_0,plain,
% 3.03/0.83      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.03/0.83      inference(cnf_transformation,[],[f49]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_988,plain,
% 3.03/0.83      ( X0 = X1
% 3.03/0.83      | r1_tarski(X0,X1) != iProver_top
% 3.03/0.83      | r1_tarski(X1,X0) != iProver_top ),
% 3.03/0.83      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_3228,plain,
% 3.03/0.83      ( k10_relat_1(sK2,X0) = k1_relat_1(sK2)
% 3.03/0.83      | r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2)) != iProver_top
% 3.03/0.83      | r1_tarski(k2_relat_1(sK2),X0) != iProver_top ),
% 3.03/0.83      inference(superposition,[status(thm)],[c_3219,c_988]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_10,plain,
% 3.03/0.83      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 3.03/0.83      inference(cnf_transformation,[],[f57]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_1194,plain,
% 3.03/0.83      ( r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2))
% 3.03/0.83      | ~ v1_relat_1(sK2) ),
% 3.03/0.83      inference(instantiation,[status(thm)],[c_10]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_1201,plain,
% 3.03/0.83      ( r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2)) = iProver_top
% 3.03/0.83      | v1_relat_1(sK2) != iProver_top ),
% 3.03/0.83      inference(predicate_to_equality,[status(thm)],[c_1194]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_6019,plain,
% 3.03/0.83      ( k10_relat_1(sK2,X0) = k1_relat_1(sK2)
% 3.03/0.83      | r1_tarski(k2_relat_1(sK2),X0) != iProver_top ),
% 3.03/0.83      inference(global_propositional_subsumption,
% 3.03/0.83                [status(thm)],
% 3.03/0.83                [c_3228,c_23,c_1135,c_1201]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_6029,plain,
% 3.03/0.83      ( k10_relat_1(sK2,sK1) = k1_relat_1(sK2) ),
% 3.03/0.83      inference(superposition,[status(thm)],[c_1800,c_6019]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_7,plain,
% 3.03/0.83      ( ~ v1_relat_1(X0)
% 3.03/0.83      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 3.03/0.83      inference(cnf_transformation,[],[f54]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_983,plain,
% 3.03/0.83      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 3.03/0.83      | v1_relat_1(X0) != iProver_top ),
% 3.03/0.83      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_1545,plain,
% 3.03/0.83      ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
% 3.03/0.83      inference(superposition,[status(thm)],[c_1342,c_983]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_9,plain,
% 3.03/0.83      ( ~ r1_tarski(X0,X1)
% 3.03/0.83      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 3.03/0.83      | ~ v1_relat_1(X2) ),
% 3.03/0.83      inference(cnf_transformation,[],[f56]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_981,plain,
% 3.03/0.83      ( r1_tarski(X0,X1) != iProver_top
% 3.03/0.83      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = iProver_top
% 3.03/0.83      | v1_relat_1(X2) != iProver_top ),
% 3.03/0.83      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_3113,plain,
% 3.03/0.83      ( r1_tarski(k2_relat_1(sK2),k9_relat_1(sK2,X0)) = iProver_top
% 3.03/0.83      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 3.03/0.83      | v1_relat_1(sK2) != iProver_top ),
% 3.03/0.83      inference(superposition,[status(thm)],[c_1545,c_981]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_3140,plain,
% 3.03/0.83      ( r1_tarski(k2_relat_1(sK2),k9_relat_1(sK2,sK0)) = iProver_top
% 3.03/0.83      | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top
% 3.03/0.83      | v1_relat_1(sK2) != iProver_top ),
% 3.03/0.83      inference(instantiation,[status(thm)],[c_3113]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_17,plain,
% 3.03/0.83      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/0.83      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.03/0.83      inference(cnf_transformation,[],[f64]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_974,plain,
% 3.03/0.83      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.03/0.83      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.03/0.83      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_2006,plain,
% 3.03/0.83      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 3.03/0.83      inference(superposition,[status(thm)],[c_970,c_974]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_15,plain,
% 3.03/0.83      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/0.83      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 3.03/0.83      inference(cnf_transformation,[],[f62]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_976,plain,
% 3.03/0.83      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.03/0.83      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.03/0.83      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_2286,plain,
% 3.03/0.83      ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) = iProver_top
% 3.03/0.83      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 3.03/0.83      inference(superposition,[status(thm)],[c_2006,c_976]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_2612,plain,
% 3.03/0.83      ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) = iProver_top ),
% 3.03/0.83      inference(global_propositional_subsumption,
% 3.03/0.83                [status(thm)],
% 3.03/0.83                [c_2286,c_23]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_2617,plain,
% 3.03/0.83      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 3.03/0.83      inference(superposition,[status(thm)],[c_2612,c_984]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_21,negated_conjecture,
% 3.03/0.83      ( k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)
% 3.03/0.83      | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) ),
% 3.03/0.83      inference(cnf_transformation,[],[f69]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_1636,plain,
% 3.03/0.83      ( k8_relset_1(sK0,sK1,sK2,sK1) != k1_relset_1(sK0,sK1,sK2)
% 3.03/0.83      | k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2) ),
% 3.03/0.83      inference(demodulation,[status(thm)],[c_1526,c_21]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_2285,plain,
% 3.03/0.83      ( k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2)
% 3.03/0.83      | k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2) ),
% 3.03/0.83      inference(demodulation,[status(thm)],[c_2006,c_1636]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_20,plain,
% 3.03/0.83      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/0.83      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 3.03/0.83      inference(cnf_transformation,[],[f67]) ).
% 3.03/0.83  
% 3.03/0.83  cnf(c_971,plain,
% 3.03/0.83      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 3.03/0.83      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.03/0.83      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.03/0.84  
% 3.03/0.84  cnf(c_2130,plain,
% 3.03/0.84      ( k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
% 3.03/0.84      inference(superposition,[status(thm)],[c_970,c_971]) ).
% 3.03/0.84  
% 3.03/0.84  cnf(c_19,plain,
% 3.03/0.84      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/0.84      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.03/0.84      inference(cnf_transformation,[],[f66]) ).
% 3.03/0.84  
% 3.03/0.84  cnf(c_972,plain,
% 3.03/0.84      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.03/0.84      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.03/0.84      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.03/0.84  
% 3.03/0.84  cnf(c_2161,plain,
% 3.03/0.84      ( k7_relset_1(sK0,sK1,sK2,X0) = k9_relat_1(sK2,X0) ),
% 3.03/0.84      inference(superposition,[status(thm)],[c_970,c_972]) ).
% 3.03/0.84  
% 3.03/0.84  cnf(c_2495,plain,
% 3.03/0.84      ( k10_relat_1(sK2,sK1) != k1_relat_1(sK2)
% 3.03/0.84      | k9_relat_1(sK2,sK0) != k2_relat_1(sK2) ),
% 3.03/0.84      inference(demodulation,[status(thm)],[c_2285,c_2130,c_2161]) ).
% 3.03/0.84  
% 3.03/0.84  cnf(c_8,plain,
% 3.03/0.84      ( r1_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,k1_relat_1(X0)))
% 3.03/0.84      | ~ v1_relat_1(X0) ),
% 3.03/0.84      inference(cnf_transformation,[],[f55]) ).
% 3.03/0.84  
% 3.03/0.84  cnf(c_982,plain,
% 3.03/0.84      ( r1_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,k1_relat_1(X0))) = iProver_top
% 3.03/0.84      | v1_relat_1(X0) != iProver_top ),
% 3.03/0.84      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.03/0.84  
% 3.03/0.84  cnf(c_1720,plain,
% 3.03/0.84      ( r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(sK2)) = iProver_top
% 3.03/0.84      | v1_relat_1(sK2) != iProver_top ),
% 3.03/0.84      inference(superposition,[status(thm)],[c_1545,c_982]) ).
% 3.03/0.84  
% 3.03/0.84  cnf(c_1889,plain,
% 3.03/0.84      ( r1_tarski(k9_relat_1(sK2,X0),k2_relat_1(sK2)) = iProver_top ),
% 3.03/0.84      inference(global_propositional_subsumption,
% 3.03/0.84                [status(thm)],
% 3.03/0.84                [c_1720,c_23,c_1135]) ).
% 3.03/0.84  
% 3.03/0.84  cnf(c_2038,plain,
% 3.03/0.84      ( k9_relat_1(sK2,X0) = k2_relat_1(sK2)
% 3.03/0.84      | r1_tarski(k2_relat_1(sK2),k9_relat_1(sK2,X0)) != iProver_top ),
% 3.03/0.84      inference(superposition,[status(thm)],[c_1889,c_988]) ).
% 3.03/0.84  
% 3.03/0.84  cnf(c_2072,plain,
% 3.03/0.84      ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2)
% 3.03/0.84      | r1_tarski(k2_relat_1(sK2),k9_relat_1(sK2,sK0)) != iProver_top ),
% 3.03/0.84      inference(instantiation,[status(thm)],[c_2038]) ).
% 3.03/0.84  
% 3.03/0.84  cnf(contradiction,plain,
% 3.03/0.84      ( $false ),
% 3.03/0.84      inference(minisat,
% 3.03/0.84                [status(thm)],
% 3.03/0.84                [c_6029,c_3140,c_2617,c_2495,c_2072,c_1135,c_23]) ).
% 3.03/0.84  
% 3.03/0.84  
% 3.03/0.84  % SZS output end CNFRefutation for theBenchmark.p
% 3.03/0.84  
% 3.03/0.84  ------                               Statistics
% 3.03/0.84  
% 3.03/0.84  ------ General
% 3.03/0.84  
% 3.03/0.84  abstr_ref_over_cycles:                  0
% 3.03/0.84  abstr_ref_under_cycles:                 0
% 3.03/0.84  gc_basic_clause_elim:                   0
% 3.03/0.84  forced_gc_time:                         0
% 3.03/0.84  parsing_time:                           0.009
% 3.03/0.84  unif_index_cands_time:                  0.
% 3.03/0.84  unif_index_add_time:                    0.
% 3.03/0.84  orderings_time:                         0.
% 3.03/0.84  out_proof_time:                         0.01
% 3.03/0.84  total_time:                             0.175
% 3.03/0.84  num_of_symbols:                         47
% 3.03/0.84  num_of_terms:                           4319
% 3.03/0.84  
% 3.03/0.84  ------ Preprocessing
% 3.03/0.84  
% 3.03/0.84  num_of_splits:                          0
% 3.03/0.84  num_of_split_atoms:                     0
% 3.03/0.84  num_of_reused_defs:                     0
% 3.03/0.84  num_eq_ax_congr_red:                    15
% 3.03/0.84  num_of_sem_filtered_clauses:            1
% 3.03/0.84  num_of_subtypes:                        0
% 3.03/0.84  monotx_restored_types:                  0
% 3.03/0.84  sat_num_of_epr_types:                   0
% 3.03/0.84  sat_num_of_non_cyclic_types:            0
% 3.03/0.84  sat_guarded_non_collapsed_types:        0
% 3.03/0.84  num_pure_diseq_elim:                    0
% 3.03/0.84  simp_replaced_by:                       0
% 3.03/0.84  res_preprocessed:                       113
% 3.03/0.84  prep_upred:                             0
% 3.03/0.84  prep_unflattend:                        0
% 3.03/0.84  smt_new_axioms:                         0
% 3.03/0.84  pred_elim_cands:                        3
% 3.03/0.84  pred_elim:                              0
% 3.03/0.84  pred_elim_cl:                           0
% 3.03/0.84  pred_elim_cycles:                       2
% 3.03/0.84  merged_defs:                            8
% 3.03/0.84  merged_defs_ncl:                        0
% 3.03/0.84  bin_hyper_res:                          9
% 3.03/0.84  prep_cycles:                            4
% 3.03/0.84  pred_elim_time:                         0.
% 3.03/0.84  splitting_time:                         0.
% 3.03/0.84  sem_filter_time:                        0.
% 3.03/0.84  monotx_time:                            0.
% 3.03/0.84  subtype_inf_time:                       0.
% 3.03/0.84  
% 3.03/0.84  ------ Problem properties
% 3.03/0.84  
% 3.03/0.84  clauses:                                22
% 3.03/0.84  conjectures:                            2
% 3.03/0.84  epr:                                    4
% 3.03/0.84  horn:                                   22
% 3.03/0.84  ground:                                 2
% 3.03/0.84  unary:                                  2
% 3.03/0.84  binary:                                 14
% 3.03/0.84  lits:                                   48
% 3.03/0.84  lits_eq:                                9
% 3.03/0.84  fd_pure:                                0
% 3.03/0.84  fd_pseudo:                              0
% 3.03/0.84  fd_cond:                                0
% 3.03/0.84  fd_pseudo_cond:                         1
% 3.03/0.84  ac_symbols:                             0
% 3.03/0.84  
% 3.03/0.84  ------ Propositional Solver
% 3.03/0.84  
% 3.03/0.84  prop_solver_calls:                      30
% 3.03/0.84  prop_fast_solver_calls:                 712
% 3.03/0.84  smt_solver_calls:                       0
% 3.03/0.84  smt_fast_solver_calls:                  0
% 3.03/0.84  prop_num_of_clauses:                    2142
% 3.03/0.84  prop_preprocess_simplified:             6101
% 3.03/0.84  prop_fo_subsumed:                       7
% 3.03/0.84  prop_solver_time:                       0.
% 3.03/0.84  smt_solver_time:                        0.
% 3.03/0.84  smt_fast_solver_time:                   0.
% 3.03/0.84  prop_fast_solver_time:                  0.
% 3.03/0.84  prop_unsat_core_time:                   0.
% 3.03/0.84  
% 3.03/0.84  ------ QBF
% 3.03/0.84  
% 3.03/0.84  qbf_q_res:                              0
% 3.03/0.84  qbf_num_tautologies:                    0
% 3.03/0.84  qbf_prep_cycles:                        0
% 3.03/0.84  
% 3.03/0.84  ------ BMC1
% 3.03/0.84  
% 3.03/0.84  bmc1_current_bound:                     -1
% 3.03/0.84  bmc1_last_solved_bound:                 -1
% 3.03/0.84  bmc1_unsat_core_size:                   -1
% 3.03/0.84  bmc1_unsat_core_parents_size:           -1
% 3.03/0.84  bmc1_merge_next_fun:                    0
% 3.03/0.84  bmc1_unsat_core_clauses_time:           0.
% 3.03/0.84  
% 3.03/0.84  ------ Instantiation
% 3.03/0.84  
% 3.03/0.84  inst_num_of_clauses:                    623
% 3.03/0.84  inst_num_in_passive:                    227
% 3.03/0.84  inst_num_in_active:                     373
% 3.03/0.84  inst_num_in_unprocessed:                23
% 3.03/0.84  inst_num_of_loops:                      400
% 3.03/0.84  inst_num_of_learning_restarts:          0
% 3.03/0.84  inst_num_moves_active_passive:          23
% 3.03/0.84  inst_lit_activity:                      0
% 3.03/0.84  inst_lit_activity_moves:                0
% 3.03/0.84  inst_num_tautologies:                   0
% 3.03/0.84  inst_num_prop_implied:                  0
% 3.03/0.84  inst_num_existing_simplified:           0
% 3.03/0.84  inst_num_eq_res_simplified:             0
% 3.03/0.84  inst_num_child_elim:                    0
% 3.03/0.84  inst_num_of_dismatching_blockings:      288
% 3.03/0.84  inst_num_of_non_proper_insts:           1097
% 3.03/0.84  inst_num_of_duplicates:                 0
% 3.03/0.84  inst_inst_num_from_inst_to_res:         0
% 3.03/0.84  inst_dismatching_checking_time:         0.
% 3.03/0.84  
% 3.03/0.84  ------ Resolution
% 3.03/0.84  
% 3.03/0.84  res_num_of_clauses:                     0
% 3.03/0.84  res_num_in_passive:                     0
% 3.03/0.84  res_num_in_active:                      0
% 3.03/0.84  res_num_of_loops:                       117
% 3.03/0.84  res_forward_subset_subsumed:            94
% 3.03/0.84  res_backward_subset_subsumed:           4
% 3.03/0.84  res_forward_subsumed:                   0
% 3.03/0.84  res_backward_subsumed:                  0
% 3.03/0.84  res_forward_subsumption_resolution:     0
% 3.03/0.84  res_backward_subsumption_resolution:    0
% 3.03/0.84  res_clause_to_clause_subsumption:       472
% 3.03/0.84  res_orphan_elimination:                 0
% 3.03/0.84  res_tautology_del:                      149
% 3.03/0.84  res_num_eq_res_simplified:              0
% 3.03/0.84  res_num_sel_changes:                    0
% 3.03/0.84  res_moves_from_active_to_pass:          0
% 3.03/0.84  
% 3.03/0.84  ------ Superposition
% 3.03/0.84  
% 3.03/0.84  sup_time_total:                         0.
% 3.03/0.84  sup_time_generating:                    0.
% 3.03/0.84  sup_time_sim_full:                      0.
% 3.03/0.84  sup_time_sim_immed:                     0.
% 3.03/0.84  
% 3.03/0.84  sup_num_of_clauses:                     152
% 3.03/0.84  sup_num_in_active:                      77
% 3.03/0.84  sup_num_in_passive:                     75
% 3.03/0.84  sup_num_of_loops:                       79
% 3.03/0.84  sup_fw_superposition:                   136
% 3.03/0.84  sup_bw_superposition:                   60
% 3.03/0.84  sup_immediate_simplified:               37
% 3.03/0.84  sup_given_eliminated:                   0
% 3.03/0.84  comparisons_done:                       0
% 3.03/0.84  comparisons_avoided:                    0
% 3.03/0.84  
% 3.03/0.84  ------ Simplifications
% 3.03/0.84  
% 3.03/0.84  
% 3.03/0.84  sim_fw_subset_subsumed:                 7
% 3.03/0.84  sim_bw_subset_subsumed:                 0
% 3.03/0.84  sim_fw_subsumed:                        14
% 3.03/0.84  sim_bw_subsumed:                        1
% 3.03/0.84  sim_fw_subsumption_res:                 0
% 3.03/0.84  sim_bw_subsumption_res:                 0
% 3.03/0.84  sim_tautology_del:                      20
% 3.03/0.84  sim_eq_tautology_del:                   8
% 3.03/0.84  sim_eq_res_simp:                        1
% 3.03/0.84  sim_fw_demodulated:                     1
% 3.03/0.84  sim_bw_demodulated:                     3
% 3.03/0.84  sim_light_normalised:                   18
% 3.03/0.84  sim_joinable_taut:                      0
% 3.03/0.84  sim_joinable_simp:                      0
% 3.03/0.84  sim_ac_normalised:                      0
% 3.03/0.84  sim_smt_subsumption:                    0
% 3.03/0.84  
%------------------------------------------------------------------------------
