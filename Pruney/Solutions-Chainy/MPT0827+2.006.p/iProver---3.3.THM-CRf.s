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
% DateTime   : Thu Dec  3 11:55:11 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 260 expanded)
%              Number of clauses        :   66 (  99 expanded)
%              Number of leaves         :   21 (  56 expanded)
%              Depth                    :   18
%              Number of atoms          :  261 ( 577 expanded)
%              Number of equality atoms :  118 ( 184 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f40,f46])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X2),X3)
       => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
          & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(k6_relat_1(X2),X3)
         => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
            & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f33,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
        | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      & r1_tarski(k6_relat_1(X2),X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f34,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
        | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      & r1_tarski(k6_relat_1(X2),X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f35,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
          | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
        & r1_tarski(k6_relat_1(X2),X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
        | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) )
      & r1_tarski(k6_relat_1(sK2),sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
      | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) )
    & r1_tarski(k6_relat_1(sK2),sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f34,f35])).

fof(f58,plain,(
    r1_tarski(k6_relat_1(sK2),sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f26])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f64,plain,(
    ! [X0,X1] : r1_xboole_0(k6_subset_1(X0,X1),X1) ),
    inference(definition_unfolding,[],[f43,f46])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f36])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f53,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f45,f44])).

fof(f61,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f38,f60])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f41,f60,f46])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f50,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f52,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f59,plain,
    ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
    | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f36])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_3,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_545,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(k6_relat_1(sK2),sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_539,plain,
    ( r1_tarski(k6_relat_1(sK2),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_546,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1677,plain,
    ( r1_tarski(X0,k6_relat_1(sK2)) != iProver_top
    | r1_tarski(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_539,c_546])).

cnf(c_2327,plain,
    ( r1_tarski(k6_subset_1(k6_relat_1(sK2),X0),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_545,c_1677])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_6,plain,
    ( r1_xboole_0(k6_subset_1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_188,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | X2 != X1
    | k6_subset_1(X3,X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_6])).

cnf(c_189,plain,
    ( ~ r1_tarski(k6_subset_1(X0,X1),X1)
    | v1_xboole_0(k6_subset_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_188])).

cnf(c_203,plain,
    ( ~ r1_tarski(k6_subset_1(X0,X1),X1)
    | k6_subset_1(X0,X1) != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_189])).

cnf(c_204,plain,
    ( ~ r1_tarski(k6_subset_1(X0,X1),X1)
    | k1_xboole_0 = k6_subset_1(X0,X1) ),
    inference(unflattening,[status(thm)],[c_203])).

cnf(c_538,plain,
    ( k1_xboole_0 = k6_subset_1(X0,X1)
    | r1_tarski(k6_subset_1(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_204])).

cnf(c_2340,plain,
    ( k6_subset_1(k6_relat_1(sK2),sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2327,c_538])).

cnf(c_7,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_543,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2398,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3)),k1_relat_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k6_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2340,c_543])).

cnf(c_10,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2416,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3)),k1_xboole_0) = iProver_top
    | v1_relat_1(k6_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2398,c_10])).

cnf(c_12,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2417,plain,
    ( r1_tarski(k6_subset_1(sK2,k1_relat_1(sK3)),k1_xboole_0) = iProver_top
    | v1_relat_1(k6_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2416,c_12])).

cnf(c_335,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_678,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_335])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_236,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_19])).

cnf(c_237,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_236])).

cnf(c_681,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_237])).

cnf(c_682,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_681])).

cnf(c_2941,plain,
    ( v1_relat_1(k6_relat_1(sK2)) != iProver_top
    | r1_tarski(k6_subset_1(sK2,k1_relat_1(sK3)),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2417,c_678,c_682])).

cnf(c_2942,plain,
    ( r1_tarski(k6_subset_1(sK2,k1_relat_1(sK3)),k1_xboole_0) = iProver_top
    | v1_relat_1(k6_relat_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2941])).

cnf(c_13,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_541,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2947,plain,
    ( r1_tarski(k6_subset_1(sK2,k1_relat_1(sK3)),k1_xboole_0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2942,c_541])).

cnf(c_1,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_4,plain,
    ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
    | ~ r1_tarski(k6_subset_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_544,plain,
    ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) = iProver_top
    | r1_tarski(k6_subset_1(X0,X1),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1447,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k6_subset_1(X0,X1),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_544])).

cnf(c_2950,plain,
    ( r1_tarski(sK2,k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2947,c_1447])).

cnf(c_8,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_542,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2399,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(k6_relat_1(sK2)),k2_relat_1(sK3)),k2_relat_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k6_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2340,c_542])).

cnf(c_9,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2408,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(k6_relat_1(sK2)),k2_relat_1(sK3)),k1_xboole_0) = iProver_top
    | v1_relat_1(k6_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2399,c_9])).

cnf(c_11,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2409,plain,
    ( r1_tarski(k6_subset_1(sK2,k2_relat_1(sK3)),k1_xboole_0) = iProver_top
    | v1_relat_1(k6_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2408,c_11])).

cnf(c_2918,plain,
    ( v1_relat_1(k6_relat_1(sK2)) != iProver_top
    | r1_tarski(k6_subset_1(sK2,k2_relat_1(sK3)),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2409,c_678,c_682])).

cnf(c_2919,plain,
    ( r1_tarski(k6_subset_1(sK2,k2_relat_1(sK3)),k1_xboole_0) = iProver_top
    | v1_relat_1(k6_relat_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2918])).

cnf(c_2924,plain,
    ( r1_tarski(k6_subset_1(sK2,k2_relat_1(sK3)),k1_xboole_0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2919,c_541])).

cnf(c_2927,plain,
    ( r1_tarski(sK2,k2_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2924,c_1447])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_218,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_19])).

cnf(c_219,plain,
    ( k2_relset_1(X0,X1,sK3) = k2_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_218])).

cnf(c_631,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(equality_resolution,[status(thm)],[c_219])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
    | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_540,plain,
    ( r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) != iProver_top
    | r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_692,plain,
    ( r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) != iProver_top
    | r1_tarski(sK2,k2_relat_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_631,c_540])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_227,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_19])).

cnf(c_228,plain,
    ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_227])).

cnf(c_674,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(equality_resolution,[status(thm)],[c_228])).

cnf(c_743,plain,
    ( r1_tarski(sK2,k2_relat_1(sK3)) != iProver_top
    | r1_tarski(sK2,k1_relat_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_692,c_674])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2950,c_2927,c_743])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:27:00 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.62/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.02  
% 2.62/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.62/1.02  
% 2.62/1.02  ------  iProver source info
% 2.62/1.02  
% 2.62/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.62/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.62/1.02  git: non_committed_changes: false
% 2.62/1.02  git: last_make_outside_of_git: false
% 2.62/1.02  
% 2.62/1.02  ------ 
% 2.62/1.02  
% 2.62/1.02  ------ Input Options
% 2.62/1.02  
% 2.62/1.02  --out_options                           all
% 2.62/1.02  --tptp_safe_out                         true
% 2.62/1.02  --problem_path                          ""
% 2.62/1.02  --include_path                          ""
% 2.62/1.02  --clausifier                            res/vclausify_rel
% 2.62/1.02  --clausifier_options                    --mode clausify
% 2.62/1.02  --stdin                                 false
% 2.62/1.02  --stats_out                             all
% 2.62/1.02  
% 2.62/1.02  ------ General Options
% 2.62/1.02  
% 2.62/1.02  --fof                                   false
% 2.62/1.02  --time_out_real                         305.
% 2.62/1.02  --time_out_virtual                      -1.
% 2.62/1.02  --symbol_type_check                     false
% 2.62/1.02  --clausify_out                          false
% 2.62/1.02  --sig_cnt_out                           false
% 2.62/1.02  --trig_cnt_out                          false
% 2.62/1.02  --trig_cnt_out_tolerance                1.
% 2.62/1.02  --trig_cnt_out_sk_spl                   false
% 2.62/1.02  --abstr_cl_out                          false
% 2.62/1.02  
% 2.62/1.02  ------ Global Options
% 2.62/1.02  
% 2.62/1.02  --schedule                              default
% 2.62/1.02  --add_important_lit                     false
% 2.62/1.02  --prop_solver_per_cl                    1000
% 2.62/1.02  --min_unsat_core                        false
% 2.62/1.02  --soft_assumptions                      false
% 2.62/1.02  --soft_lemma_size                       3
% 2.62/1.02  --prop_impl_unit_size                   0
% 2.62/1.02  --prop_impl_unit                        []
% 2.62/1.02  --share_sel_clauses                     true
% 2.62/1.02  --reset_solvers                         false
% 2.62/1.02  --bc_imp_inh                            [conj_cone]
% 2.62/1.02  --conj_cone_tolerance                   3.
% 2.62/1.02  --extra_neg_conj                        none
% 2.62/1.02  --large_theory_mode                     true
% 2.62/1.02  --prolific_symb_bound                   200
% 2.62/1.02  --lt_threshold                          2000
% 2.62/1.02  --clause_weak_htbl                      true
% 2.62/1.02  --gc_record_bc_elim                     false
% 2.62/1.02  
% 2.62/1.02  ------ Preprocessing Options
% 2.62/1.02  
% 2.62/1.02  --preprocessing_flag                    true
% 2.62/1.02  --time_out_prep_mult                    0.1
% 2.62/1.02  --splitting_mode                        input
% 2.62/1.02  --splitting_grd                         true
% 2.62/1.02  --splitting_cvd                         false
% 2.62/1.02  --splitting_cvd_svl                     false
% 2.62/1.02  --splitting_nvd                         32
% 2.62/1.02  --sub_typing                            true
% 2.62/1.02  --prep_gs_sim                           true
% 2.62/1.02  --prep_unflatten                        true
% 2.62/1.02  --prep_res_sim                          true
% 2.62/1.02  --prep_upred                            true
% 2.62/1.02  --prep_sem_filter                       exhaustive
% 2.62/1.02  --prep_sem_filter_out                   false
% 2.62/1.02  --pred_elim                             true
% 2.62/1.02  --res_sim_input                         true
% 2.62/1.02  --eq_ax_congr_red                       true
% 2.62/1.02  --pure_diseq_elim                       true
% 2.62/1.02  --brand_transform                       false
% 2.62/1.02  --non_eq_to_eq                          false
% 2.62/1.02  --prep_def_merge                        true
% 2.62/1.02  --prep_def_merge_prop_impl              false
% 2.62/1.02  --prep_def_merge_mbd                    true
% 2.62/1.02  --prep_def_merge_tr_red                 false
% 2.62/1.02  --prep_def_merge_tr_cl                  false
% 2.62/1.02  --smt_preprocessing                     true
% 2.62/1.02  --smt_ac_axioms                         fast
% 2.62/1.02  --preprocessed_out                      false
% 2.62/1.02  --preprocessed_stats                    false
% 2.62/1.02  
% 2.62/1.02  ------ Abstraction refinement Options
% 2.62/1.02  
% 2.62/1.02  --abstr_ref                             []
% 2.62/1.02  --abstr_ref_prep                        false
% 2.62/1.02  --abstr_ref_until_sat                   false
% 2.62/1.02  --abstr_ref_sig_restrict                funpre
% 2.62/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.62/1.02  --abstr_ref_under                       []
% 2.62/1.02  
% 2.62/1.02  ------ SAT Options
% 2.62/1.02  
% 2.62/1.02  --sat_mode                              false
% 2.62/1.02  --sat_fm_restart_options                ""
% 2.62/1.02  --sat_gr_def                            false
% 2.62/1.02  --sat_epr_types                         true
% 2.62/1.02  --sat_non_cyclic_types                  false
% 2.62/1.02  --sat_finite_models                     false
% 2.62/1.02  --sat_fm_lemmas                         false
% 2.62/1.02  --sat_fm_prep                           false
% 2.62/1.02  --sat_fm_uc_incr                        true
% 2.62/1.02  --sat_out_model                         small
% 2.62/1.02  --sat_out_clauses                       false
% 2.62/1.02  
% 2.62/1.02  ------ QBF Options
% 2.62/1.02  
% 2.62/1.02  --qbf_mode                              false
% 2.62/1.02  --qbf_elim_univ                         false
% 2.62/1.02  --qbf_dom_inst                          none
% 2.62/1.02  --qbf_dom_pre_inst                      false
% 2.62/1.02  --qbf_sk_in                             false
% 2.62/1.02  --qbf_pred_elim                         true
% 2.62/1.02  --qbf_split                             512
% 2.62/1.02  
% 2.62/1.02  ------ BMC1 Options
% 2.62/1.02  
% 2.62/1.02  --bmc1_incremental                      false
% 2.62/1.02  --bmc1_axioms                           reachable_all
% 2.62/1.02  --bmc1_min_bound                        0
% 2.62/1.02  --bmc1_max_bound                        -1
% 2.62/1.02  --bmc1_max_bound_default                -1
% 2.62/1.02  --bmc1_symbol_reachability              true
% 2.62/1.02  --bmc1_property_lemmas                  false
% 2.62/1.02  --bmc1_k_induction                      false
% 2.62/1.02  --bmc1_non_equiv_states                 false
% 2.62/1.02  --bmc1_deadlock                         false
% 2.62/1.02  --bmc1_ucm                              false
% 2.62/1.02  --bmc1_add_unsat_core                   none
% 2.62/1.02  --bmc1_unsat_core_children              false
% 2.62/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.62/1.02  --bmc1_out_stat                         full
% 2.62/1.02  --bmc1_ground_init                      false
% 2.62/1.02  --bmc1_pre_inst_next_state              false
% 2.62/1.02  --bmc1_pre_inst_state                   false
% 2.62/1.02  --bmc1_pre_inst_reach_state             false
% 2.62/1.02  --bmc1_out_unsat_core                   false
% 2.62/1.02  --bmc1_aig_witness_out                  false
% 2.62/1.02  --bmc1_verbose                          false
% 2.62/1.02  --bmc1_dump_clauses_tptp                false
% 2.62/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.62/1.02  --bmc1_dump_file                        -
% 2.62/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.62/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.62/1.02  --bmc1_ucm_extend_mode                  1
% 2.62/1.02  --bmc1_ucm_init_mode                    2
% 2.62/1.02  --bmc1_ucm_cone_mode                    none
% 2.62/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.62/1.02  --bmc1_ucm_relax_model                  4
% 2.62/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.62/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.62/1.02  --bmc1_ucm_layered_model                none
% 2.62/1.02  --bmc1_ucm_max_lemma_size               10
% 2.62/1.02  
% 2.62/1.02  ------ AIG Options
% 2.62/1.02  
% 2.62/1.02  --aig_mode                              false
% 2.62/1.02  
% 2.62/1.02  ------ Instantiation Options
% 2.62/1.02  
% 2.62/1.02  --instantiation_flag                    true
% 2.62/1.02  --inst_sos_flag                         false
% 2.62/1.02  --inst_sos_phase                        true
% 2.62/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.62/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.62/1.02  --inst_lit_sel_side                     num_symb
% 2.62/1.02  --inst_solver_per_active                1400
% 2.62/1.02  --inst_solver_calls_frac                1.
% 2.62/1.02  --inst_passive_queue_type               priority_queues
% 2.62/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.62/1.02  --inst_passive_queues_freq              [25;2]
% 2.62/1.02  --inst_dismatching                      true
% 2.62/1.02  --inst_eager_unprocessed_to_passive     true
% 2.62/1.02  --inst_prop_sim_given                   true
% 2.62/1.02  --inst_prop_sim_new                     false
% 2.62/1.02  --inst_subs_new                         false
% 2.62/1.02  --inst_eq_res_simp                      false
% 2.62/1.02  --inst_subs_given                       false
% 2.62/1.02  --inst_orphan_elimination               true
% 2.62/1.02  --inst_learning_loop_flag               true
% 2.62/1.02  --inst_learning_start                   3000
% 2.62/1.02  --inst_learning_factor                  2
% 2.62/1.02  --inst_start_prop_sim_after_learn       3
% 2.62/1.02  --inst_sel_renew                        solver
% 2.62/1.02  --inst_lit_activity_flag                true
% 2.62/1.02  --inst_restr_to_given                   false
% 2.62/1.02  --inst_activity_threshold               500
% 2.62/1.02  --inst_out_proof                        true
% 2.62/1.02  
% 2.62/1.02  ------ Resolution Options
% 2.62/1.02  
% 2.62/1.02  --resolution_flag                       true
% 2.62/1.02  --res_lit_sel                           adaptive
% 2.62/1.02  --res_lit_sel_side                      none
% 2.62/1.02  --res_ordering                          kbo
% 2.62/1.02  --res_to_prop_solver                    active
% 2.62/1.02  --res_prop_simpl_new                    false
% 2.62/1.02  --res_prop_simpl_given                  true
% 2.62/1.02  --res_passive_queue_type                priority_queues
% 2.62/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.62/1.02  --res_passive_queues_freq               [15;5]
% 2.62/1.02  --res_forward_subs                      full
% 2.62/1.02  --res_backward_subs                     full
% 2.62/1.02  --res_forward_subs_resolution           true
% 2.62/1.02  --res_backward_subs_resolution          true
% 2.62/1.02  --res_orphan_elimination                true
% 2.62/1.02  --res_time_limit                        2.
% 2.62/1.02  --res_out_proof                         true
% 2.62/1.02  
% 2.62/1.02  ------ Superposition Options
% 2.62/1.02  
% 2.62/1.02  --superposition_flag                    true
% 2.62/1.02  --sup_passive_queue_type                priority_queues
% 2.62/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.62/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.62/1.02  --demod_completeness_check              fast
% 2.62/1.02  --demod_use_ground                      true
% 2.62/1.02  --sup_to_prop_solver                    passive
% 2.62/1.02  --sup_prop_simpl_new                    true
% 2.62/1.02  --sup_prop_simpl_given                  true
% 2.62/1.02  --sup_fun_splitting                     false
% 2.62/1.02  --sup_smt_interval                      50000
% 2.62/1.02  
% 2.62/1.02  ------ Superposition Simplification Setup
% 2.62/1.02  
% 2.62/1.02  --sup_indices_passive                   []
% 2.62/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.62/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/1.02  --sup_full_bw                           [BwDemod]
% 2.62/1.02  --sup_immed_triv                        [TrivRules]
% 2.62/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.62/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/1.02  --sup_immed_bw_main                     []
% 2.62/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.62/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.62/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.62/1.02  
% 2.62/1.02  ------ Combination Options
% 2.62/1.02  
% 2.62/1.02  --comb_res_mult                         3
% 2.62/1.02  --comb_sup_mult                         2
% 2.62/1.02  --comb_inst_mult                        10
% 2.62/1.02  
% 2.62/1.02  ------ Debug Options
% 2.62/1.02  
% 2.62/1.02  --dbg_backtrace                         false
% 2.62/1.02  --dbg_dump_prop_clauses                 false
% 2.62/1.02  --dbg_dump_prop_clauses_file            -
% 2.62/1.02  --dbg_out_stat                          false
% 2.62/1.02  ------ Parsing...
% 2.62/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.62/1.02  
% 2.62/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.62/1.02  
% 2.62/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.62/1.02  
% 2.62/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.62/1.02  ------ Proving...
% 2.62/1.02  ------ Problem Properties 
% 2.62/1.02  
% 2.62/1.02  
% 2.62/1.02  clauses                                 17
% 2.62/1.02  conjectures                             2
% 2.62/1.02  EPR                                     1
% 2.62/1.02  Horn                                    17
% 2.62/1.02  unary                                   8
% 2.62/1.02  binary                                  6
% 2.62/1.02  lits                                    29
% 2.62/1.02  lits eq                                 11
% 2.62/1.02  fd_pure                                 0
% 2.62/1.02  fd_pseudo                               0
% 2.62/1.02  fd_cond                                 0
% 2.62/1.02  fd_pseudo_cond                          0
% 2.62/1.02  AC symbols                              0
% 2.62/1.02  
% 2.62/1.02  ------ Schedule dynamic 5 is on 
% 2.62/1.02  
% 2.62/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.62/1.02  
% 2.62/1.02  
% 2.62/1.02  ------ 
% 2.62/1.02  Current options:
% 2.62/1.02  ------ 
% 2.62/1.02  
% 2.62/1.02  ------ Input Options
% 2.62/1.02  
% 2.62/1.02  --out_options                           all
% 2.62/1.02  --tptp_safe_out                         true
% 2.62/1.02  --problem_path                          ""
% 2.62/1.02  --include_path                          ""
% 2.62/1.02  --clausifier                            res/vclausify_rel
% 2.62/1.02  --clausifier_options                    --mode clausify
% 2.62/1.02  --stdin                                 false
% 2.62/1.02  --stats_out                             all
% 2.62/1.02  
% 2.62/1.02  ------ General Options
% 2.62/1.02  
% 2.62/1.02  --fof                                   false
% 2.62/1.02  --time_out_real                         305.
% 2.62/1.02  --time_out_virtual                      -1.
% 2.62/1.02  --symbol_type_check                     false
% 2.62/1.02  --clausify_out                          false
% 2.62/1.02  --sig_cnt_out                           false
% 2.62/1.02  --trig_cnt_out                          false
% 2.62/1.02  --trig_cnt_out_tolerance                1.
% 2.62/1.02  --trig_cnt_out_sk_spl                   false
% 2.62/1.02  --abstr_cl_out                          false
% 2.62/1.02  
% 2.62/1.02  ------ Global Options
% 2.62/1.02  
% 2.62/1.02  --schedule                              default
% 2.62/1.02  --add_important_lit                     false
% 2.62/1.02  --prop_solver_per_cl                    1000
% 2.62/1.02  --min_unsat_core                        false
% 2.62/1.02  --soft_assumptions                      false
% 2.62/1.02  --soft_lemma_size                       3
% 2.62/1.02  --prop_impl_unit_size                   0
% 2.62/1.02  --prop_impl_unit                        []
% 2.62/1.02  --share_sel_clauses                     true
% 2.62/1.02  --reset_solvers                         false
% 2.62/1.02  --bc_imp_inh                            [conj_cone]
% 2.62/1.02  --conj_cone_tolerance                   3.
% 2.62/1.02  --extra_neg_conj                        none
% 2.62/1.02  --large_theory_mode                     true
% 2.62/1.02  --prolific_symb_bound                   200
% 2.62/1.02  --lt_threshold                          2000
% 2.62/1.02  --clause_weak_htbl                      true
% 2.62/1.02  --gc_record_bc_elim                     false
% 2.62/1.02  
% 2.62/1.02  ------ Preprocessing Options
% 2.62/1.02  
% 2.62/1.02  --preprocessing_flag                    true
% 2.62/1.02  --time_out_prep_mult                    0.1
% 2.62/1.02  --splitting_mode                        input
% 2.62/1.02  --splitting_grd                         true
% 2.62/1.02  --splitting_cvd                         false
% 2.62/1.02  --splitting_cvd_svl                     false
% 2.62/1.02  --splitting_nvd                         32
% 2.62/1.02  --sub_typing                            true
% 2.62/1.02  --prep_gs_sim                           true
% 2.62/1.02  --prep_unflatten                        true
% 2.62/1.02  --prep_res_sim                          true
% 2.62/1.02  --prep_upred                            true
% 2.62/1.02  --prep_sem_filter                       exhaustive
% 2.62/1.02  --prep_sem_filter_out                   false
% 2.62/1.02  --pred_elim                             true
% 2.62/1.02  --res_sim_input                         true
% 2.62/1.02  --eq_ax_congr_red                       true
% 2.62/1.02  --pure_diseq_elim                       true
% 2.62/1.02  --brand_transform                       false
% 2.62/1.02  --non_eq_to_eq                          false
% 2.62/1.02  --prep_def_merge                        true
% 2.62/1.02  --prep_def_merge_prop_impl              false
% 2.62/1.02  --prep_def_merge_mbd                    true
% 2.62/1.02  --prep_def_merge_tr_red                 false
% 2.62/1.02  --prep_def_merge_tr_cl                  false
% 2.62/1.02  --smt_preprocessing                     true
% 2.62/1.02  --smt_ac_axioms                         fast
% 2.62/1.02  --preprocessed_out                      false
% 2.62/1.02  --preprocessed_stats                    false
% 2.62/1.02  
% 2.62/1.02  ------ Abstraction refinement Options
% 2.62/1.02  
% 2.62/1.02  --abstr_ref                             []
% 2.62/1.02  --abstr_ref_prep                        false
% 2.62/1.02  --abstr_ref_until_sat                   false
% 2.62/1.02  --abstr_ref_sig_restrict                funpre
% 2.62/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.62/1.02  --abstr_ref_under                       []
% 2.62/1.02  
% 2.62/1.02  ------ SAT Options
% 2.62/1.02  
% 2.62/1.02  --sat_mode                              false
% 2.62/1.02  --sat_fm_restart_options                ""
% 2.62/1.02  --sat_gr_def                            false
% 2.62/1.02  --sat_epr_types                         true
% 2.62/1.02  --sat_non_cyclic_types                  false
% 2.62/1.02  --sat_finite_models                     false
% 2.62/1.02  --sat_fm_lemmas                         false
% 2.62/1.02  --sat_fm_prep                           false
% 2.62/1.02  --sat_fm_uc_incr                        true
% 2.62/1.02  --sat_out_model                         small
% 2.62/1.02  --sat_out_clauses                       false
% 2.62/1.02  
% 2.62/1.02  ------ QBF Options
% 2.62/1.02  
% 2.62/1.02  --qbf_mode                              false
% 2.62/1.02  --qbf_elim_univ                         false
% 2.62/1.02  --qbf_dom_inst                          none
% 2.62/1.02  --qbf_dom_pre_inst                      false
% 2.62/1.02  --qbf_sk_in                             false
% 2.62/1.02  --qbf_pred_elim                         true
% 2.62/1.02  --qbf_split                             512
% 2.62/1.02  
% 2.62/1.02  ------ BMC1 Options
% 2.62/1.02  
% 2.62/1.02  --bmc1_incremental                      false
% 2.62/1.02  --bmc1_axioms                           reachable_all
% 2.62/1.02  --bmc1_min_bound                        0
% 2.62/1.02  --bmc1_max_bound                        -1
% 2.62/1.02  --bmc1_max_bound_default                -1
% 2.62/1.02  --bmc1_symbol_reachability              true
% 2.62/1.02  --bmc1_property_lemmas                  false
% 2.62/1.02  --bmc1_k_induction                      false
% 2.62/1.02  --bmc1_non_equiv_states                 false
% 2.62/1.02  --bmc1_deadlock                         false
% 2.62/1.02  --bmc1_ucm                              false
% 2.62/1.02  --bmc1_add_unsat_core                   none
% 2.62/1.02  --bmc1_unsat_core_children              false
% 2.62/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.62/1.02  --bmc1_out_stat                         full
% 2.62/1.02  --bmc1_ground_init                      false
% 2.62/1.02  --bmc1_pre_inst_next_state              false
% 2.62/1.02  --bmc1_pre_inst_state                   false
% 2.62/1.02  --bmc1_pre_inst_reach_state             false
% 2.62/1.02  --bmc1_out_unsat_core                   false
% 2.62/1.02  --bmc1_aig_witness_out                  false
% 2.62/1.02  --bmc1_verbose                          false
% 2.62/1.02  --bmc1_dump_clauses_tptp                false
% 2.62/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.62/1.02  --bmc1_dump_file                        -
% 2.62/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.62/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.62/1.02  --bmc1_ucm_extend_mode                  1
% 2.62/1.02  --bmc1_ucm_init_mode                    2
% 2.62/1.02  --bmc1_ucm_cone_mode                    none
% 2.62/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.62/1.02  --bmc1_ucm_relax_model                  4
% 2.62/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.62/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.62/1.02  --bmc1_ucm_layered_model                none
% 2.62/1.02  --bmc1_ucm_max_lemma_size               10
% 2.62/1.02  
% 2.62/1.02  ------ AIG Options
% 2.62/1.02  
% 2.62/1.02  --aig_mode                              false
% 2.62/1.02  
% 2.62/1.02  ------ Instantiation Options
% 2.62/1.02  
% 2.62/1.02  --instantiation_flag                    true
% 2.62/1.02  --inst_sos_flag                         false
% 2.62/1.02  --inst_sos_phase                        true
% 2.62/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.62/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.62/1.02  --inst_lit_sel_side                     none
% 2.62/1.02  --inst_solver_per_active                1400
% 2.62/1.02  --inst_solver_calls_frac                1.
% 2.62/1.02  --inst_passive_queue_type               priority_queues
% 2.62/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.62/1.02  --inst_passive_queues_freq              [25;2]
% 2.62/1.02  --inst_dismatching                      true
% 2.62/1.02  --inst_eager_unprocessed_to_passive     true
% 2.62/1.02  --inst_prop_sim_given                   true
% 2.62/1.02  --inst_prop_sim_new                     false
% 2.62/1.02  --inst_subs_new                         false
% 2.62/1.02  --inst_eq_res_simp                      false
% 2.62/1.02  --inst_subs_given                       false
% 2.62/1.02  --inst_orphan_elimination               true
% 2.62/1.02  --inst_learning_loop_flag               true
% 2.62/1.02  --inst_learning_start                   3000
% 2.62/1.02  --inst_learning_factor                  2
% 2.62/1.02  --inst_start_prop_sim_after_learn       3
% 2.62/1.02  --inst_sel_renew                        solver
% 2.62/1.02  --inst_lit_activity_flag                true
% 2.62/1.02  --inst_restr_to_given                   false
% 2.62/1.02  --inst_activity_threshold               500
% 2.62/1.02  --inst_out_proof                        true
% 2.62/1.02  
% 2.62/1.02  ------ Resolution Options
% 2.62/1.02  
% 2.62/1.02  --resolution_flag                       false
% 2.62/1.02  --res_lit_sel                           adaptive
% 2.62/1.02  --res_lit_sel_side                      none
% 2.62/1.02  --res_ordering                          kbo
% 2.62/1.02  --res_to_prop_solver                    active
% 2.62/1.02  --res_prop_simpl_new                    false
% 2.62/1.02  --res_prop_simpl_given                  true
% 2.62/1.02  --res_passive_queue_type                priority_queues
% 2.62/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.62/1.02  --res_passive_queues_freq               [15;5]
% 2.62/1.02  --res_forward_subs                      full
% 2.62/1.02  --res_backward_subs                     full
% 2.62/1.02  --res_forward_subs_resolution           true
% 2.62/1.02  --res_backward_subs_resolution          true
% 2.62/1.02  --res_orphan_elimination                true
% 2.62/1.02  --res_time_limit                        2.
% 2.62/1.02  --res_out_proof                         true
% 2.62/1.02  
% 2.62/1.02  ------ Superposition Options
% 2.62/1.02  
% 2.62/1.02  --superposition_flag                    true
% 2.62/1.02  --sup_passive_queue_type                priority_queues
% 2.62/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.62/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.62/1.02  --demod_completeness_check              fast
% 2.62/1.02  --demod_use_ground                      true
% 2.62/1.02  --sup_to_prop_solver                    passive
% 2.62/1.02  --sup_prop_simpl_new                    true
% 2.62/1.02  --sup_prop_simpl_given                  true
% 2.62/1.02  --sup_fun_splitting                     false
% 2.62/1.02  --sup_smt_interval                      50000
% 2.62/1.02  
% 2.62/1.02  ------ Superposition Simplification Setup
% 2.62/1.02  
% 2.62/1.02  --sup_indices_passive                   []
% 2.62/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.62/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/1.02  --sup_full_bw                           [BwDemod]
% 2.62/1.02  --sup_immed_triv                        [TrivRules]
% 2.62/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.62/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/1.02  --sup_immed_bw_main                     []
% 2.62/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.62/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.62/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.62/1.02  
% 2.62/1.02  ------ Combination Options
% 2.62/1.02  
% 2.62/1.02  --comb_res_mult                         3
% 2.62/1.02  --comb_sup_mult                         2
% 2.62/1.02  --comb_inst_mult                        10
% 2.62/1.02  
% 2.62/1.02  ------ Debug Options
% 2.62/1.02  
% 2.62/1.02  --dbg_backtrace                         false
% 2.62/1.02  --dbg_dump_prop_clauses                 false
% 2.62/1.02  --dbg_dump_prop_clauses_file            -
% 2.62/1.02  --dbg_out_stat                          false
% 2.62/1.02  
% 2.62/1.02  
% 2.62/1.02  
% 2.62/1.02  
% 2.62/1.02  ------ Proving...
% 2.62/1.02  
% 2.62/1.02  
% 2.62/1.02  % SZS status Theorem for theBenchmark.p
% 2.62/1.02  
% 2.62/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.62/1.02  
% 2.62/1.02  fof(f4,axiom,(
% 2.62/1.02    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/1.02  
% 2.62/1.02  fof(f40,plain,(
% 2.62/1.02    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.62/1.02    inference(cnf_transformation,[],[f4])).
% 2.62/1.02  
% 2.62/1.02  fof(f10,axiom,(
% 2.62/1.02    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/1.02  
% 2.62/1.02  fof(f46,plain,(
% 2.62/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.62/1.02    inference(cnf_transformation,[],[f10])).
% 2.62/1.02  
% 2.62/1.02  fof(f62,plain,(
% 2.62/1.02    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 2.62/1.02    inference(definition_unfolding,[],[f40,f46])).
% 2.62/1.02  
% 2.62/1.02  fof(f19,conjecture,(
% 2.62/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 2.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/1.02  
% 2.62/1.02  fof(f20,negated_conjecture,(
% 2.62/1.02    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 2.62/1.02    inference(negated_conjecture,[],[f19])).
% 2.62/1.02  
% 2.62/1.02  fof(f33,plain,(
% 2.62/1.02    ? [X0,X1,X2,X3] : (((~r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(X2,k1_relset_1(X0,X1,X3))) & r1_tarski(k6_relat_1(X2),X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.62/1.02    inference(ennf_transformation,[],[f20])).
% 2.62/1.02  
% 2.62/1.02  fof(f34,plain,(
% 2.62/1.02    ? [X0,X1,X2,X3] : ((~r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(X2,k1_relset_1(X0,X1,X3))) & r1_tarski(k6_relat_1(X2),X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.62/1.02    inference(flattening,[],[f33])).
% 2.62/1.02  
% 2.62/1.02  fof(f35,plain,(
% 2.62/1.02    ? [X0,X1,X2,X3] : ((~r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(X2,k1_relset_1(X0,X1,X3))) & r1_tarski(k6_relat_1(X2),X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))) & r1_tarski(k6_relat_1(sK2),sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 2.62/1.02    introduced(choice_axiom,[])).
% 2.62/1.02  
% 2.62/1.02  fof(f36,plain,(
% 2.62/1.02    (~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))) & r1_tarski(k6_relat_1(sK2),sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.62/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f34,f35])).
% 2.62/1.02  
% 2.62/1.02  fof(f58,plain,(
% 2.62/1.02    r1_tarski(k6_relat_1(sK2),sK3)),
% 2.62/1.02    inference(cnf_transformation,[],[f36])).
% 2.62/1.02  
% 2.62/1.02  fof(f3,axiom,(
% 2.62/1.02    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/1.02  
% 2.62/1.02  fof(f23,plain,(
% 2.62/1.02    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.62/1.02    inference(ennf_transformation,[],[f3])).
% 2.62/1.02  
% 2.62/1.02  fof(f24,plain,(
% 2.62/1.02    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.62/1.02    inference(flattening,[],[f23])).
% 2.62/1.02  
% 2.62/1.02  fof(f39,plain,(
% 2.62/1.02    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.62/1.02    inference(cnf_transformation,[],[f24])).
% 2.62/1.02  
% 2.62/1.02  fof(f1,axiom,(
% 2.62/1.02    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/1.02  
% 2.62/1.02  fof(f22,plain,(
% 2.62/1.02    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.62/1.02    inference(ennf_transformation,[],[f1])).
% 2.62/1.02  
% 2.62/1.02  fof(f37,plain,(
% 2.62/1.02    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.62/1.02    inference(cnf_transformation,[],[f22])).
% 2.62/1.02  
% 2.62/1.02  fof(f6,axiom,(
% 2.62/1.02    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 2.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/1.02  
% 2.62/1.02  fof(f26,plain,(
% 2.62/1.02    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 2.62/1.02    inference(ennf_transformation,[],[f6])).
% 2.62/1.02  
% 2.62/1.02  fof(f27,plain,(
% 2.62/1.02    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 2.62/1.02    inference(flattening,[],[f26])).
% 2.62/1.02  
% 2.62/1.02  fof(f42,plain,(
% 2.62/1.02    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 2.62/1.02    inference(cnf_transformation,[],[f27])).
% 2.62/1.02  
% 2.62/1.02  fof(f7,axiom,(
% 2.62/1.02    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/1.02  
% 2.62/1.02  fof(f43,plain,(
% 2.62/1.02    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.62/1.02    inference(cnf_transformation,[],[f7])).
% 2.62/1.02  
% 2.62/1.02  fof(f64,plain,(
% 2.62/1.02    ( ! [X0,X1] : (r1_xboole_0(k6_subset_1(X0,X1),X1)) )),
% 2.62/1.02    inference(definition_unfolding,[],[f43,f46])).
% 2.62/1.02  
% 2.62/1.02  fof(f11,axiom,(
% 2.62/1.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 2.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/1.02  
% 2.62/1.02  fof(f28,plain,(
% 2.62/1.02    ! [X0] : (! [X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.62/1.02    inference(ennf_transformation,[],[f11])).
% 2.62/1.02  
% 2.62/1.02  fof(f47,plain,(
% 2.62/1.02    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.62/1.02    inference(cnf_transformation,[],[f28])).
% 2.62/1.02  
% 2.62/1.02  fof(f13,axiom,(
% 2.62/1.02    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/1.02  
% 2.62/1.02  fof(f49,plain,(
% 2.62/1.02    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.62/1.02    inference(cnf_transformation,[],[f13])).
% 2.62/1.02  
% 2.62/1.02  fof(f14,axiom,(
% 2.62/1.02    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/1.02  
% 2.62/1.02  fof(f51,plain,(
% 2.62/1.02    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.62/1.02    inference(cnf_transformation,[],[f14])).
% 2.62/1.02  
% 2.62/1.02  fof(f16,axiom,(
% 2.62/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/1.02  
% 2.62/1.02  fof(f30,plain,(
% 2.62/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.62/1.02    inference(ennf_transformation,[],[f16])).
% 2.62/1.02  
% 2.62/1.02  fof(f54,plain,(
% 2.62/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.62/1.02    inference(cnf_transformation,[],[f30])).
% 2.62/1.02  
% 2.62/1.02  fof(f57,plain,(
% 2.62/1.02    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.62/1.02    inference(cnf_transformation,[],[f36])).
% 2.62/1.02  
% 2.62/1.02  fof(f15,axiom,(
% 2.62/1.02    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/1.02  
% 2.62/1.02  fof(f21,plain,(
% 2.62/1.02    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 2.62/1.02    inference(pure_predicate_removal,[],[f15])).
% 2.62/1.02  
% 2.62/1.02  fof(f53,plain,(
% 2.62/1.02    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.62/1.02    inference(cnf_transformation,[],[f21])).
% 2.62/1.02  
% 2.62/1.02  fof(f2,axiom,(
% 2.62/1.02    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/1.02  
% 2.62/1.02  fof(f38,plain,(
% 2.62/1.02    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.62/1.02    inference(cnf_transformation,[],[f2])).
% 2.62/1.02  
% 2.62/1.02  fof(f9,axiom,(
% 2.62/1.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/1.02  
% 2.62/1.02  fof(f45,plain,(
% 2.62/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.62/1.02    inference(cnf_transformation,[],[f9])).
% 2.62/1.02  
% 2.62/1.02  fof(f8,axiom,(
% 2.62/1.02    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/1.02  
% 2.62/1.02  fof(f44,plain,(
% 2.62/1.02    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.62/1.02    inference(cnf_transformation,[],[f8])).
% 2.62/1.02  
% 2.62/1.02  fof(f60,plain,(
% 2.62/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 2.62/1.02    inference(definition_unfolding,[],[f45,f44])).
% 2.62/1.02  
% 2.62/1.02  fof(f61,plain,(
% 2.62/1.02    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0) )),
% 2.62/1.02    inference(definition_unfolding,[],[f38,f60])).
% 2.62/1.02  
% 2.62/1.02  fof(f5,axiom,(
% 2.62/1.02    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/1.02  
% 2.62/1.02  fof(f25,plain,(
% 2.62/1.02    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.62/1.02    inference(ennf_transformation,[],[f5])).
% 2.62/1.02  
% 2.62/1.02  fof(f41,plain,(
% 2.62/1.02    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.62/1.02    inference(cnf_transformation,[],[f25])).
% 2.62/1.02  
% 2.62/1.02  fof(f63,plain,(
% 2.62/1.02    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) | ~r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 2.62/1.02    inference(definition_unfolding,[],[f41,f60,f46])).
% 2.62/1.02  
% 2.62/1.02  fof(f12,axiom,(
% 2.62/1.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))))),
% 2.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/1.02  
% 2.62/1.02  fof(f29,plain,(
% 2.62/1.02    ! [X0] : (! [X1] : (r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.62/1.02    inference(ennf_transformation,[],[f12])).
% 2.62/1.02  
% 2.62/1.02  fof(f48,plain,(
% 2.62/1.02    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.62/1.02    inference(cnf_transformation,[],[f29])).
% 2.62/1.02  
% 2.62/1.02  fof(f50,plain,(
% 2.62/1.02    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.62/1.02    inference(cnf_transformation,[],[f13])).
% 2.62/1.02  
% 2.62/1.02  fof(f52,plain,(
% 2.62/1.02    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.62/1.02    inference(cnf_transformation,[],[f14])).
% 2.62/1.02  
% 2.62/1.02  fof(f18,axiom,(
% 2.62/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/1.02  
% 2.62/1.02  fof(f32,plain,(
% 2.62/1.02    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.62/1.02    inference(ennf_transformation,[],[f18])).
% 2.62/1.02  
% 2.62/1.02  fof(f56,plain,(
% 2.62/1.02    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.62/1.02    inference(cnf_transformation,[],[f32])).
% 2.62/1.02  
% 2.62/1.02  fof(f59,plain,(
% 2.62/1.02    ~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))),
% 2.62/1.02    inference(cnf_transformation,[],[f36])).
% 2.62/1.02  
% 2.62/1.02  fof(f17,axiom,(
% 2.62/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.62/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/1.02  
% 2.62/1.02  fof(f31,plain,(
% 2.62/1.02    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.62/1.02    inference(ennf_transformation,[],[f17])).
% 2.62/1.02  
% 2.62/1.02  fof(f55,plain,(
% 2.62/1.02    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.62/1.02    inference(cnf_transformation,[],[f31])).
% 2.62/1.02  
% 2.62/1.02  cnf(c_3,plain,
% 2.62/1.02      ( r1_tarski(k6_subset_1(X0,X1),X0) ),
% 2.62/1.02      inference(cnf_transformation,[],[f62]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_545,plain,
% 2.62/1.02      ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
% 2.62/1.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_18,negated_conjecture,
% 2.62/1.02      ( r1_tarski(k6_relat_1(sK2),sK3) ),
% 2.62/1.02      inference(cnf_transformation,[],[f58]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_539,plain,
% 2.62/1.02      ( r1_tarski(k6_relat_1(sK2),sK3) = iProver_top ),
% 2.62/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_2,plain,
% 2.62/1.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 2.62/1.02      inference(cnf_transformation,[],[f39]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_546,plain,
% 2.62/1.02      ( r1_tarski(X0,X1) != iProver_top
% 2.62/1.02      | r1_tarski(X2,X0) != iProver_top
% 2.62/1.02      | r1_tarski(X2,X1) = iProver_top ),
% 2.62/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_1677,plain,
% 2.62/1.02      ( r1_tarski(X0,k6_relat_1(sK2)) != iProver_top
% 2.62/1.02      | r1_tarski(X0,sK3) = iProver_top ),
% 2.62/1.02      inference(superposition,[status(thm)],[c_539,c_546]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_2327,plain,
% 2.62/1.02      ( r1_tarski(k6_subset_1(k6_relat_1(sK2),X0),sK3) = iProver_top ),
% 2.62/1.02      inference(superposition,[status(thm)],[c_545,c_1677]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_0,plain,
% 2.62/1.02      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.62/1.02      inference(cnf_transformation,[],[f37]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_5,plain,
% 2.62/1.02      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 2.62/1.02      inference(cnf_transformation,[],[f42]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_6,plain,
% 2.62/1.02      ( r1_xboole_0(k6_subset_1(X0,X1),X1) ),
% 2.62/1.02      inference(cnf_transformation,[],[f64]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_188,plain,
% 2.62/1.02      ( ~ r1_tarski(X0,X1)
% 2.62/1.02      | v1_xboole_0(X0)
% 2.62/1.02      | X2 != X1
% 2.62/1.02      | k6_subset_1(X3,X2) != X0 ),
% 2.62/1.02      inference(resolution_lifted,[status(thm)],[c_5,c_6]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_189,plain,
% 2.62/1.02      ( ~ r1_tarski(k6_subset_1(X0,X1),X1)
% 2.62/1.02      | v1_xboole_0(k6_subset_1(X0,X1)) ),
% 2.62/1.02      inference(unflattening,[status(thm)],[c_188]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_203,plain,
% 2.62/1.02      ( ~ r1_tarski(k6_subset_1(X0,X1),X1)
% 2.62/1.02      | k6_subset_1(X0,X1) != X2
% 2.62/1.02      | k1_xboole_0 = X2 ),
% 2.62/1.02      inference(resolution_lifted,[status(thm)],[c_0,c_189]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_204,plain,
% 2.62/1.02      ( ~ r1_tarski(k6_subset_1(X0,X1),X1)
% 2.62/1.02      | k1_xboole_0 = k6_subset_1(X0,X1) ),
% 2.62/1.02      inference(unflattening,[status(thm)],[c_203]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_538,plain,
% 2.62/1.02      ( k1_xboole_0 = k6_subset_1(X0,X1)
% 2.62/1.02      | r1_tarski(k6_subset_1(X0,X1),X1) != iProver_top ),
% 2.62/1.02      inference(predicate_to_equality,[status(thm)],[c_204]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_2340,plain,
% 2.62/1.02      ( k6_subset_1(k6_relat_1(sK2),sK3) = k1_xboole_0 ),
% 2.62/1.02      inference(superposition,[status(thm)],[c_2327,c_538]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_7,plain,
% 2.62/1.02      ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
% 2.62/1.02      | ~ v1_relat_1(X1)
% 2.62/1.02      | ~ v1_relat_1(X0) ),
% 2.62/1.02      inference(cnf_transformation,[],[f47]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_543,plain,
% 2.62/1.02      ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) = iProver_top
% 2.62/1.02      | v1_relat_1(X0) != iProver_top
% 2.62/1.02      | v1_relat_1(X1) != iProver_top ),
% 2.62/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_2398,plain,
% 2.62/1.02      ( r1_tarski(k6_subset_1(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3)),k1_relat_1(k1_xboole_0)) = iProver_top
% 2.62/1.02      | v1_relat_1(k6_relat_1(sK2)) != iProver_top
% 2.62/1.02      | v1_relat_1(sK3) != iProver_top ),
% 2.62/1.02      inference(superposition,[status(thm)],[c_2340,c_543]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_10,plain,
% 2.62/1.02      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.62/1.02      inference(cnf_transformation,[],[f49]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_2416,plain,
% 2.62/1.02      ( r1_tarski(k6_subset_1(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3)),k1_xboole_0) = iProver_top
% 2.62/1.02      | v1_relat_1(k6_relat_1(sK2)) != iProver_top
% 2.62/1.02      | v1_relat_1(sK3) != iProver_top ),
% 2.62/1.02      inference(light_normalisation,[status(thm)],[c_2398,c_10]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_12,plain,
% 2.62/1.02      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 2.62/1.02      inference(cnf_transformation,[],[f51]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_2417,plain,
% 2.62/1.02      ( r1_tarski(k6_subset_1(sK2,k1_relat_1(sK3)),k1_xboole_0) = iProver_top
% 2.62/1.02      | v1_relat_1(k6_relat_1(sK2)) != iProver_top
% 2.62/1.02      | v1_relat_1(sK3) != iProver_top ),
% 2.62/1.02      inference(demodulation,[status(thm)],[c_2416,c_12]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_335,plain,( X0 = X0 ),theory(equality) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_678,plain,
% 2.62/1.02      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 2.62/1.02      inference(instantiation,[status(thm)],[c_335]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_14,plain,
% 2.62/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/1.02      | v1_relat_1(X0) ),
% 2.62/1.02      inference(cnf_transformation,[],[f54]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_19,negated_conjecture,
% 2.62/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.62/1.02      inference(cnf_transformation,[],[f57]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_236,plain,
% 2.62/1.02      ( v1_relat_1(X0)
% 2.62/1.02      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 2.62/1.02      | sK3 != X0 ),
% 2.62/1.02      inference(resolution_lifted,[status(thm)],[c_14,c_19]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_237,plain,
% 2.62/1.02      ( v1_relat_1(sK3)
% 2.62/1.02      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 2.62/1.02      inference(unflattening,[status(thm)],[c_236]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_681,plain,
% 2.62/1.02      ( v1_relat_1(sK3)
% 2.62/1.02      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 2.62/1.02      inference(instantiation,[status(thm)],[c_237]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_682,plain,
% 2.62/1.02      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 2.62/1.02      | v1_relat_1(sK3) = iProver_top ),
% 2.62/1.02      inference(predicate_to_equality,[status(thm)],[c_681]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_2941,plain,
% 2.62/1.02      ( v1_relat_1(k6_relat_1(sK2)) != iProver_top
% 2.62/1.02      | r1_tarski(k6_subset_1(sK2,k1_relat_1(sK3)),k1_xboole_0) = iProver_top ),
% 2.62/1.02      inference(global_propositional_subsumption,
% 2.62/1.02                [status(thm)],
% 2.62/1.02                [c_2417,c_678,c_682]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_2942,plain,
% 2.62/1.02      ( r1_tarski(k6_subset_1(sK2,k1_relat_1(sK3)),k1_xboole_0) = iProver_top
% 2.62/1.02      | v1_relat_1(k6_relat_1(sK2)) != iProver_top ),
% 2.62/1.02      inference(renaming,[status(thm)],[c_2941]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_13,plain,
% 2.62/1.02      ( v1_relat_1(k6_relat_1(X0)) ),
% 2.62/1.02      inference(cnf_transformation,[],[f53]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_541,plain,
% 2.62/1.02      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 2.62/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_2947,plain,
% 2.62/1.02      ( r1_tarski(k6_subset_1(sK2,k1_relat_1(sK3)),k1_xboole_0) = iProver_top ),
% 2.62/1.02      inference(forward_subsumption_resolution,
% 2.62/1.02                [status(thm)],
% 2.62/1.02                [c_2942,c_541]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_1,plain,
% 2.62/1.02      ( k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
% 2.62/1.02      inference(cnf_transformation,[],[f61]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_4,plain,
% 2.62/1.02      ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
% 2.62/1.02      | ~ r1_tarski(k6_subset_1(X0,X1),X2) ),
% 2.62/1.02      inference(cnf_transformation,[],[f63]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_544,plain,
% 2.62/1.02      ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) = iProver_top
% 2.62/1.02      | r1_tarski(k6_subset_1(X0,X1),X2) != iProver_top ),
% 2.62/1.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_1447,plain,
% 2.62/1.02      ( r1_tarski(X0,X1) = iProver_top
% 2.62/1.02      | r1_tarski(k6_subset_1(X0,X1),k1_xboole_0) != iProver_top ),
% 2.62/1.02      inference(superposition,[status(thm)],[c_1,c_544]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_2950,plain,
% 2.62/1.02      ( r1_tarski(sK2,k1_relat_1(sK3)) = iProver_top ),
% 2.62/1.02      inference(superposition,[status(thm)],[c_2947,c_1447]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_8,plain,
% 2.62/1.02      ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
% 2.62/1.02      | ~ v1_relat_1(X1)
% 2.62/1.02      | ~ v1_relat_1(X0) ),
% 2.62/1.02      inference(cnf_transformation,[],[f48]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_542,plain,
% 2.62/1.02      ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) = iProver_top
% 2.62/1.02      | v1_relat_1(X0) != iProver_top
% 2.62/1.02      | v1_relat_1(X1) != iProver_top ),
% 2.62/1.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_2399,plain,
% 2.62/1.02      ( r1_tarski(k6_subset_1(k2_relat_1(k6_relat_1(sK2)),k2_relat_1(sK3)),k2_relat_1(k1_xboole_0)) = iProver_top
% 2.62/1.02      | v1_relat_1(k6_relat_1(sK2)) != iProver_top
% 2.62/1.02      | v1_relat_1(sK3) != iProver_top ),
% 2.62/1.02      inference(superposition,[status(thm)],[c_2340,c_542]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_9,plain,
% 2.62/1.02      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.62/1.02      inference(cnf_transformation,[],[f50]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_2408,plain,
% 2.62/1.02      ( r1_tarski(k6_subset_1(k2_relat_1(k6_relat_1(sK2)),k2_relat_1(sK3)),k1_xboole_0) = iProver_top
% 2.62/1.02      | v1_relat_1(k6_relat_1(sK2)) != iProver_top
% 2.62/1.02      | v1_relat_1(sK3) != iProver_top ),
% 2.62/1.02      inference(light_normalisation,[status(thm)],[c_2399,c_9]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_11,plain,
% 2.62/1.02      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 2.62/1.02      inference(cnf_transformation,[],[f52]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_2409,plain,
% 2.62/1.02      ( r1_tarski(k6_subset_1(sK2,k2_relat_1(sK3)),k1_xboole_0) = iProver_top
% 2.62/1.02      | v1_relat_1(k6_relat_1(sK2)) != iProver_top
% 2.62/1.02      | v1_relat_1(sK3) != iProver_top ),
% 2.62/1.02      inference(demodulation,[status(thm)],[c_2408,c_11]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_2918,plain,
% 2.62/1.02      ( v1_relat_1(k6_relat_1(sK2)) != iProver_top
% 2.62/1.02      | r1_tarski(k6_subset_1(sK2,k2_relat_1(sK3)),k1_xboole_0) = iProver_top ),
% 2.62/1.02      inference(global_propositional_subsumption,
% 2.62/1.02                [status(thm)],
% 2.62/1.02                [c_2409,c_678,c_682]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_2919,plain,
% 2.62/1.02      ( r1_tarski(k6_subset_1(sK2,k2_relat_1(sK3)),k1_xboole_0) = iProver_top
% 2.62/1.02      | v1_relat_1(k6_relat_1(sK2)) != iProver_top ),
% 2.62/1.02      inference(renaming,[status(thm)],[c_2918]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_2924,plain,
% 2.62/1.02      ( r1_tarski(k6_subset_1(sK2,k2_relat_1(sK3)),k1_xboole_0) = iProver_top ),
% 2.62/1.02      inference(forward_subsumption_resolution,
% 2.62/1.02                [status(thm)],
% 2.62/1.02                [c_2919,c_541]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_2927,plain,
% 2.62/1.02      ( r1_tarski(sK2,k2_relat_1(sK3)) = iProver_top ),
% 2.62/1.02      inference(superposition,[status(thm)],[c_2924,c_1447]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_16,plain,
% 2.62/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/1.02      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.62/1.02      inference(cnf_transformation,[],[f56]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_218,plain,
% 2.62/1.02      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.62/1.02      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 2.62/1.02      | sK3 != X2 ),
% 2.62/1.02      inference(resolution_lifted,[status(thm)],[c_16,c_19]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_219,plain,
% 2.62/1.02      ( k2_relset_1(X0,X1,sK3) = k2_relat_1(sK3)
% 2.62/1.02      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 2.62/1.02      inference(unflattening,[status(thm)],[c_218]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_631,plain,
% 2.62/1.02      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 2.62/1.02      inference(equality_resolution,[status(thm)],[c_219]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_17,negated_conjecture,
% 2.62/1.02      ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
% 2.62/1.02      | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) ),
% 2.62/1.02      inference(cnf_transformation,[],[f59]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_540,plain,
% 2.62/1.02      ( r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) != iProver_top
% 2.62/1.02      | r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) != iProver_top ),
% 2.62/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_692,plain,
% 2.62/1.02      ( r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) != iProver_top
% 2.62/1.02      | r1_tarski(sK2,k2_relat_1(sK3)) != iProver_top ),
% 2.62/1.02      inference(demodulation,[status(thm)],[c_631,c_540]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_15,plain,
% 2.62/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.62/1.02      inference(cnf_transformation,[],[f55]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_227,plain,
% 2.62/1.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.62/1.02      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 2.62/1.02      | sK3 != X2 ),
% 2.62/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_19]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_228,plain,
% 2.62/1.02      ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
% 2.62/1.02      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 2.62/1.02      inference(unflattening,[status(thm)],[c_227]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_674,plain,
% 2.62/1.02      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 2.62/1.02      inference(equality_resolution,[status(thm)],[c_228]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(c_743,plain,
% 2.62/1.02      ( r1_tarski(sK2,k2_relat_1(sK3)) != iProver_top
% 2.62/1.02      | r1_tarski(sK2,k1_relat_1(sK3)) != iProver_top ),
% 2.62/1.02      inference(light_normalisation,[status(thm)],[c_692,c_674]) ).
% 2.62/1.02  
% 2.62/1.02  cnf(contradiction,plain,
% 2.62/1.02      ( $false ),
% 2.62/1.02      inference(minisat,[status(thm)],[c_2950,c_2927,c_743]) ).
% 2.62/1.02  
% 2.62/1.02  
% 2.62/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.62/1.02  
% 2.62/1.02  ------                               Statistics
% 2.62/1.02  
% 2.62/1.02  ------ General
% 2.62/1.02  
% 2.62/1.02  abstr_ref_over_cycles:                  0
% 2.62/1.02  abstr_ref_under_cycles:                 0
% 2.62/1.02  gc_basic_clause_elim:                   0
% 2.62/1.02  forced_gc_time:                         0
% 2.62/1.02  parsing_time:                           0.007
% 2.62/1.02  unif_index_cands_time:                  0.
% 2.62/1.02  unif_index_add_time:                    0.
% 2.62/1.02  orderings_time:                         0.
% 2.62/1.02  out_proof_time:                         0.01
% 2.62/1.02  total_time:                             0.134
% 2.62/1.02  num_of_symbols:                         51
% 2.62/1.02  num_of_terms:                           3703
% 2.62/1.02  
% 2.62/1.02  ------ Preprocessing
% 2.62/1.02  
% 2.62/1.02  num_of_splits:                          0
% 2.62/1.02  num_of_split_atoms:                     0
% 2.62/1.02  num_of_reused_defs:                     0
% 2.62/1.02  num_eq_ax_congr_red:                    8
% 2.62/1.02  num_of_sem_filtered_clauses:            1
% 2.62/1.02  num_of_subtypes:                        0
% 2.62/1.02  monotx_restored_types:                  0
% 2.62/1.02  sat_num_of_epr_types:                   0
% 2.62/1.02  sat_num_of_non_cyclic_types:            0
% 2.62/1.02  sat_guarded_non_collapsed_types:        0
% 2.62/1.02  num_pure_diseq_elim:                    0
% 2.62/1.02  simp_replaced_by:                       0
% 2.62/1.02  res_preprocessed:                       100
% 2.62/1.02  prep_upred:                             0
% 2.62/1.02  prep_unflattend:                        6
% 2.62/1.02  smt_new_axioms:                         0
% 2.62/1.02  pred_elim_cands:                        2
% 2.62/1.02  pred_elim:                              3
% 2.62/1.02  pred_elim_cl:                           3
% 2.62/1.02  pred_elim_cycles:                       5
% 2.62/1.02  merged_defs:                            0
% 2.62/1.02  merged_defs_ncl:                        0
% 2.62/1.02  bin_hyper_res:                          0
% 2.62/1.02  prep_cycles:                            4
% 2.62/1.02  pred_elim_time:                         0.002
% 2.62/1.02  splitting_time:                         0.
% 2.62/1.02  sem_filter_time:                        0.
% 2.62/1.02  monotx_time:                            0.
% 2.62/1.02  subtype_inf_time:                       0.
% 2.62/1.02  
% 2.62/1.02  ------ Problem properties
% 2.62/1.02  
% 2.62/1.02  clauses:                                17
% 2.62/1.02  conjectures:                            2
% 2.62/1.02  epr:                                    1
% 2.62/1.02  horn:                                   17
% 2.62/1.02  ground:                                 4
% 2.62/1.02  unary:                                  8
% 2.62/1.02  binary:                                 6
% 2.62/1.02  lits:                                   29
% 2.62/1.02  lits_eq:                                11
% 2.62/1.02  fd_pure:                                0
% 2.62/1.02  fd_pseudo:                              0
% 2.62/1.02  fd_cond:                                0
% 2.62/1.02  fd_pseudo_cond:                         0
% 2.62/1.02  ac_symbols:                             0
% 2.62/1.02  
% 2.62/1.02  ------ Propositional Solver
% 2.62/1.02  
% 2.62/1.02  prop_solver_calls:                      26
% 2.62/1.02  prop_fast_solver_calls:                 478
% 2.62/1.02  smt_solver_calls:                       0
% 2.62/1.02  smt_fast_solver_calls:                  0
% 2.62/1.02  prop_num_of_clauses:                    1311
% 2.62/1.02  prop_preprocess_simplified:             4091
% 2.62/1.02  prop_fo_subsumed:                       4
% 2.62/1.02  prop_solver_time:                       0.
% 2.62/1.02  smt_solver_time:                        0.
% 2.62/1.02  smt_fast_solver_time:                   0.
% 2.62/1.02  prop_fast_solver_time:                  0.
% 2.62/1.02  prop_unsat_core_time:                   0.
% 2.62/1.02  
% 2.62/1.02  ------ QBF
% 2.62/1.02  
% 2.62/1.02  qbf_q_res:                              0
% 2.62/1.02  qbf_num_tautologies:                    0
% 2.62/1.02  qbf_prep_cycles:                        0
% 2.62/1.02  
% 2.62/1.02  ------ BMC1
% 2.62/1.02  
% 2.62/1.02  bmc1_current_bound:                     -1
% 2.62/1.02  bmc1_last_solved_bound:                 -1
% 2.62/1.02  bmc1_unsat_core_size:                   -1
% 2.62/1.02  bmc1_unsat_core_parents_size:           -1
% 2.62/1.02  bmc1_merge_next_fun:                    0
% 2.62/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.62/1.02  
% 2.62/1.02  ------ Instantiation
% 2.62/1.02  
% 2.62/1.02  inst_num_of_clauses:                    379
% 2.62/1.02  inst_num_in_passive:                    84
% 2.62/1.02  inst_num_in_active:                     184
% 2.62/1.02  inst_num_in_unprocessed:                111
% 2.62/1.02  inst_num_of_loops:                      190
% 2.62/1.02  inst_num_of_learning_restarts:          0
% 2.62/1.02  inst_num_moves_active_passive:          5
% 2.62/1.02  inst_lit_activity:                      0
% 2.62/1.02  inst_lit_activity_moves:                0
% 2.62/1.02  inst_num_tautologies:                   0
% 2.62/1.02  inst_num_prop_implied:                  0
% 2.62/1.02  inst_num_existing_simplified:           0
% 2.62/1.02  inst_num_eq_res_simplified:             0
% 2.62/1.02  inst_num_child_elim:                    0
% 2.62/1.02  inst_num_of_dismatching_blockings:      44
% 2.62/1.02  inst_num_of_non_proper_insts:           286
% 2.62/1.02  inst_num_of_duplicates:                 0
% 2.62/1.02  inst_inst_num_from_inst_to_res:         0
% 2.62/1.02  inst_dismatching_checking_time:         0.
% 2.62/1.02  
% 2.62/1.02  ------ Resolution
% 2.62/1.02  
% 2.62/1.02  res_num_of_clauses:                     0
% 2.62/1.02  res_num_in_passive:                     0
% 2.62/1.02  res_num_in_active:                      0
% 2.62/1.02  res_num_of_loops:                       104
% 2.62/1.02  res_forward_subset_subsumed:            15
% 2.62/1.02  res_backward_subset_subsumed:           0
% 2.62/1.02  res_forward_subsumed:                   0
% 2.62/1.02  res_backward_subsumed:                  0
% 2.62/1.02  res_forward_subsumption_resolution:     0
% 2.62/1.02  res_backward_subsumption_resolution:    0
% 2.62/1.02  res_clause_to_clause_subsumption:       253
% 2.62/1.02  res_orphan_elimination:                 0
% 2.62/1.02  res_tautology_del:                      19
% 2.62/1.02  res_num_eq_res_simplified:              0
% 2.62/1.02  res_num_sel_changes:                    0
% 2.62/1.02  res_moves_from_active_to_pass:          0
% 2.62/1.02  
% 2.62/1.02  ------ Superposition
% 2.62/1.02  
% 2.62/1.02  sup_time_total:                         0.
% 2.62/1.02  sup_time_generating:                    0.
% 2.62/1.02  sup_time_sim_full:                      0.
% 2.62/1.02  sup_time_sim_immed:                     0.
% 2.62/1.02  
% 2.62/1.02  sup_num_of_clauses:                     65
% 2.62/1.02  sup_num_in_active:                      37
% 2.62/1.02  sup_num_in_passive:                     28
% 2.62/1.02  sup_num_of_loops:                       37
% 2.62/1.02  sup_fw_superposition:                   55
% 2.62/1.02  sup_bw_superposition:                   30
% 2.62/1.02  sup_immediate_simplified:               25
% 2.62/1.02  sup_given_eliminated:                   0
% 2.62/1.02  comparisons_done:                       0
% 2.62/1.02  comparisons_avoided:                    0
% 2.62/1.02  
% 2.62/1.02  ------ Simplifications
% 2.62/1.02  
% 2.62/1.02  
% 2.62/1.02  sim_fw_subset_subsumed:                 9
% 2.62/1.02  sim_bw_subset_subsumed:                 0
% 2.62/1.02  sim_fw_subsumed:                        10
% 2.62/1.02  sim_bw_subsumed:                        0
% 2.62/1.02  sim_fw_subsumption_res:                 2
% 2.62/1.02  sim_bw_subsumption_res:                 0
% 2.62/1.02  sim_tautology_del:                      1
% 2.62/1.02  sim_eq_tautology_del:                   1
% 2.62/1.02  sim_eq_res_simp:                        0
% 2.62/1.02  sim_fw_demodulated:                     9
% 2.62/1.02  sim_bw_demodulated:                     1
% 2.62/1.02  sim_light_normalised:                   11
% 2.62/1.02  sim_joinable_taut:                      0
% 2.62/1.02  sim_joinable_simp:                      0
% 2.62/1.02  sim_ac_normalised:                      0
% 2.62/1.02  sim_smt_subsumption:                    0
% 2.62/1.02  
%------------------------------------------------------------------------------
