%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:55:33 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 233 expanded)
%              Number of clauses        :   69 ( 118 expanded)
%              Number of leaves         :   14 (  38 expanded)
%              Depth                    :   17
%              Number of atoms          :  255 ( 502 expanded)
%              Number of equality atoms :   66 (  83 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
   => ( ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f31])).

fof(f48,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f49,plain,(
    ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(X2,X1)
        & v1_relat_1(X2) )
     => ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(k7_relat_1(X2,X0))
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_8,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_239,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_43,X1_43)),X1_43)
    | ~ v1_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_698,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_43,X1_43)),X1_43) = iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_239])).

cnf(c_9,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_238,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0_43,X1_43)),k2_relat_1(X0_43))
    | ~ v1_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_699,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0_43,X1_43)),k2_relat_1(X0_43)) = iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_238])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_231,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_706,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_231])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_235,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43)))
    | k2_relset_1(X1_43,X2_43,X0_43) = k2_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_702,plain,
    ( k2_relset_1(X0_43,X1_43,X2_43) = k2_relat_1(X2_43)
    | m1_subset_1(X2_43,k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_235])).

cnf(c_1170,plain,
    ( k2_relset_1(sK0,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_706,c_702])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_236,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43)))
    | m1_subset_1(k2_relset_1(X1_43,X2_43,X0_43),k1_zfmisc_1(X2_43)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_701,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43))) != iProver_top
    | m1_subset_1(k2_relset_1(X1_43,X2_43,X0_43),k1_zfmisc_1(X2_43)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_236])).

cnf(c_1802,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1170,c_701])).

cnf(c_17,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3037,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1802,c_17])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_244,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
    | r1_tarski(X0_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_693,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) != iProver_top
    | r1_tarski(X0_43,X1_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_244])).

cnf(c_3042,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3037,c_693])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_246,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | ~ r1_tarski(X2_43,X0_43)
    | r1_tarski(X2_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_691,plain,
    ( r1_tarski(X0_43,X1_43) != iProver_top
    | r1_tarski(X2_43,X0_43) != iProver_top
    | r1_tarski(X2_43,X1_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_246])).

cnf(c_3214,plain,
    ( r1_tarski(X0_43,k2_relat_1(sK3)) != iProver_top
    | r1_tarski(X0_43,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3042,c_691])).

cnf(c_3521,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0_43)),sK2) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_699,c_3214])).

cnf(c_822,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_244])).

cnf(c_823,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_822])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_136,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_137,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_136])).

cnf(c_166,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_3,c_137])).

cnf(c_230,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | ~ v1_relat_1(X1_43)
    | v1_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_166])).

cnf(c_853,plain,
    ( ~ r1_tarski(X0_43,k2_zfmisc_1(X1_43,X2_43))
    | v1_relat_1(X0_43)
    | ~ v1_relat_1(k2_zfmisc_1(X1_43,X2_43)) ),
    inference(instantiation,[status(thm)],[c_230])).

cnf(c_935,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_853])).

cnf(c_936,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK2)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_935])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_240,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_43,X1_43)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1019,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_240])).

cnf(c_1020,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1019])).

cnf(c_3538,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0_43)),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3521,c_17,c_823,c_936,c_1020])).

cnf(c_14,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_233,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43)))
    | ~ r1_tarski(k2_relat_1(X0_43),X2_43)
    | ~ r1_tarski(k1_relat_1(X0_43),X1_43)
    | ~ v1_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_704,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43))) = iProver_top
    | r1_tarski(k2_relat_1(X0_43),X2_43) != iProver_top
    | r1_tarski(k1_relat_1(X0_43),X1_43) != iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_233])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k5_relset_1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_234,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43)))
    | k5_relset_1(X1_43,X2_43,X0_43,X3_43) = k7_relat_1(X0_43,X3_43) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_703,plain,
    ( k5_relset_1(X0_43,X1_43,X2_43,X3_43) = k7_relat_1(X2_43,X3_43)
    | m1_subset_1(X2_43,k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_234])).

cnf(c_2034,plain,
    ( k5_relset_1(sK0,sK2,sK3,X0_43) = k7_relat_1(sK3,X0_43) ),
    inference(superposition,[status(thm)],[c_706,c_703])).

cnf(c_15,negated_conjecture,
    ( ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_232,negated_conjecture,
    ( ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_705,plain,
    ( m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_232])).

cnf(c_2458,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2034,c_705])).

cnf(c_2467,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_704,c_2458])).

cnf(c_10,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_237,plain,
    ( v4_relat_1(X0_43,X1_43)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_700,plain,
    ( v4_relat_1(X0_43,X1_43) = iProver_top
    | m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_237])).

cnf(c_1067,plain,
    ( v4_relat_1(sK3,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_706,c_700])).

cnf(c_6,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_241,plain,
    ( ~ v4_relat_1(X0_43,X1_43)
    | ~ v1_relat_1(X0_43)
    | v1_relat_1(k7_relat_1(X0_43,X2_43)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_696,plain,
    ( v4_relat_1(X0_43,X1_43) != iProver_top
    | v1_relat_1(X0_43) != iProver_top
    | v1_relat_1(k7_relat_1(X0_43,X2_43)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_241])).

cnf(c_1344,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0_43)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1067,c_696])).

cnf(c_1499,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0_43)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1344,c_17,c_823,c_936,c_1020])).

cnf(c_3048,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2467,c_1499])).

cnf(c_3547,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3538,c_3048])).

cnf(c_4015,plain,
    ( v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_698,c_3547])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4015,c_1020,c_936,c_823,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:31:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.45/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.03  
% 2.45/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.45/1.03  
% 2.45/1.03  ------  iProver source info
% 2.45/1.03  
% 2.45/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.45/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.45/1.03  git: non_committed_changes: false
% 2.45/1.03  git: last_make_outside_of_git: false
% 2.45/1.03  
% 2.45/1.03  ------ 
% 2.45/1.03  
% 2.45/1.03  ------ Input Options
% 2.45/1.03  
% 2.45/1.03  --out_options                           all
% 2.45/1.03  --tptp_safe_out                         true
% 2.45/1.03  --problem_path                          ""
% 2.45/1.03  --include_path                          ""
% 2.45/1.03  --clausifier                            res/vclausify_rel
% 2.45/1.03  --clausifier_options                    --mode clausify
% 2.45/1.03  --stdin                                 false
% 2.45/1.03  --stats_out                             all
% 2.45/1.03  
% 2.45/1.03  ------ General Options
% 2.45/1.03  
% 2.45/1.03  --fof                                   false
% 2.45/1.03  --time_out_real                         305.
% 2.45/1.03  --time_out_virtual                      -1.
% 2.45/1.03  --symbol_type_check                     false
% 2.45/1.03  --clausify_out                          false
% 2.45/1.03  --sig_cnt_out                           false
% 2.45/1.03  --trig_cnt_out                          false
% 2.45/1.03  --trig_cnt_out_tolerance                1.
% 2.45/1.03  --trig_cnt_out_sk_spl                   false
% 2.45/1.03  --abstr_cl_out                          false
% 2.45/1.03  
% 2.45/1.03  ------ Global Options
% 2.45/1.03  
% 2.45/1.03  --schedule                              default
% 2.45/1.03  --add_important_lit                     false
% 2.45/1.03  --prop_solver_per_cl                    1000
% 2.45/1.03  --min_unsat_core                        false
% 2.45/1.03  --soft_assumptions                      false
% 2.45/1.03  --soft_lemma_size                       3
% 2.45/1.03  --prop_impl_unit_size                   0
% 2.45/1.03  --prop_impl_unit                        []
% 2.45/1.03  --share_sel_clauses                     true
% 2.45/1.03  --reset_solvers                         false
% 2.45/1.03  --bc_imp_inh                            [conj_cone]
% 2.45/1.03  --conj_cone_tolerance                   3.
% 2.45/1.03  --extra_neg_conj                        none
% 2.45/1.03  --large_theory_mode                     true
% 2.45/1.03  --prolific_symb_bound                   200
% 2.45/1.03  --lt_threshold                          2000
% 2.45/1.03  --clause_weak_htbl                      true
% 2.45/1.03  --gc_record_bc_elim                     false
% 2.45/1.03  
% 2.45/1.03  ------ Preprocessing Options
% 2.45/1.03  
% 2.45/1.03  --preprocessing_flag                    true
% 2.45/1.03  --time_out_prep_mult                    0.1
% 2.45/1.03  --splitting_mode                        input
% 2.45/1.03  --splitting_grd                         true
% 2.45/1.03  --splitting_cvd                         false
% 2.45/1.03  --splitting_cvd_svl                     false
% 2.45/1.03  --splitting_nvd                         32
% 2.45/1.03  --sub_typing                            true
% 2.45/1.03  --prep_gs_sim                           true
% 2.45/1.03  --prep_unflatten                        true
% 2.45/1.03  --prep_res_sim                          true
% 2.45/1.03  --prep_upred                            true
% 2.45/1.03  --prep_sem_filter                       exhaustive
% 2.45/1.03  --prep_sem_filter_out                   false
% 2.45/1.03  --pred_elim                             true
% 2.45/1.03  --res_sim_input                         true
% 2.45/1.03  --eq_ax_congr_red                       true
% 2.45/1.03  --pure_diseq_elim                       true
% 2.45/1.03  --brand_transform                       false
% 2.45/1.03  --non_eq_to_eq                          false
% 2.45/1.03  --prep_def_merge                        true
% 2.45/1.03  --prep_def_merge_prop_impl              false
% 2.45/1.03  --prep_def_merge_mbd                    true
% 2.45/1.03  --prep_def_merge_tr_red                 false
% 2.45/1.03  --prep_def_merge_tr_cl                  false
% 2.45/1.03  --smt_preprocessing                     true
% 2.45/1.03  --smt_ac_axioms                         fast
% 2.45/1.03  --preprocessed_out                      false
% 2.45/1.03  --preprocessed_stats                    false
% 2.45/1.03  
% 2.45/1.03  ------ Abstraction refinement Options
% 2.45/1.03  
% 2.45/1.03  --abstr_ref                             []
% 2.45/1.03  --abstr_ref_prep                        false
% 2.45/1.03  --abstr_ref_until_sat                   false
% 2.45/1.03  --abstr_ref_sig_restrict                funpre
% 2.45/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.45/1.03  --abstr_ref_under                       []
% 2.45/1.03  
% 2.45/1.03  ------ SAT Options
% 2.45/1.03  
% 2.45/1.03  --sat_mode                              false
% 2.45/1.03  --sat_fm_restart_options                ""
% 2.45/1.03  --sat_gr_def                            false
% 2.45/1.03  --sat_epr_types                         true
% 2.45/1.03  --sat_non_cyclic_types                  false
% 2.45/1.03  --sat_finite_models                     false
% 2.45/1.03  --sat_fm_lemmas                         false
% 2.45/1.03  --sat_fm_prep                           false
% 2.45/1.03  --sat_fm_uc_incr                        true
% 2.45/1.03  --sat_out_model                         small
% 2.45/1.03  --sat_out_clauses                       false
% 2.45/1.03  
% 2.45/1.03  ------ QBF Options
% 2.45/1.03  
% 2.45/1.03  --qbf_mode                              false
% 2.45/1.03  --qbf_elim_univ                         false
% 2.45/1.03  --qbf_dom_inst                          none
% 2.45/1.03  --qbf_dom_pre_inst                      false
% 2.45/1.03  --qbf_sk_in                             false
% 2.45/1.03  --qbf_pred_elim                         true
% 2.45/1.03  --qbf_split                             512
% 2.45/1.03  
% 2.45/1.03  ------ BMC1 Options
% 2.45/1.03  
% 2.45/1.03  --bmc1_incremental                      false
% 2.45/1.03  --bmc1_axioms                           reachable_all
% 2.45/1.03  --bmc1_min_bound                        0
% 2.45/1.03  --bmc1_max_bound                        -1
% 2.45/1.03  --bmc1_max_bound_default                -1
% 2.45/1.03  --bmc1_symbol_reachability              true
% 2.45/1.03  --bmc1_property_lemmas                  false
% 2.45/1.03  --bmc1_k_induction                      false
% 2.45/1.03  --bmc1_non_equiv_states                 false
% 2.45/1.03  --bmc1_deadlock                         false
% 2.45/1.03  --bmc1_ucm                              false
% 2.45/1.03  --bmc1_add_unsat_core                   none
% 2.45/1.03  --bmc1_unsat_core_children              false
% 2.45/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.45/1.03  --bmc1_out_stat                         full
% 2.45/1.03  --bmc1_ground_init                      false
% 2.45/1.03  --bmc1_pre_inst_next_state              false
% 2.45/1.03  --bmc1_pre_inst_state                   false
% 2.45/1.03  --bmc1_pre_inst_reach_state             false
% 2.45/1.03  --bmc1_out_unsat_core                   false
% 2.45/1.03  --bmc1_aig_witness_out                  false
% 2.45/1.03  --bmc1_verbose                          false
% 2.45/1.03  --bmc1_dump_clauses_tptp                false
% 2.45/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.45/1.03  --bmc1_dump_file                        -
% 2.45/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.45/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.45/1.03  --bmc1_ucm_extend_mode                  1
% 2.45/1.03  --bmc1_ucm_init_mode                    2
% 2.45/1.03  --bmc1_ucm_cone_mode                    none
% 2.45/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.45/1.03  --bmc1_ucm_relax_model                  4
% 2.45/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.45/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.45/1.03  --bmc1_ucm_layered_model                none
% 2.45/1.03  --bmc1_ucm_max_lemma_size               10
% 2.45/1.03  
% 2.45/1.03  ------ AIG Options
% 2.45/1.03  
% 2.45/1.03  --aig_mode                              false
% 2.45/1.03  
% 2.45/1.03  ------ Instantiation Options
% 2.45/1.03  
% 2.45/1.03  --instantiation_flag                    true
% 2.45/1.03  --inst_sos_flag                         false
% 2.45/1.03  --inst_sos_phase                        true
% 2.45/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.45/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.45/1.03  --inst_lit_sel_side                     num_symb
% 2.45/1.03  --inst_solver_per_active                1400
% 2.45/1.03  --inst_solver_calls_frac                1.
% 2.45/1.03  --inst_passive_queue_type               priority_queues
% 2.45/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.45/1.03  --inst_passive_queues_freq              [25;2]
% 2.45/1.03  --inst_dismatching                      true
% 2.45/1.03  --inst_eager_unprocessed_to_passive     true
% 2.45/1.03  --inst_prop_sim_given                   true
% 2.45/1.03  --inst_prop_sim_new                     false
% 2.45/1.03  --inst_subs_new                         false
% 2.45/1.03  --inst_eq_res_simp                      false
% 2.45/1.03  --inst_subs_given                       false
% 2.45/1.03  --inst_orphan_elimination               true
% 2.45/1.03  --inst_learning_loop_flag               true
% 2.45/1.03  --inst_learning_start                   3000
% 2.45/1.03  --inst_learning_factor                  2
% 2.45/1.03  --inst_start_prop_sim_after_learn       3
% 2.45/1.03  --inst_sel_renew                        solver
% 2.45/1.03  --inst_lit_activity_flag                true
% 2.45/1.03  --inst_restr_to_given                   false
% 2.45/1.03  --inst_activity_threshold               500
% 2.45/1.03  --inst_out_proof                        true
% 2.45/1.03  
% 2.45/1.03  ------ Resolution Options
% 2.45/1.03  
% 2.45/1.03  --resolution_flag                       true
% 2.45/1.03  --res_lit_sel                           adaptive
% 2.45/1.03  --res_lit_sel_side                      none
% 2.45/1.03  --res_ordering                          kbo
% 2.45/1.03  --res_to_prop_solver                    active
% 2.45/1.03  --res_prop_simpl_new                    false
% 2.45/1.03  --res_prop_simpl_given                  true
% 2.45/1.03  --res_passive_queue_type                priority_queues
% 2.45/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.45/1.03  --res_passive_queues_freq               [15;5]
% 2.45/1.03  --res_forward_subs                      full
% 2.45/1.03  --res_backward_subs                     full
% 2.45/1.03  --res_forward_subs_resolution           true
% 2.45/1.03  --res_backward_subs_resolution          true
% 2.45/1.03  --res_orphan_elimination                true
% 2.45/1.03  --res_time_limit                        2.
% 2.45/1.03  --res_out_proof                         true
% 2.45/1.03  
% 2.45/1.03  ------ Superposition Options
% 2.45/1.03  
% 2.45/1.03  --superposition_flag                    true
% 2.45/1.03  --sup_passive_queue_type                priority_queues
% 2.45/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.45/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.45/1.03  --demod_completeness_check              fast
% 2.45/1.03  --demod_use_ground                      true
% 2.45/1.03  --sup_to_prop_solver                    passive
% 2.45/1.03  --sup_prop_simpl_new                    true
% 2.45/1.03  --sup_prop_simpl_given                  true
% 2.45/1.03  --sup_fun_splitting                     false
% 2.45/1.03  --sup_smt_interval                      50000
% 2.45/1.03  
% 2.45/1.03  ------ Superposition Simplification Setup
% 2.45/1.03  
% 2.45/1.03  --sup_indices_passive                   []
% 2.45/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.45/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.03  --sup_full_bw                           [BwDemod]
% 2.45/1.03  --sup_immed_triv                        [TrivRules]
% 2.45/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.45/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.03  --sup_immed_bw_main                     []
% 2.45/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.45/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/1.03  
% 2.45/1.03  ------ Combination Options
% 2.45/1.03  
% 2.45/1.03  --comb_res_mult                         3
% 2.45/1.03  --comb_sup_mult                         2
% 2.45/1.03  --comb_inst_mult                        10
% 2.45/1.03  
% 2.45/1.03  ------ Debug Options
% 2.45/1.03  
% 2.45/1.03  --dbg_backtrace                         false
% 2.45/1.03  --dbg_dump_prop_clauses                 false
% 2.45/1.03  --dbg_dump_prop_clauses_file            -
% 2.45/1.03  --dbg_out_stat                          false
% 2.45/1.03  ------ Parsing...
% 2.45/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.45/1.03  
% 2.45/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.45/1.03  
% 2.45/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.45/1.03  
% 2.45/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.45/1.03  ------ Proving...
% 2.45/1.03  ------ Problem Properties 
% 2.45/1.03  
% 2.45/1.03  
% 2.45/1.03  clauses                                 17
% 2.45/1.03  conjectures                             2
% 2.45/1.03  EPR                                     2
% 2.45/1.03  Horn                                    17
% 2.45/1.03  unary                                   3
% 2.45/1.03  binary                                  8
% 2.45/1.03  lits                                    38
% 2.45/1.03  lits eq                                 2
% 2.45/1.03  fd_pure                                 0
% 2.45/1.03  fd_pseudo                               0
% 2.45/1.03  fd_cond                                 0
% 2.45/1.03  fd_pseudo_cond                          0
% 2.45/1.03  AC symbols                              0
% 2.45/1.03  
% 2.45/1.03  ------ Schedule dynamic 5 is on 
% 2.45/1.03  
% 2.45/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.45/1.03  
% 2.45/1.03  
% 2.45/1.03  ------ 
% 2.45/1.03  Current options:
% 2.45/1.03  ------ 
% 2.45/1.03  
% 2.45/1.03  ------ Input Options
% 2.45/1.03  
% 2.45/1.03  --out_options                           all
% 2.45/1.03  --tptp_safe_out                         true
% 2.45/1.03  --problem_path                          ""
% 2.45/1.03  --include_path                          ""
% 2.45/1.03  --clausifier                            res/vclausify_rel
% 2.45/1.03  --clausifier_options                    --mode clausify
% 2.45/1.03  --stdin                                 false
% 2.45/1.03  --stats_out                             all
% 2.45/1.03  
% 2.45/1.03  ------ General Options
% 2.45/1.03  
% 2.45/1.03  --fof                                   false
% 2.45/1.03  --time_out_real                         305.
% 2.45/1.03  --time_out_virtual                      -1.
% 2.45/1.03  --symbol_type_check                     false
% 2.45/1.03  --clausify_out                          false
% 2.45/1.03  --sig_cnt_out                           false
% 2.45/1.03  --trig_cnt_out                          false
% 2.45/1.03  --trig_cnt_out_tolerance                1.
% 2.45/1.03  --trig_cnt_out_sk_spl                   false
% 2.45/1.03  --abstr_cl_out                          false
% 2.45/1.03  
% 2.45/1.03  ------ Global Options
% 2.45/1.03  
% 2.45/1.03  --schedule                              default
% 2.45/1.03  --add_important_lit                     false
% 2.45/1.03  --prop_solver_per_cl                    1000
% 2.45/1.03  --min_unsat_core                        false
% 2.45/1.03  --soft_assumptions                      false
% 2.45/1.03  --soft_lemma_size                       3
% 2.45/1.03  --prop_impl_unit_size                   0
% 2.45/1.03  --prop_impl_unit                        []
% 2.45/1.03  --share_sel_clauses                     true
% 2.45/1.03  --reset_solvers                         false
% 2.45/1.03  --bc_imp_inh                            [conj_cone]
% 2.45/1.03  --conj_cone_tolerance                   3.
% 2.45/1.03  --extra_neg_conj                        none
% 2.45/1.03  --large_theory_mode                     true
% 2.45/1.03  --prolific_symb_bound                   200
% 2.45/1.03  --lt_threshold                          2000
% 2.45/1.03  --clause_weak_htbl                      true
% 2.45/1.03  --gc_record_bc_elim                     false
% 2.45/1.03  
% 2.45/1.03  ------ Preprocessing Options
% 2.45/1.03  
% 2.45/1.03  --preprocessing_flag                    true
% 2.45/1.03  --time_out_prep_mult                    0.1
% 2.45/1.03  --splitting_mode                        input
% 2.45/1.03  --splitting_grd                         true
% 2.45/1.03  --splitting_cvd                         false
% 2.45/1.03  --splitting_cvd_svl                     false
% 2.45/1.03  --splitting_nvd                         32
% 2.45/1.03  --sub_typing                            true
% 2.45/1.03  --prep_gs_sim                           true
% 2.45/1.03  --prep_unflatten                        true
% 2.45/1.03  --prep_res_sim                          true
% 2.45/1.03  --prep_upred                            true
% 2.45/1.03  --prep_sem_filter                       exhaustive
% 2.45/1.03  --prep_sem_filter_out                   false
% 2.45/1.03  --pred_elim                             true
% 2.45/1.03  --res_sim_input                         true
% 2.45/1.03  --eq_ax_congr_red                       true
% 2.45/1.03  --pure_diseq_elim                       true
% 2.45/1.03  --brand_transform                       false
% 2.45/1.03  --non_eq_to_eq                          false
% 2.45/1.03  --prep_def_merge                        true
% 2.45/1.03  --prep_def_merge_prop_impl              false
% 2.45/1.03  --prep_def_merge_mbd                    true
% 2.45/1.03  --prep_def_merge_tr_red                 false
% 2.45/1.03  --prep_def_merge_tr_cl                  false
% 2.45/1.03  --smt_preprocessing                     true
% 2.45/1.03  --smt_ac_axioms                         fast
% 2.45/1.03  --preprocessed_out                      false
% 2.45/1.03  --preprocessed_stats                    false
% 2.45/1.03  
% 2.45/1.03  ------ Abstraction refinement Options
% 2.45/1.03  
% 2.45/1.03  --abstr_ref                             []
% 2.45/1.03  --abstr_ref_prep                        false
% 2.45/1.03  --abstr_ref_until_sat                   false
% 2.45/1.03  --abstr_ref_sig_restrict                funpre
% 2.45/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.45/1.03  --abstr_ref_under                       []
% 2.45/1.03  
% 2.45/1.03  ------ SAT Options
% 2.45/1.03  
% 2.45/1.03  --sat_mode                              false
% 2.45/1.03  --sat_fm_restart_options                ""
% 2.45/1.03  --sat_gr_def                            false
% 2.45/1.03  --sat_epr_types                         true
% 2.45/1.03  --sat_non_cyclic_types                  false
% 2.45/1.03  --sat_finite_models                     false
% 2.45/1.03  --sat_fm_lemmas                         false
% 2.45/1.03  --sat_fm_prep                           false
% 2.45/1.03  --sat_fm_uc_incr                        true
% 2.45/1.03  --sat_out_model                         small
% 2.45/1.03  --sat_out_clauses                       false
% 2.45/1.03  
% 2.45/1.03  ------ QBF Options
% 2.45/1.03  
% 2.45/1.03  --qbf_mode                              false
% 2.45/1.03  --qbf_elim_univ                         false
% 2.45/1.03  --qbf_dom_inst                          none
% 2.45/1.03  --qbf_dom_pre_inst                      false
% 2.45/1.03  --qbf_sk_in                             false
% 2.45/1.03  --qbf_pred_elim                         true
% 2.45/1.03  --qbf_split                             512
% 2.45/1.03  
% 2.45/1.03  ------ BMC1 Options
% 2.45/1.03  
% 2.45/1.03  --bmc1_incremental                      false
% 2.45/1.03  --bmc1_axioms                           reachable_all
% 2.45/1.03  --bmc1_min_bound                        0
% 2.45/1.03  --bmc1_max_bound                        -1
% 2.45/1.03  --bmc1_max_bound_default                -1
% 2.45/1.03  --bmc1_symbol_reachability              true
% 2.45/1.03  --bmc1_property_lemmas                  false
% 2.45/1.03  --bmc1_k_induction                      false
% 2.45/1.03  --bmc1_non_equiv_states                 false
% 2.45/1.03  --bmc1_deadlock                         false
% 2.45/1.03  --bmc1_ucm                              false
% 2.45/1.03  --bmc1_add_unsat_core                   none
% 2.45/1.03  --bmc1_unsat_core_children              false
% 2.45/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.45/1.03  --bmc1_out_stat                         full
% 2.45/1.03  --bmc1_ground_init                      false
% 2.45/1.03  --bmc1_pre_inst_next_state              false
% 2.45/1.03  --bmc1_pre_inst_state                   false
% 2.45/1.03  --bmc1_pre_inst_reach_state             false
% 2.45/1.03  --bmc1_out_unsat_core                   false
% 2.45/1.03  --bmc1_aig_witness_out                  false
% 2.45/1.03  --bmc1_verbose                          false
% 2.45/1.03  --bmc1_dump_clauses_tptp                false
% 2.45/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.45/1.03  --bmc1_dump_file                        -
% 2.45/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.45/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.45/1.03  --bmc1_ucm_extend_mode                  1
% 2.45/1.03  --bmc1_ucm_init_mode                    2
% 2.45/1.03  --bmc1_ucm_cone_mode                    none
% 2.45/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.45/1.03  --bmc1_ucm_relax_model                  4
% 2.45/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.45/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.45/1.03  --bmc1_ucm_layered_model                none
% 2.45/1.03  --bmc1_ucm_max_lemma_size               10
% 2.45/1.03  
% 2.45/1.03  ------ AIG Options
% 2.45/1.03  
% 2.45/1.03  --aig_mode                              false
% 2.45/1.03  
% 2.45/1.03  ------ Instantiation Options
% 2.45/1.03  
% 2.45/1.03  --instantiation_flag                    true
% 2.45/1.03  --inst_sos_flag                         false
% 2.45/1.03  --inst_sos_phase                        true
% 2.45/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.45/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.45/1.03  --inst_lit_sel_side                     none
% 2.45/1.03  --inst_solver_per_active                1400
% 2.45/1.03  --inst_solver_calls_frac                1.
% 2.45/1.03  --inst_passive_queue_type               priority_queues
% 2.45/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.45/1.03  --inst_passive_queues_freq              [25;2]
% 2.45/1.03  --inst_dismatching                      true
% 2.45/1.03  --inst_eager_unprocessed_to_passive     true
% 2.45/1.03  --inst_prop_sim_given                   true
% 2.45/1.03  --inst_prop_sim_new                     false
% 2.45/1.03  --inst_subs_new                         false
% 2.45/1.03  --inst_eq_res_simp                      false
% 2.45/1.03  --inst_subs_given                       false
% 2.45/1.03  --inst_orphan_elimination               true
% 2.45/1.03  --inst_learning_loop_flag               true
% 2.45/1.03  --inst_learning_start                   3000
% 2.45/1.03  --inst_learning_factor                  2
% 2.45/1.03  --inst_start_prop_sim_after_learn       3
% 2.45/1.03  --inst_sel_renew                        solver
% 2.45/1.03  --inst_lit_activity_flag                true
% 2.45/1.03  --inst_restr_to_given                   false
% 2.45/1.03  --inst_activity_threshold               500
% 2.45/1.03  --inst_out_proof                        true
% 2.45/1.03  
% 2.45/1.03  ------ Resolution Options
% 2.45/1.03  
% 2.45/1.03  --resolution_flag                       false
% 2.45/1.03  --res_lit_sel                           adaptive
% 2.45/1.03  --res_lit_sel_side                      none
% 2.45/1.03  --res_ordering                          kbo
% 2.45/1.03  --res_to_prop_solver                    active
% 2.45/1.03  --res_prop_simpl_new                    false
% 2.45/1.03  --res_prop_simpl_given                  true
% 2.45/1.03  --res_passive_queue_type                priority_queues
% 2.45/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.45/1.03  --res_passive_queues_freq               [15;5]
% 2.45/1.03  --res_forward_subs                      full
% 2.45/1.03  --res_backward_subs                     full
% 2.45/1.03  --res_forward_subs_resolution           true
% 2.45/1.03  --res_backward_subs_resolution          true
% 2.45/1.03  --res_orphan_elimination                true
% 2.45/1.03  --res_time_limit                        2.
% 2.45/1.03  --res_out_proof                         true
% 2.45/1.03  
% 2.45/1.03  ------ Superposition Options
% 2.45/1.03  
% 2.45/1.03  --superposition_flag                    true
% 2.45/1.03  --sup_passive_queue_type                priority_queues
% 2.45/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.45/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.45/1.03  --demod_completeness_check              fast
% 2.45/1.03  --demod_use_ground                      true
% 2.45/1.03  --sup_to_prop_solver                    passive
% 2.45/1.03  --sup_prop_simpl_new                    true
% 2.45/1.03  --sup_prop_simpl_given                  true
% 2.45/1.03  --sup_fun_splitting                     false
% 2.45/1.03  --sup_smt_interval                      50000
% 2.45/1.03  
% 2.45/1.03  ------ Superposition Simplification Setup
% 2.45/1.03  
% 2.45/1.03  --sup_indices_passive                   []
% 2.45/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.45/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.03  --sup_full_bw                           [BwDemod]
% 2.45/1.03  --sup_immed_triv                        [TrivRules]
% 2.45/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.45/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.03  --sup_immed_bw_main                     []
% 2.45/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.45/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/1.03  
% 2.45/1.03  ------ Combination Options
% 2.45/1.03  
% 2.45/1.03  --comb_res_mult                         3
% 2.45/1.03  --comb_sup_mult                         2
% 2.45/1.03  --comb_inst_mult                        10
% 2.45/1.03  
% 2.45/1.03  ------ Debug Options
% 2.45/1.03  
% 2.45/1.03  --dbg_backtrace                         false
% 2.45/1.03  --dbg_dump_prop_clauses                 false
% 2.45/1.03  --dbg_dump_prop_clauses_file            -
% 2.45/1.03  --dbg_out_stat                          false
% 2.45/1.03  
% 2.45/1.03  
% 2.45/1.03  
% 2.45/1.03  
% 2.45/1.03  ------ Proving...
% 2.45/1.03  
% 2.45/1.03  
% 2.45/1.03  % SZS status Theorem for theBenchmark.p
% 2.45/1.03  
% 2.45/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.45/1.03  
% 2.45/1.03  fof(f6,axiom,(
% 2.45/1.03    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 2.45/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.03  
% 2.45/1.03  fof(f21,plain,(
% 2.45/1.03    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 2.45/1.03    inference(ennf_transformation,[],[f6])).
% 2.45/1.03  
% 2.45/1.03  fof(f41,plain,(
% 2.45/1.03    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 2.45/1.03    inference(cnf_transformation,[],[f21])).
% 2.45/1.03  
% 2.45/1.03  fof(f7,axiom,(
% 2.45/1.03    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)))),
% 2.45/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.03  
% 2.45/1.03  fof(f22,plain,(
% 2.45/1.03    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.45/1.03    inference(ennf_transformation,[],[f7])).
% 2.45/1.03  
% 2.45/1.03  fof(f42,plain,(
% 2.45/1.03    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.45/1.03    inference(cnf_transformation,[],[f22])).
% 2.45/1.03  
% 2.45/1.03  fof(f13,conjecture,(
% 2.45/1.03    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 2.45/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.03  
% 2.45/1.03  fof(f14,negated_conjecture,(
% 2.45/1.03    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 2.45/1.03    inference(negated_conjecture,[],[f13])).
% 2.45/1.03  
% 2.45/1.03  fof(f29,plain,(
% 2.45/1.03    ? [X0,X1,X2,X3] : (~m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 2.45/1.03    inference(ennf_transformation,[],[f14])).
% 2.45/1.03  
% 2.45/1.03  fof(f31,plain,(
% 2.45/1.03    ? [X0,X1,X2,X3] : (~m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) => (~m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))))),
% 2.45/1.03    introduced(choice_axiom,[])).
% 2.45/1.03  
% 2.45/1.03  fof(f32,plain,(
% 2.45/1.03    ~m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 2.45/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f31])).
% 2.45/1.03  
% 2.45/1.03  fof(f48,plain,(
% 2.45/1.03    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 2.45/1.03    inference(cnf_transformation,[],[f32])).
% 2.45/1.03  
% 2.45/1.03  fof(f10,axiom,(
% 2.45/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.45/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.03  
% 2.45/1.03  fof(f25,plain,(
% 2.45/1.03    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.45/1.03    inference(ennf_transformation,[],[f10])).
% 2.45/1.03  
% 2.45/1.03  fof(f45,plain,(
% 2.45/1.03    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.45/1.03    inference(cnf_transformation,[],[f25])).
% 2.45/1.03  
% 2.45/1.03  fof(f9,axiom,(
% 2.45/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 2.45/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.03  
% 2.45/1.03  fof(f24,plain,(
% 2.45/1.03    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.45/1.03    inference(ennf_transformation,[],[f9])).
% 2.45/1.03  
% 2.45/1.03  fof(f44,plain,(
% 2.45/1.03    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.45/1.03    inference(cnf_transformation,[],[f24])).
% 2.45/1.03  
% 2.45/1.03  fof(f2,axiom,(
% 2.45/1.03    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.45/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.03  
% 2.45/1.03  fof(f30,plain,(
% 2.45/1.03    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.45/1.03    inference(nnf_transformation,[],[f2])).
% 2.45/1.03  
% 2.45/1.03  fof(f34,plain,(
% 2.45/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.45/1.03    inference(cnf_transformation,[],[f30])).
% 2.45/1.03  
% 2.45/1.03  fof(f1,axiom,(
% 2.45/1.03    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.45/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.03  
% 2.45/1.03  fof(f16,plain,(
% 2.45/1.03    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.45/1.03    inference(ennf_transformation,[],[f1])).
% 2.45/1.03  
% 2.45/1.03  fof(f17,plain,(
% 2.45/1.03    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.45/1.03    inference(flattening,[],[f16])).
% 2.45/1.03  
% 2.45/1.03  fof(f33,plain,(
% 2.45/1.03    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.45/1.03    inference(cnf_transformation,[],[f17])).
% 2.45/1.03  
% 2.45/1.03  fof(f3,axiom,(
% 2.45/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.45/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.03  
% 2.45/1.03  fof(f18,plain,(
% 2.45/1.03    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.45/1.03    inference(ennf_transformation,[],[f3])).
% 2.45/1.03  
% 2.45/1.03  fof(f36,plain,(
% 2.45/1.03    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.45/1.03    inference(cnf_transformation,[],[f18])).
% 2.45/1.03  
% 2.45/1.03  fof(f35,plain,(
% 2.45/1.03    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.45/1.03    inference(cnf_transformation,[],[f30])).
% 2.45/1.03  
% 2.45/1.03  fof(f5,axiom,(
% 2.45/1.03    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.45/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.03  
% 2.45/1.03  fof(f40,plain,(
% 2.45/1.03    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.45/1.03    inference(cnf_transformation,[],[f5])).
% 2.45/1.03  
% 2.45/1.03  fof(f12,axiom,(
% 2.45/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.45/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.03  
% 2.45/1.03  fof(f27,plain,(
% 2.45/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 2.45/1.03    inference(ennf_transformation,[],[f12])).
% 2.45/1.03  
% 2.45/1.03  fof(f28,plain,(
% 2.45/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 2.45/1.03    inference(flattening,[],[f27])).
% 2.45/1.03  
% 2.45/1.03  fof(f47,plain,(
% 2.45/1.03    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 2.45/1.03    inference(cnf_transformation,[],[f28])).
% 2.45/1.03  
% 2.45/1.03  fof(f11,axiom,(
% 2.45/1.03    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3))),
% 2.45/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.03  
% 2.45/1.03  fof(f26,plain,(
% 2.45/1.03    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.45/1.03    inference(ennf_transformation,[],[f11])).
% 2.45/1.03  
% 2.45/1.03  fof(f46,plain,(
% 2.45/1.03    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.45/1.03    inference(cnf_transformation,[],[f26])).
% 2.45/1.03  
% 2.45/1.03  fof(f49,plain,(
% 2.45/1.03    ~m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.45/1.03    inference(cnf_transformation,[],[f32])).
% 2.45/1.03  
% 2.45/1.03  fof(f8,axiom,(
% 2.45/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.45/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.03  
% 2.45/1.03  fof(f15,plain,(
% 2.45/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.45/1.03    inference(pure_predicate_removal,[],[f8])).
% 2.45/1.03  
% 2.45/1.03  fof(f23,plain,(
% 2.45/1.03    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.45/1.03    inference(ennf_transformation,[],[f15])).
% 2.45/1.03  
% 2.45/1.03  fof(f43,plain,(
% 2.45/1.03    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.45/1.03    inference(cnf_transformation,[],[f23])).
% 2.45/1.03  
% 2.45/1.03  fof(f4,axiom,(
% 2.45/1.03    ! [X0,X1,X2] : ((v4_relat_1(X2,X1) & v1_relat_1(X2)) => (v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))))),
% 2.45/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.03  
% 2.45/1.03  fof(f19,plain,(
% 2.45/1.03    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | (~v4_relat_1(X2,X1) | ~v1_relat_1(X2)))),
% 2.45/1.03    inference(ennf_transformation,[],[f4])).
% 2.45/1.03  
% 2.45/1.03  fof(f20,plain,(
% 2.45/1.03    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2))),
% 2.45/1.03    inference(flattening,[],[f19])).
% 2.45/1.03  
% 2.45/1.03  fof(f37,plain,(
% 2.45/1.03    ( ! [X2,X0,X1] : (v1_relat_1(k7_relat_1(X2,X0)) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 2.45/1.03    inference(cnf_transformation,[],[f20])).
% 2.45/1.03  
% 2.45/1.03  cnf(c_8,plain,
% 2.45/1.03      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 2.45/1.03      inference(cnf_transformation,[],[f41]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_239,plain,
% 2.45/1.03      ( r1_tarski(k1_relat_1(k7_relat_1(X0_43,X1_43)),X1_43)
% 2.45/1.03      | ~ v1_relat_1(X0_43) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_8]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_698,plain,
% 2.45/1.03      ( r1_tarski(k1_relat_1(k7_relat_1(X0_43,X1_43)),X1_43) = iProver_top
% 2.45/1.03      | v1_relat_1(X0_43) != iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_239]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_9,plain,
% 2.45/1.03      ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0))
% 2.45/1.03      | ~ v1_relat_1(X0) ),
% 2.45/1.03      inference(cnf_transformation,[],[f42]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_238,plain,
% 2.45/1.03      ( r1_tarski(k2_relat_1(k7_relat_1(X0_43,X1_43)),k2_relat_1(X0_43))
% 2.45/1.03      | ~ v1_relat_1(X0_43) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_9]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_699,plain,
% 2.45/1.03      ( r1_tarski(k2_relat_1(k7_relat_1(X0_43,X1_43)),k2_relat_1(X0_43)) = iProver_top
% 2.45/1.03      | v1_relat_1(X0_43) != iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_238]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_16,negated_conjecture,
% 2.45/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 2.45/1.03      inference(cnf_transformation,[],[f48]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_231,negated_conjecture,
% 2.45/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_16]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_706,plain,
% 2.45/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_231]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_12,plain,
% 2.45/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.45/1.03      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.45/1.03      inference(cnf_transformation,[],[f45]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_235,plain,
% 2.45/1.03      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43)))
% 2.45/1.03      | k2_relset_1(X1_43,X2_43,X0_43) = k2_relat_1(X0_43) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_12]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_702,plain,
% 2.45/1.03      ( k2_relset_1(X0_43,X1_43,X2_43) = k2_relat_1(X2_43)
% 2.45/1.03      | m1_subset_1(X2_43,k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43))) != iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_235]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1170,plain,
% 2.45/1.03      ( k2_relset_1(sK0,sK2,sK3) = k2_relat_1(sK3) ),
% 2.45/1.03      inference(superposition,[status(thm)],[c_706,c_702]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_11,plain,
% 2.45/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.45/1.03      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 2.45/1.03      inference(cnf_transformation,[],[f44]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_236,plain,
% 2.45/1.03      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43)))
% 2.45/1.03      | m1_subset_1(k2_relset_1(X1_43,X2_43,X0_43),k1_zfmisc_1(X2_43)) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_11]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_701,plain,
% 2.45/1.03      ( m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43))) != iProver_top
% 2.45/1.03      | m1_subset_1(k2_relset_1(X1_43,X2_43,X0_43),k1_zfmisc_1(X2_43)) = iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_236]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1802,plain,
% 2.45/1.03      ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top
% 2.45/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 2.45/1.03      inference(superposition,[status(thm)],[c_1170,c_701]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_17,plain,
% 2.45/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3037,plain,
% 2.45/1.03      ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top ),
% 2.45/1.03      inference(global_propositional_subsumption,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_1802,c_17]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_2,plain,
% 2.45/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.45/1.03      inference(cnf_transformation,[],[f34]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_244,plain,
% 2.45/1.03      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
% 2.45/1.03      | r1_tarski(X0_43,X1_43) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_2]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_693,plain,
% 2.45/1.03      ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) != iProver_top
% 2.45/1.03      | r1_tarski(X0_43,X1_43) = iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_244]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3042,plain,
% 2.45/1.03      ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
% 2.45/1.03      inference(superposition,[status(thm)],[c_3037,c_693]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_0,plain,
% 2.45/1.03      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 2.45/1.03      inference(cnf_transformation,[],[f33]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_246,plain,
% 2.45/1.03      ( ~ r1_tarski(X0_43,X1_43)
% 2.45/1.03      | ~ r1_tarski(X2_43,X0_43)
% 2.45/1.03      | r1_tarski(X2_43,X1_43) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_0]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_691,plain,
% 2.45/1.03      ( r1_tarski(X0_43,X1_43) != iProver_top
% 2.45/1.03      | r1_tarski(X2_43,X0_43) != iProver_top
% 2.45/1.03      | r1_tarski(X2_43,X1_43) = iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_246]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3214,plain,
% 2.45/1.03      ( r1_tarski(X0_43,k2_relat_1(sK3)) != iProver_top
% 2.45/1.03      | r1_tarski(X0_43,sK2) = iProver_top ),
% 2.45/1.03      inference(superposition,[status(thm)],[c_3042,c_691]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3521,plain,
% 2.45/1.03      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0_43)),sK2) = iProver_top
% 2.45/1.03      | v1_relat_1(sK3) != iProver_top ),
% 2.45/1.03      inference(superposition,[status(thm)],[c_699,c_3214]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_822,plain,
% 2.45/1.03      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.45/1.03      | r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_244]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_823,plain,
% 2.45/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 2.45/1.03      | r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) = iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_822]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3,plain,
% 2.45/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.45/1.03      | ~ v1_relat_1(X1)
% 2.45/1.03      | v1_relat_1(X0) ),
% 2.45/1.03      inference(cnf_transformation,[],[f36]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1,plain,
% 2.45/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.45/1.03      inference(cnf_transformation,[],[f35]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_136,plain,
% 2.45/1.03      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.45/1.03      inference(prop_impl,[status(thm)],[c_1]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_137,plain,
% 2.45/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.45/1.03      inference(renaming,[status(thm)],[c_136]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_166,plain,
% 2.45/1.03      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.45/1.03      inference(bin_hyper_res,[status(thm)],[c_3,c_137]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_230,plain,
% 2.45/1.03      ( ~ r1_tarski(X0_43,X1_43)
% 2.45/1.03      | ~ v1_relat_1(X1_43)
% 2.45/1.03      | v1_relat_1(X0_43) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_166]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_853,plain,
% 2.45/1.03      ( ~ r1_tarski(X0_43,k2_zfmisc_1(X1_43,X2_43))
% 2.45/1.03      | v1_relat_1(X0_43)
% 2.45/1.03      | ~ v1_relat_1(k2_zfmisc_1(X1_43,X2_43)) ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_230]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_935,plain,
% 2.45/1.03      ( ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))
% 2.45/1.03      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
% 2.45/1.03      | v1_relat_1(sK3) ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_853]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_936,plain,
% 2.45/1.03      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) != iProver_top
% 2.45/1.03      | v1_relat_1(k2_zfmisc_1(sK0,sK2)) != iProver_top
% 2.45/1.03      | v1_relat_1(sK3) = iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_935]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_7,plain,
% 2.45/1.03      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.45/1.03      inference(cnf_transformation,[],[f40]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_240,plain,
% 2.45/1.03      ( v1_relat_1(k2_zfmisc_1(X0_43,X1_43)) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_7]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1019,plain,
% 2.45/1.03      ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) ),
% 2.45/1.03      inference(instantiation,[status(thm)],[c_240]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1020,plain,
% 2.45/1.03      ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) = iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_1019]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3538,plain,
% 2.45/1.03      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0_43)),sK2) = iProver_top ),
% 2.45/1.03      inference(global_propositional_subsumption,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_3521,c_17,c_823,c_936,c_1020]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_14,plain,
% 2.45/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.45/1.03      | ~ r1_tarski(k2_relat_1(X0),X2)
% 2.45/1.03      | ~ r1_tarski(k1_relat_1(X0),X1)
% 2.45/1.03      | ~ v1_relat_1(X0) ),
% 2.45/1.03      inference(cnf_transformation,[],[f47]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_233,plain,
% 2.45/1.03      ( m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43)))
% 2.45/1.03      | ~ r1_tarski(k2_relat_1(X0_43),X2_43)
% 2.45/1.03      | ~ r1_tarski(k1_relat_1(X0_43),X1_43)
% 2.45/1.03      | ~ v1_relat_1(X0_43) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_14]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_704,plain,
% 2.45/1.03      ( m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43))) = iProver_top
% 2.45/1.03      | r1_tarski(k2_relat_1(X0_43),X2_43) != iProver_top
% 2.45/1.03      | r1_tarski(k1_relat_1(X0_43),X1_43) != iProver_top
% 2.45/1.03      | v1_relat_1(X0_43) != iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_233]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_13,plain,
% 2.45/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.45/1.03      | k5_relset_1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 2.45/1.03      inference(cnf_transformation,[],[f46]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_234,plain,
% 2.45/1.03      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43)))
% 2.45/1.03      | k5_relset_1(X1_43,X2_43,X0_43,X3_43) = k7_relat_1(X0_43,X3_43) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_13]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_703,plain,
% 2.45/1.03      ( k5_relset_1(X0_43,X1_43,X2_43,X3_43) = k7_relat_1(X2_43,X3_43)
% 2.45/1.03      | m1_subset_1(X2_43,k1_zfmisc_1(k2_zfmisc_1(X0_43,X1_43))) != iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_234]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_2034,plain,
% 2.45/1.03      ( k5_relset_1(sK0,sK2,sK3,X0_43) = k7_relat_1(sK3,X0_43) ),
% 2.45/1.03      inference(superposition,[status(thm)],[c_706,c_703]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_15,negated_conjecture,
% 2.45/1.03      ( ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.45/1.03      inference(cnf_transformation,[],[f49]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_232,negated_conjecture,
% 2.45/1.03      ( ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_15]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_705,plain,
% 2.45/1.03      ( m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_232]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_2458,plain,
% 2.45/1.03      ( m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 2.45/1.03      inference(demodulation,[status(thm)],[c_2034,c_705]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_2467,plain,
% 2.45/1.03      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2) != iProver_top
% 2.45/1.03      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) != iProver_top
% 2.45/1.03      | v1_relat_1(k7_relat_1(sK3,sK1)) != iProver_top ),
% 2.45/1.03      inference(superposition,[status(thm)],[c_704,c_2458]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_10,plain,
% 2.45/1.03      ( v4_relat_1(X0,X1)
% 2.45/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.45/1.03      inference(cnf_transformation,[],[f43]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_237,plain,
% 2.45/1.03      ( v4_relat_1(X0_43,X1_43)
% 2.45/1.03      | ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43))) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_10]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_700,plain,
% 2.45/1.03      ( v4_relat_1(X0_43,X1_43) = iProver_top
% 2.45/1.03      | m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43))) != iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_237]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1067,plain,
% 2.45/1.03      ( v4_relat_1(sK3,sK0) = iProver_top ),
% 2.45/1.03      inference(superposition,[status(thm)],[c_706,c_700]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_6,plain,
% 2.45/1.03      ( ~ v4_relat_1(X0,X1)
% 2.45/1.03      | ~ v1_relat_1(X0)
% 2.45/1.03      | v1_relat_1(k7_relat_1(X0,X2)) ),
% 2.45/1.03      inference(cnf_transformation,[],[f37]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_241,plain,
% 2.45/1.03      ( ~ v4_relat_1(X0_43,X1_43)
% 2.45/1.03      | ~ v1_relat_1(X0_43)
% 2.45/1.03      | v1_relat_1(k7_relat_1(X0_43,X2_43)) ),
% 2.45/1.03      inference(subtyping,[status(esa)],[c_6]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_696,plain,
% 2.45/1.03      ( v4_relat_1(X0_43,X1_43) != iProver_top
% 2.45/1.03      | v1_relat_1(X0_43) != iProver_top
% 2.45/1.03      | v1_relat_1(k7_relat_1(X0_43,X2_43)) = iProver_top ),
% 2.45/1.03      inference(predicate_to_equality,[status(thm)],[c_241]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1344,plain,
% 2.45/1.03      ( v1_relat_1(k7_relat_1(sK3,X0_43)) = iProver_top
% 2.45/1.03      | v1_relat_1(sK3) != iProver_top ),
% 2.45/1.03      inference(superposition,[status(thm)],[c_1067,c_696]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_1499,plain,
% 2.45/1.03      ( v1_relat_1(k7_relat_1(sK3,X0_43)) = iProver_top ),
% 2.45/1.03      inference(global_propositional_subsumption,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_1344,c_17,c_823,c_936,c_1020]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3048,plain,
% 2.45/1.03      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2) != iProver_top
% 2.45/1.03      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) != iProver_top ),
% 2.45/1.03      inference(forward_subsumption_resolution,
% 2.45/1.03                [status(thm)],
% 2.45/1.03                [c_2467,c_1499]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_3547,plain,
% 2.45/1.03      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) != iProver_top ),
% 2.45/1.03      inference(superposition,[status(thm)],[c_3538,c_3048]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(c_4015,plain,
% 2.45/1.03      ( v1_relat_1(sK3) != iProver_top ),
% 2.45/1.03      inference(superposition,[status(thm)],[c_698,c_3547]) ).
% 2.45/1.03  
% 2.45/1.03  cnf(contradiction,plain,
% 2.45/1.03      ( $false ),
% 2.45/1.03      inference(minisat,[status(thm)],[c_4015,c_1020,c_936,c_823,c_17]) ).
% 2.45/1.03  
% 2.45/1.03  
% 2.45/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.45/1.03  
% 2.45/1.03  ------                               Statistics
% 2.45/1.03  
% 2.45/1.03  ------ General
% 2.45/1.03  
% 2.45/1.03  abstr_ref_over_cycles:                  0
% 2.45/1.03  abstr_ref_under_cycles:                 0
% 2.45/1.03  gc_basic_clause_elim:                   0
% 2.45/1.03  forced_gc_time:                         0
% 2.45/1.03  parsing_time:                           0.01
% 2.45/1.03  unif_index_cands_time:                  0.
% 2.45/1.03  unif_index_add_time:                    0.
% 2.45/1.03  orderings_time:                         0.
% 2.45/1.03  out_proof_time:                         0.017
% 2.45/1.03  total_time:                             0.194
% 2.45/1.03  num_of_symbols:                         48
% 2.45/1.03  num_of_terms:                           6096
% 2.45/1.03  
% 2.45/1.03  ------ Preprocessing
% 2.45/1.03  
% 2.45/1.03  num_of_splits:                          0
% 2.45/1.03  num_of_split_atoms:                     0
% 2.45/1.03  num_of_reused_defs:                     0
% 2.45/1.03  num_eq_ax_congr_red:                    12
% 2.45/1.03  num_of_sem_filtered_clauses:            1
% 2.45/1.03  num_of_subtypes:                        2
% 2.45/1.03  monotx_restored_types:                  0
% 2.45/1.03  sat_num_of_epr_types:                   0
% 2.45/1.03  sat_num_of_non_cyclic_types:            0
% 2.45/1.03  sat_guarded_non_collapsed_types:        0
% 2.45/1.03  num_pure_diseq_elim:                    0
% 2.45/1.03  simp_replaced_by:                       0
% 2.45/1.03  res_preprocessed:                       76
% 2.45/1.03  prep_upred:                             0
% 2.45/1.03  prep_unflattend:                        0
% 2.45/1.03  smt_new_axioms:                         0
% 2.45/1.03  pred_elim_cands:                        4
% 2.45/1.03  pred_elim:                              0
% 2.45/1.03  pred_elim_cl:                           0
% 2.45/1.03  pred_elim_cycles:                       1
% 2.45/1.03  merged_defs:                            6
% 2.45/1.03  merged_defs_ncl:                        0
% 2.45/1.03  bin_hyper_res:                          7
% 2.45/1.03  prep_cycles:                            3
% 2.45/1.03  pred_elim_time:                         0.
% 2.45/1.03  splitting_time:                         0.
% 2.45/1.03  sem_filter_time:                        0.
% 2.45/1.03  monotx_time:                            0.
% 2.45/1.03  subtype_inf_time:                       0.
% 2.45/1.03  
% 2.45/1.03  ------ Problem properties
% 2.45/1.03  
% 2.45/1.03  clauses:                                17
% 2.45/1.03  conjectures:                            2
% 2.45/1.03  epr:                                    2
% 2.45/1.03  horn:                                   17
% 2.45/1.03  ground:                                 2
% 2.45/1.03  unary:                                  3
% 2.45/1.03  binary:                                 8
% 2.45/1.03  lits:                                   38
% 2.45/1.03  lits_eq:                                2
% 2.45/1.03  fd_pure:                                0
% 2.45/1.03  fd_pseudo:                              0
% 2.45/1.03  fd_cond:                                0
% 2.45/1.03  fd_pseudo_cond:                         0
% 2.45/1.03  ac_symbols:                             0
% 2.45/1.03  
% 2.45/1.03  ------ Propositional Solver
% 2.45/1.03  
% 2.45/1.03  prop_solver_calls:                      23
% 2.45/1.03  prop_fast_solver_calls:                 457
% 2.45/1.03  smt_solver_calls:                       0
% 2.45/1.03  smt_fast_solver_calls:                  0
% 2.45/1.03  prop_num_of_clauses:                    1981
% 2.45/1.03  prop_preprocess_simplified:             4638
% 2.45/1.03  prop_fo_subsumed:                       6
% 2.45/1.03  prop_solver_time:                       0.
% 2.45/1.03  smt_solver_time:                        0.
% 2.45/1.03  smt_fast_solver_time:                   0.
% 2.45/1.03  prop_fast_solver_time:                  0.
% 2.45/1.03  prop_unsat_core_time:                   0.
% 2.45/1.03  
% 2.45/1.03  ------ QBF
% 2.45/1.03  
% 2.45/1.03  qbf_q_res:                              0
% 2.45/1.03  qbf_num_tautologies:                    0
% 2.45/1.03  qbf_prep_cycles:                        0
% 2.45/1.03  
% 2.45/1.03  ------ BMC1
% 2.45/1.03  
% 2.45/1.03  bmc1_current_bound:                     -1
% 2.45/1.03  bmc1_last_solved_bound:                 -1
% 2.45/1.03  bmc1_unsat_core_size:                   -1
% 2.45/1.03  bmc1_unsat_core_parents_size:           -1
% 2.45/1.03  bmc1_merge_next_fun:                    0
% 2.45/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.45/1.03  
% 2.45/1.03  ------ Instantiation
% 2.45/1.03  
% 2.45/1.03  inst_num_of_clauses:                    519
% 2.45/1.03  inst_num_in_passive:                    51
% 2.45/1.03  inst_num_in_active:                     207
% 2.45/1.03  inst_num_in_unprocessed:                261
% 2.45/1.03  inst_num_of_loops:                      210
% 2.45/1.03  inst_num_of_learning_restarts:          0
% 2.45/1.03  inst_num_moves_active_passive:          1
% 2.45/1.03  inst_lit_activity:                      0
% 2.45/1.03  inst_lit_activity_moves:                0
% 2.45/1.03  inst_num_tautologies:                   0
% 2.45/1.03  inst_num_prop_implied:                  0
% 2.45/1.03  inst_num_existing_simplified:           0
% 2.45/1.03  inst_num_eq_res_simplified:             0
% 2.45/1.03  inst_num_child_elim:                    0
% 2.45/1.03  inst_num_of_dismatching_blockings:      120
% 2.45/1.03  inst_num_of_non_proper_insts:           258
% 2.45/1.03  inst_num_of_duplicates:                 0
% 2.45/1.03  inst_inst_num_from_inst_to_res:         0
% 2.45/1.03  inst_dismatching_checking_time:         0.
% 2.45/1.03  
% 2.45/1.03  ------ Resolution
% 2.45/1.03  
% 2.45/1.03  res_num_of_clauses:                     0
% 2.45/1.03  res_num_in_passive:                     0
% 2.45/1.03  res_num_in_active:                      0
% 2.45/1.03  res_num_of_loops:                       79
% 2.45/1.03  res_forward_subset_subsumed:            23
% 2.45/1.03  res_backward_subset_subsumed:           0
% 2.45/1.03  res_forward_subsumed:                   0
% 2.45/1.03  res_backward_subsumed:                  0
% 2.45/1.03  res_forward_subsumption_resolution:     0
% 2.45/1.03  res_backward_subsumption_resolution:    0
% 2.45/1.03  res_clause_to_clause_subsumption:       170
% 2.45/1.03  res_orphan_elimination:                 0
% 2.45/1.03  res_tautology_del:                      49
% 2.45/1.03  res_num_eq_res_simplified:              0
% 2.45/1.03  res_num_sel_changes:                    0
% 2.45/1.03  res_moves_from_active_to_pass:          0
% 2.45/1.03  
% 2.45/1.03  ------ Superposition
% 2.45/1.03  
% 2.45/1.03  sup_time_total:                         0.
% 2.45/1.03  sup_time_generating:                    0.
% 2.45/1.03  sup_time_sim_full:                      0.
% 2.45/1.03  sup_time_sim_immed:                     0.
% 2.45/1.03  
% 2.45/1.03  sup_num_of_clauses:                     71
% 2.45/1.03  sup_num_in_active:                      40
% 2.45/1.03  sup_num_in_passive:                     31
% 2.45/1.03  sup_num_of_loops:                       41
% 2.45/1.03  sup_fw_superposition:                   33
% 2.45/1.03  sup_bw_superposition:                   28
% 2.45/1.03  sup_immediate_simplified:               4
% 2.45/1.03  sup_given_eliminated:                   0
% 2.45/1.03  comparisons_done:                       0
% 2.45/1.03  comparisons_avoided:                    0
% 2.45/1.03  
% 2.45/1.03  ------ Simplifications
% 2.45/1.03  
% 2.45/1.03  
% 2.45/1.03  sim_fw_subset_subsumed:                 3
% 2.45/1.03  sim_bw_subset_subsumed:                 0
% 2.45/1.03  sim_fw_subsumed:                        1
% 2.45/1.03  sim_bw_subsumed:                        0
% 2.45/1.03  sim_fw_subsumption_res:                 1
% 2.45/1.03  sim_bw_subsumption_res:                 0
% 2.45/1.03  sim_tautology_del:                      1
% 2.45/1.03  sim_eq_tautology_del:                   0
% 2.45/1.03  sim_eq_res_simp:                        0
% 2.45/1.03  sim_fw_demodulated:                     1
% 2.45/1.03  sim_bw_demodulated:                     2
% 2.45/1.03  sim_light_normalised:                   0
% 2.45/1.03  sim_joinable_taut:                      0
% 2.45/1.03  sim_joinable_simp:                      0
% 2.45/1.03  sim_ac_normalised:                      0
% 2.45/1.03  sim_smt_subsumption:                    0
% 2.45/1.03  
%------------------------------------------------------------------------------
