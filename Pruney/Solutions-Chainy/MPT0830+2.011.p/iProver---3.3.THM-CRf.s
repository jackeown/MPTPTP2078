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
% DateTime   : Thu Dec  3 11:55:27 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 177 expanded)
%              Number of clauses        :   55 (  84 expanded)
%              Number of leaves         :   11 (  29 expanded)
%              Depth                    :   15
%              Number of atoms          :  217 ( 388 expanded)
%              Number of equality atoms :   60 (  76 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

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

fof(f36,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
   => ( ~ m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ~ m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f29,f36])).

fof(f57,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

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

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f27])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
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

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f58,plain,(
    ~ m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(X2,X1)
        & v1_relat_1(X2) )
     => ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(k7_relat_1(X2,X0),X0)
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_14,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_733,plain,
    ( r1_tarski(k7_relat_1(X0_44,X1_44),X0_44)
    | ~ v1_relat_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1207,plain,
    ( r1_tarski(k7_relat_1(X0_44,X1_44),X0_44) = iProver_top
    | v1_relat_1(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_733])).

cnf(c_10,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_737,plain,
    ( ~ v4_relat_1(X0_44,X1_44)
    | r1_tarski(k1_relat_1(X0_44),X1_44)
    | ~ v1_relat_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1203,plain,
    ( v4_relat_1(X0_44,X1_44) != iProver_top
    | r1_tarski(k1_relat_1(X0_44),X1_44) = iProver_top
    | v1_relat_1(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_737])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_727,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1213,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_727])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_739,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | r1_tarski(X0_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1201,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44)) != iProver_top
    | r1_tarski(X0_44,X1_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_739])).

cnf(c_1369,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1213,c_1201])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_741,plain,
    ( ~ r1_tarski(X0_44,X1_44)
    | ~ r1_tarski(X2_44,X0_44)
    | r1_tarski(X2_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1199,plain,
    ( r1_tarski(X0_44,X1_44) != iProver_top
    | r1_tarski(X2_44,X0_44) != iProver_top
    | r1_tarski(X2_44,X1_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_741])).

cnf(c_1614,plain,
    ( r1_tarski(X0_44,k2_zfmisc_1(sK1,sK3)) = iProver_top
    | r1_tarski(X0_44,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1369,c_1199])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_740,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | ~ r1_tarski(X0_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1200,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44)) = iProver_top
    | r1_tarski(X0_44,X1_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_740])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_729,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X0_46)))
    | m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X2_44,X0_46)))
    | ~ r1_tarski(k1_relat_1(X0_44),X2_44) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1211,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X0_46))) != iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X2_44,X0_46))) = iProver_top
    | r1_tarski(k1_relat_1(X0_44),X2_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_729])).

cnf(c_2854,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X0_46))) = iProver_top
    | r1_tarski(X0_44,k2_zfmisc_1(X2_44,X0_46)) != iProver_top
    | r1_tarski(k1_relat_1(X0_44),X1_44) != iProver_top ),
    inference(superposition,[status(thm)],[c_1200,c_1211])).

cnf(c_8701,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,sK3))) = iProver_top
    | r1_tarski(X0_44,sK4) != iProver_top
    | r1_tarski(k1_relat_1(X0_44),X1_44) != iProver_top ),
    inference(superposition,[status(thm)],[c_1614,c_2854])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k5_relset_1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_730,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X0_46)))
    | k5_relset_1(X1_44,X0_46,X0_44,X2_44) = k7_relat_1(X0_44,X2_44) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1210,plain,
    ( k5_relset_1(X0_44,X0_46,X1_44,X2_44) = k7_relat_1(X1_44,X2_44)
    | m1_subset_1(X1_44,k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_730])).

cnf(c_2360,plain,
    ( k5_relset_1(sK1,sK3,sK4,X0_44) = k7_relat_1(sK4,X0_44) ),
    inference(superposition,[status(thm)],[c_1213,c_1210])).

cnf(c_19,negated_conjecture,
    ( ~ m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_728,negated_conjecture,
    ( ~ m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1212,plain,
    ( m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_728])).

cnf(c_2871,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2360,c_1212])).

cnf(c_9406,plain,
    ( r1_tarski(k7_relat_1(sK4,sK2),sK4) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK4,sK2)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8701,c_2871])).

cnf(c_9441,plain,
    ( v4_relat_1(k7_relat_1(sK4,sK2),sK2) != iProver_top
    | r1_tarski(k7_relat_1(sK4,sK2),sK4) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1203,c_9406])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_732,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X0_46)))
    | v1_relat_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1208,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X0_46))) != iProver_top
    | v1_relat_1(X0_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_732])).

cnf(c_1477,plain,
    ( r1_tarski(X0_44,k2_zfmisc_1(X1_44,X0_46)) != iProver_top
    | v1_relat_1(X0_44) = iProver_top ),
    inference(superposition,[status(thm)],[c_1200,c_1208])).

cnf(c_3549,plain,
    ( r1_tarski(X0_44,sK4) != iProver_top
    | v1_relat_1(X0_44) = iProver_top ),
    inference(superposition,[status(thm)],[c_1614,c_1477])).

cnf(c_16,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_731,plain,
    ( v4_relat_1(X0_44,X1_44)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X0_46))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1209,plain,
    ( v4_relat_1(X0_44,X1_44) = iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X0_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_731])).

cnf(c_1598,plain,
    ( v4_relat_1(sK4,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1213,c_1209])).

cnf(c_12,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(k7_relat_1(X0,X2),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_735,plain,
    ( ~ v4_relat_1(X0_44,X1_44)
    | v4_relat_1(k7_relat_1(X0_44,X2_44),X2_44)
    | ~ v1_relat_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1205,plain,
    ( v4_relat_1(X0_44,X1_44) != iProver_top
    | v4_relat_1(k7_relat_1(X0_44,X2_44),X2_44) = iProver_top
    | v1_relat_1(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_735])).

cnf(c_2507,plain,
    ( v4_relat_1(k7_relat_1(sK4,X0_44),X0_44) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1598,c_1205])).

cnf(c_21,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1336,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_732])).

cnf(c_1337,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1336])).

cnf(c_3066,plain,
    ( v4_relat_1(k7_relat_1(sK4,X0_44),X0_44) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2507,c_21,c_1337])).

cnf(c_9582,plain,
    ( r1_tarski(k7_relat_1(sK4,sK2),sK4) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9441,c_3549,c_3066])).

cnf(c_9584,plain,
    ( v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1207,c_9582])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9584,c_1337,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:09:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.24/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.00  
% 3.24/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.24/1.00  
% 3.24/1.00  ------  iProver source info
% 3.24/1.00  
% 3.24/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.24/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.24/1.00  git: non_committed_changes: false
% 3.24/1.00  git: last_make_outside_of_git: false
% 3.24/1.00  
% 3.24/1.00  ------ 
% 3.24/1.00  
% 3.24/1.00  ------ Input Options
% 3.24/1.00  
% 3.24/1.00  --out_options                           all
% 3.24/1.00  --tptp_safe_out                         true
% 3.24/1.00  --problem_path                          ""
% 3.24/1.00  --include_path                          ""
% 3.24/1.00  --clausifier                            res/vclausify_rel
% 3.24/1.00  --clausifier_options                    --mode clausify
% 3.24/1.00  --stdin                                 false
% 3.24/1.00  --stats_out                             all
% 3.24/1.00  
% 3.24/1.00  ------ General Options
% 3.24/1.00  
% 3.24/1.00  --fof                                   false
% 3.24/1.00  --time_out_real                         305.
% 3.24/1.00  --time_out_virtual                      -1.
% 3.24/1.00  --symbol_type_check                     false
% 3.24/1.00  --clausify_out                          false
% 3.24/1.00  --sig_cnt_out                           false
% 3.24/1.00  --trig_cnt_out                          false
% 3.24/1.00  --trig_cnt_out_tolerance                1.
% 3.24/1.00  --trig_cnt_out_sk_spl                   false
% 3.24/1.00  --abstr_cl_out                          false
% 3.24/1.00  
% 3.24/1.00  ------ Global Options
% 3.24/1.00  
% 3.24/1.00  --schedule                              default
% 3.24/1.00  --add_important_lit                     false
% 3.24/1.00  --prop_solver_per_cl                    1000
% 3.24/1.00  --min_unsat_core                        false
% 3.24/1.00  --soft_assumptions                      false
% 3.24/1.00  --soft_lemma_size                       3
% 3.24/1.00  --prop_impl_unit_size                   0
% 3.24/1.00  --prop_impl_unit                        []
% 3.24/1.00  --share_sel_clauses                     true
% 3.24/1.00  --reset_solvers                         false
% 3.24/1.00  --bc_imp_inh                            [conj_cone]
% 3.24/1.00  --conj_cone_tolerance                   3.
% 3.24/1.00  --extra_neg_conj                        none
% 3.24/1.00  --large_theory_mode                     true
% 3.24/1.00  --prolific_symb_bound                   200
% 3.24/1.00  --lt_threshold                          2000
% 3.24/1.00  --clause_weak_htbl                      true
% 3.24/1.00  --gc_record_bc_elim                     false
% 3.24/1.00  
% 3.24/1.00  ------ Preprocessing Options
% 3.24/1.00  
% 3.24/1.00  --preprocessing_flag                    true
% 3.24/1.00  --time_out_prep_mult                    0.1
% 3.24/1.00  --splitting_mode                        input
% 3.24/1.00  --splitting_grd                         true
% 3.24/1.00  --splitting_cvd                         false
% 3.24/1.00  --splitting_cvd_svl                     false
% 3.24/1.00  --splitting_nvd                         32
% 3.24/1.00  --sub_typing                            true
% 3.24/1.00  --prep_gs_sim                           true
% 3.24/1.00  --prep_unflatten                        true
% 3.24/1.00  --prep_res_sim                          true
% 3.24/1.00  --prep_upred                            true
% 3.24/1.00  --prep_sem_filter                       exhaustive
% 3.24/1.00  --prep_sem_filter_out                   false
% 3.24/1.00  --pred_elim                             true
% 3.24/1.00  --res_sim_input                         true
% 3.24/1.00  --eq_ax_congr_red                       true
% 3.24/1.00  --pure_diseq_elim                       true
% 3.24/1.00  --brand_transform                       false
% 3.24/1.00  --non_eq_to_eq                          false
% 3.24/1.00  --prep_def_merge                        true
% 3.24/1.00  --prep_def_merge_prop_impl              false
% 3.24/1.00  --prep_def_merge_mbd                    true
% 3.24/1.00  --prep_def_merge_tr_red                 false
% 3.24/1.00  --prep_def_merge_tr_cl                  false
% 3.24/1.00  --smt_preprocessing                     true
% 3.24/1.00  --smt_ac_axioms                         fast
% 3.24/1.00  --preprocessed_out                      false
% 3.24/1.00  --preprocessed_stats                    false
% 3.24/1.00  
% 3.24/1.00  ------ Abstraction refinement Options
% 3.24/1.00  
% 3.24/1.00  --abstr_ref                             []
% 3.24/1.00  --abstr_ref_prep                        false
% 3.24/1.00  --abstr_ref_until_sat                   false
% 3.24/1.00  --abstr_ref_sig_restrict                funpre
% 3.24/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.24/1.00  --abstr_ref_under                       []
% 3.24/1.00  
% 3.24/1.00  ------ SAT Options
% 3.24/1.00  
% 3.24/1.00  --sat_mode                              false
% 3.24/1.00  --sat_fm_restart_options                ""
% 3.24/1.00  --sat_gr_def                            false
% 3.24/1.00  --sat_epr_types                         true
% 3.24/1.00  --sat_non_cyclic_types                  false
% 3.24/1.00  --sat_finite_models                     false
% 3.24/1.00  --sat_fm_lemmas                         false
% 3.24/1.00  --sat_fm_prep                           false
% 3.24/1.00  --sat_fm_uc_incr                        true
% 3.24/1.00  --sat_out_model                         small
% 3.24/1.00  --sat_out_clauses                       false
% 3.24/1.00  
% 3.24/1.00  ------ QBF Options
% 3.24/1.00  
% 3.24/1.00  --qbf_mode                              false
% 3.24/1.00  --qbf_elim_univ                         false
% 3.24/1.00  --qbf_dom_inst                          none
% 3.24/1.00  --qbf_dom_pre_inst                      false
% 3.24/1.00  --qbf_sk_in                             false
% 3.24/1.00  --qbf_pred_elim                         true
% 3.24/1.00  --qbf_split                             512
% 3.24/1.00  
% 3.24/1.00  ------ BMC1 Options
% 3.24/1.00  
% 3.24/1.00  --bmc1_incremental                      false
% 3.24/1.00  --bmc1_axioms                           reachable_all
% 3.24/1.00  --bmc1_min_bound                        0
% 3.24/1.00  --bmc1_max_bound                        -1
% 3.24/1.00  --bmc1_max_bound_default                -1
% 3.24/1.00  --bmc1_symbol_reachability              true
% 3.24/1.00  --bmc1_property_lemmas                  false
% 3.24/1.00  --bmc1_k_induction                      false
% 3.24/1.00  --bmc1_non_equiv_states                 false
% 3.24/1.00  --bmc1_deadlock                         false
% 3.24/1.00  --bmc1_ucm                              false
% 3.24/1.00  --bmc1_add_unsat_core                   none
% 3.24/1.00  --bmc1_unsat_core_children              false
% 3.24/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.24/1.00  --bmc1_out_stat                         full
% 3.24/1.00  --bmc1_ground_init                      false
% 3.24/1.00  --bmc1_pre_inst_next_state              false
% 3.24/1.00  --bmc1_pre_inst_state                   false
% 3.24/1.00  --bmc1_pre_inst_reach_state             false
% 3.24/1.00  --bmc1_out_unsat_core                   false
% 3.24/1.00  --bmc1_aig_witness_out                  false
% 3.24/1.00  --bmc1_verbose                          false
% 3.24/1.00  --bmc1_dump_clauses_tptp                false
% 3.24/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.24/1.00  --bmc1_dump_file                        -
% 3.24/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.24/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.24/1.00  --bmc1_ucm_extend_mode                  1
% 3.24/1.00  --bmc1_ucm_init_mode                    2
% 3.24/1.00  --bmc1_ucm_cone_mode                    none
% 3.24/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.24/1.00  --bmc1_ucm_relax_model                  4
% 3.24/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.24/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.24/1.00  --bmc1_ucm_layered_model                none
% 3.24/1.00  --bmc1_ucm_max_lemma_size               10
% 3.24/1.00  
% 3.24/1.00  ------ AIG Options
% 3.24/1.00  
% 3.24/1.00  --aig_mode                              false
% 3.24/1.00  
% 3.24/1.00  ------ Instantiation Options
% 3.24/1.00  
% 3.24/1.00  --instantiation_flag                    true
% 3.24/1.00  --inst_sos_flag                         false
% 3.24/1.00  --inst_sos_phase                        true
% 3.24/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.24/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.24/1.00  --inst_lit_sel_side                     num_symb
% 3.24/1.00  --inst_solver_per_active                1400
% 3.24/1.00  --inst_solver_calls_frac                1.
% 3.24/1.00  --inst_passive_queue_type               priority_queues
% 3.24/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.24/1.00  --inst_passive_queues_freq              [25;2]
% 3.24/1.00  --inst_dismatching                      true
% 3.24/1.00  --inst_eager_unprocessed_to_passive     true
% 3.24/1.00  --inst_prop_sim_given                   true
% 3.24/1.00  --inst_prop_sim_new                     false
% 3.24/1.00  --inst_subs_new                         false
% 3.24/1.00  --inst_eq_res_simp                      false
% 3.24/1.00  --inst_subs_given                       false
% 3.24/1.00  --inst_orphan_elimination               true
% 3.24/1.00  --inst_learning_loop_flag               true
% 3.24/1.00  --inst_learning_start                   3000
% 3.24/1.00  --inst_learning_factor                  2
% 3.24/1.00  --inst_start_prop_sim_after_learn       3
% 3.24/1.00  --inst_sel_renew                        solver
% 3.24/1.00  --inst_lit_activity_flag                true
% 3.24/1.00  --inst_restr_to_given                   false
% 3.24/1.00  --inst_activity_threshold               500
% 3.24/1.00  --inst_out_proof                        true
% 3.24/1.00  
% 3.24/1.00  ------ Resolution Options
% 3.24/1.00  
% 3.24/1.00  --resolution_flag                       true
% 3.24/1.00  --res_lit_sel                           adaptive
% 3.24/1.00  --res_lit_sel_side                      none
% 3.24/1.00  --res_ordering                          kbo
% 3.24/1.00  --res_to_prop_solver                    active
% 3.24/1.00  --res_prop_simpl_new                    false
% 3.24/1.00  --res_prop_simpl_given                  true
% 3.24/1.00  --res_passive_queue_type                priority_queues
% 3.24/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.24/1.00  --res_passive_queues_freq               [15;5]
% 3.24/1.00  --res_forward_subs                      full
% 3.24/1.00  --res_backward_subs                     full
% 3.24/1.00  --res_forward_subs_resolution           true
% 3.24/1.00  --res_backward_subs_resolution          true
% 3.24/1.00  --res_orphan_elimination                true
% 3.24/1.00  --res_time_limit                        2.
% 3.24/1.00  --res_out_proof                         true
% 3.24/1.00  
% 3.24/1.00  ------ Superposition Options
% 3.24/1.00  
% 3.24/1.00  --superposition_flag                    true
% 3.24/1.00  --sup_passive_queue_type                priority_queues
% 3.24/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.24/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.24/1.00  --demod_completeness_check              fast
% 3.24/1.00  --demod_use_ground                      true
% 3.24/1.00  --sup_to_prop_solver                    passive
% 3.24/1.00  --sup_prop_simpl_new                    true
% 3.24/1.00  --sup_prop_simpl_given                  true
% 3.24/1.00  --sup_fun_splitting                     false
% 3.24/1.00  --sup_smt_interval                      50000
% 3.24/1.00  
% 3.24/1.00  ------ Superposition Simplification Setup
% 3.24/1.00  
% 3.24/1.00  --sup_indices_passive                   []
% 3.24/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.24/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.00  --sup_full_bw                           [BwDemod]
% 3.24/1.00  --sup_immed_triv                        [TrivRules]
% 3.24/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.24/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.00  --sup_immed_bw_main                     []
% 3.24/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.24/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/1.00  
% 3.24/1.00  ------ Combination Options
% 3.24/1.00  
% 3.24/1.00  --comb_res_mult                         3
% 3.24/1.00  --comb_sup_mult                         2
% 3.24/1.00  --comb_inst_mult                        10
% 3.24/1.00  
% 3.24/1.00  ------ Debug Options
% 3.24/1.00  
% 3.24/1.00  --dbg_backtrace                         false
% 3.24/1.00  --dbg_dump_prop_clauses                 false
% 3.24/1.00  --dbg_dump_prop_clauses_file            -
% 3.24/1.00  --dbg_out_stat                          false
% 3.24/1.00  ------ Parsing...
% 3.24/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.24/1.00  
% 3.24/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.24/1.00  
% 3.24/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.24/1.00  
% 3.24/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.24/1.00  ------ Proving...
% 3.24/1.00  ------ Problem Properties 
% 3.24/1.00  
% 3.24/1.00  
% 3.24/1.00  clauses                                 17
% 3.24/1.00  conjectures                             2
% 3.24/1.00  EPR                                     1
% 3.24/1.00  Horn                                    16
% 3.24/1.00  unary                                   2
% 3.24/1.00  binary                                  6
% 3.24/1.00  lits                                    41
% 3.24/1.00  lits eq                                 3
% 3.24/1.00  fd_pure                                 0
% 3.24/1.00  fd_pseudo                               0
% 3.24/1.00  fd_cond                                 0
% 3.24/1.00  fd_pseudo_cond                          0
% 3.24/1.00  AC symbols                              0
% 3.24/1.00  
% 3.24/1.00  ------ Schedule dynamic 5 is on 
% 3.24/1.00  
% 3.24/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.24/1.00  
% 3.24/1.00  
% 3.24/1.00  ------ 
% 3.24/1.00  Current options:
% 3.24/1.00  ------ 
% 3.24/1.00  
% 3.24/1.00  ------ Input Options
% 3.24/1.00  
% 3.24/1.00  --out_options                           all
% 3.24/1.00  --tptp_safe_out                         true
% 3.24/1.00  --problem_path                          ""
% 3.24/1.00  --include_path                          ""
% 3.24/1.00  --clausifier                            res/vclausify_rel
% 3.24/1.00  --clausifier_options                    --mode clausify
% 3.24/1.00  --stdin                                 false
% 3.24/1.00  --stats_out                             all
% 3.24/1.00  
% 3.24/1.00  ------ General Options
% 3.24/1.00  
% 3.24/1.00  --fof                                   false
% 3.24/1.00  --time_out_real                         305.
% 3.24/1.00  --time_out_virtual                      -1.
% 3.24/1.00  --symbol_type_check                     false
% 3.24/1.00  --clausify_out                          false
% 3.24/1.00  --sig_cnt_out                           false
% 3.24/1.00  --trig_cnt_out                          false
% 3.24/1.00  --trig_cnt_out_tolerance                1.
% 3.24/1.00  --trig_cnt_out_sk_spl                   false
% 3.24/1.00  --abstr_cl_out                          false
% 3.24/1.00  
% 3.24/1.00  ------ Global Options
% 3.24/1.00  
% 3.24/1.00  --schedule                              default
% 3.24/1.00  --add_important_lit                     false
% 3.24/1.00  --prop_solver_per_cl                    1000
% 3.24/1.00  --min_unsat_core                        false
% 3.24/1.00  --soft_assumptions                      false
% 3.24/1.00  --soft_lemma_size                       3
% 3.24/1.00  --prop_impl_unit_size                   0
% 3.24/1.00  --prop_impl_unit                        []
% 3.24/1.00  --share_sel_clauses                     true
% 3.24/1.00  --reset_solvers                         false
% 3.24/1.00  --bc_imp_inh                            [conj_cone]
% 3.24/1.00  --conj_cone_tolerance                   3.
% 3.24/1.00  --extra_neg_conj                        none
% 3.24/1.00  --large_theory_mode                     true
% 3.24/1.00  --prolific_symb_bound                   200
% 3.24/1.00  --lt_threshold                          2000
% 3.24/1.00  --clause_weak_htbl                      true
% 3.24/1.00  --gc_record_bc_elim                     false
% 3.24/1.00  
% 3.24/1.00  ------ Preprocessing Options
% 3.24/1.00  
% 3.24/1.00  --preprocessing_flag                    true
% 3.24/1.00  --time_out_prep_mult                    0.1
% 3.24/1.00  --splitting_mode                        input
% 3.24/1.00  --splitting_grd                         true
% 3.24/1.00  --splitting_cvd                         false
% 3.24/1.00  --splitting_cvd_svl                     false
% 3.24/1.00  --splitting_nvd                         32
% 3.24/1.00  --sub_typing                            true
% 3.24/1.00  --prep_gs_sim                           true
% 3.24/1.00  --prep_unflatten                        true
% 3.24/1.00  --prep_res_sim                          true
% 3.24/1.00  --prep_upred                            true
% 3.24/1.00  --prep_sem_filter                       exhaustive
% 3.24/1.00  --prep_sem_filter_out                   false
% 3.24/1.00  --pred_elim                             true
% 3.24/1.00  --res_sim_input                         true
% 3.24/1.00  --eq_ax_congr_red                       true
% 3.24/1.00  --pure_diseq_elim                       true
% 3.24/1.00  --brand_transform                       false
% 3.24/1.00  --non_eq_to_eq                          false
% 3.24/1.00  --prep_def_merge                        true
% 3.24/1.00  --prep_def_merge_prop_impl              false
% 3.24/1.00  --prep_def_merge_mbd                    true
% 3.24/1.00  --prep_def_merge_tr_red                 false
% 3.24/1.00  --prep_def_merge_tr_cl                  false
% 3.24/1.00  --smt_preprocessing                     true
% 3.24/1.00  --smt_ac_axioms                         fast
% 3.24/1.00  --preprocessed_out                      false
% 3.24/1.00  --preprocessed_stats                    false
% 3.24/1.00  
% 3.24/1.00  ------ Abstraction refinement Options
% 3.24/1.00  
% 3.24/1.00  --abstr_ref                             []
% 3.24/1.00  --abstr_ref_prep                        false
% 3.24/1.00  --abstr_ref_until_sat                   false
% 3.24/1.00  --abstr_ref_sig_restrict                funpre
% 3.24/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.24/1.00  --abstr_ref_under                       []
% 3.24/1.00  
% 3.24/1.00  ------ SAT Options
% 3.24/1.00  
% 3.24/1.00  --sat_mode                              false
% 3.24/1.00  --sat_fm_restart_options                ""
% 3.24/1.00  --sat_gr_def                            false
% 3.24/1.00  --sat_epr_types                         true
% 3.24/1.00  --sat_non_cyclic_types                  false
% 3.24/1.00  --sat_finite_models                     false
% 3.24/1.00  --sat_fm_lemmas                         false
% 3.24/1.00  --sat_fm_prep                           false
% 3.24/1.00  --sat_fm_uc_incr                        true
% 3.24/1.00  --sat_out_model                         small
% 3.24/1.00  --sat_out_clauses                       false
% 3.24/1.00  
% 3.24/1.00  ------ QBF Options
% 3.24/1.00  
% 3.24/1.00  --qbf_mode                              false
% 3.24/1.00  --qbf_elim_univ                         false
% 3.24/1.00  --qbf_dom_inst                          none
% 3.24/1.00  --qbf_dom_pre_inst                      false
% 3.24/1.00  --qbf_sk_in                             false
% 3.24/1.00  --qbf_pred_elim                         true
% 3.24/1.00  --qbf_split                             512
% 3.24/1.00  
% 3.24/1.00  ------ BMC1 Options
% 3.24/1.00  
% 3.24/1.00  --bmc1_incremental                      false
% 3.24/1.00  --bmc1_axioms                           reachable_all
% 3.24/1.00  --bmc1_min_bound                        0
% 3.24/1.00  --bmc1_max_bound                        -1
% 3.24/1.00  --bmc1_max_bound_default                -1
% 3.24/1.00  --bmc1_symbol_reachability              true
% 3.24/1.00  --bmc1_property_lemmas                  false
% 3.24/1.00  --bmc1_k_induction                      false
% 3.24/1.00  --bmc1_non_equiv_states                 false
% 3.24/1.00  --bmc1_deadlock                         false
% 3.24/1.00  --bmc1_ucm                              false
% 3.24/1.00  --bmc1_add_unsat_core                   none
% 3.24/1.00  --bmc1_unsat_core_children              false
% 3.24/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.24/1.00  --bmc1_out_stat                         full
% 3.24/1.00  --bmc1_ground_init                      false
% 3.24/1.00  --bmc1_pre_inst_next_state              false
% 3.24/1.00  --bmc1_pre_inst_state                   false
% 3.24/1.00  --bmc1_pre_inst_reach_state             false
% 3.24/1.00  --bmc1_out_unsat_core                   false
% 3.24/1.00  --bmc1_aig_witness_out                  false
% 3.24/1.00  --bmc1_verbose                          false
% 3.24/1.00  --bmc1_dump_clauses_tptp                false
% 3.24/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.24/1.00  --bmc1_dump_file                        -
% 3.24/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.24/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.24/1.00  --bmc1_ucm_extend_mode                  1
% 3.24/1.00  --bmc1_ucm_init_mode                    2
% 3.24/1.00  --bmc1_ucm_cone_mode                    none
% 3.24/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.24/1.00  --bmc1_ucm_relax_model                  4
% 3.24/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.24/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.24/1.00  --bmc1_ucm_layered_model                none
% 3.24/1.00  --bmc1_ucm_max_lemma_size               10
% 3.24/1.00  
% 3.24/1.00  ------ AIG Options
% 3.24/1.00  
% 3.24/1.00  --aig_mode                              false
% 3.24/1.00  
% 3.24/1.00  ------ Instantiation Options
% 3.24/1.00  
% 3.24/1.00  --instantiation_flag                    true
% 3.24/1.00  --inst_sos_flag                         false
% 3.24/1.00  --inst_sos_phase                        true
% 3.24/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.24/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.24/1.00  --inst_lit_sel_side                     none
% 3.24/1.00  --inst_solver_per_active                1400
% 3.24/1.00  --inst_solver_calls_frac                1.
% 3.24/1.00  --inst_passive_queue_type               priority_queues
% 3.24/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.24/1.00  --inst_passive_queues_freq              [25;2]
% 3.24/1.00  --inst_dismatching                      true
% 3.24/1.00  --inst_eager_unprocessed_to_passive     true
% 3.24/1.00  --inst_prop_sim_given                   true
% 3.24/1.00  --inst_prop_sim_new                     false
% 3.24/1.00  --inst_subs_new                         false
% 3.24/1.00  --inst_eq_res_simp                      false
% 3.24/1.00  --inst_subs_given                       false
% 3.24/1.00  --inst_orphan_elimination               true
% 3.24/1.00  --inst_learning_loop_flag               true
% 3.24/1.00  --inst_learning_start                   3000
% 3.24/1.00  --inst_learning_factor                  2
% 3.24/1.00  --inst_start_prop_sim_after_learn       3
% 3.24/1.00  --inst_sel_renew                        solver
% 3.24/1.00  --inst_lit_activity_flag                true
% 3.24/1.00  --inst_restr_to_given                   false
% 3.24/1.00  --inst_activity_threshold               500
% 3.24/1.00  --inst_out_proof                        true
% 3.24/1.00  
% 3.24/1.00  ------ Resolution Options
% 3.24/1.00  
% 3.24/1.00  --resolution_flag                       false
% 3.24/1.00  --res_lit_sel                           adaptive
% 3.24/1.00  --res_lit_sel_side                      none
% 3.24/1.00  --res_ordering                          kbo
% 3.24/1.00  --res_to_prop_solver                    active
% 3.24/1.00  --res_prop_simpl_new                    false
% 3.24/1.00  --res_prop_simpl_given                  true
% 3.24/1.00  --res_passive_queue_type                priority_queues
% 3.24/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.24/1.00  --res_passive_queues_freq               [15;5]
% 3.24/1.00  --res_forward_subs                      full
% 3.24/1.00  --res_backward_subs                     full
% 3.24/1.00  --res_forward_subs_resolution           true
% 3.24/1.00  --res_backward_subs_resolution          true
% 3.24/1.00  --res_orphan_elimination                true
% 3.24/1.00  --res_time_limit                        2.
% 3.24/1.00  --res_out_proof                         true
% 3.24/1.00  
% 3.24/1.00  ------ Superposition Options
% 3.24/1.00  
% 3.24/1.00  --superposition_flag                    true
% 3.24/1.00  --sup_passive_queue_type                priority_queues
% 3.24/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.24/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.24/1.00  --demod_completeness_check              fast
% 3.24/1.00  --demod_use_ground                      true
% 3.24/1.00  --sup_to_prop_solver                    passive
% 3.24/1.00  --sup_prop_simpl_new                    true
% 3.24/1.00  --sup_prop_simpl_given                  true
% 3.24/1.00  --sup_fun_splitting                     false
% 3.24/1.00  --sup_smt_interval                      50000
% 3.24/1.00  
% 3.24/1.00  ------ Superposition Simplification Setup
% 3.24/1.00  
% 3.24/1.00  --sup_indices_passive                   []
% 3.24/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.24/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.00  --sup_full_bw                           [BwDemod]
% 3.24/1.00  --sup_immed_triv                        [TrivRules]
% 3.24/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.24/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.00  --sup_immed_bw_main                     []
% 3.24/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.24/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/1.00  
% 3.24/1.00  ------ Combination Options
% 3.24/1.00  
% 3.24/1.00  --comb_res_mult                         3
% 3.24/1.00  --comb_sup_mult                         2
% 3.24/1.00  --comb_inst_mult                        10
% 3.24/1.00  
% 3.24/1.00  ------ Debug Options
% 3.24/1.00  
% 3.24/1.00  --dbg_backtrace                         false
% 3.24/1.00  --dbg_dump_prop_clauses                 false
% 3.24/1.00  --dbg_dump_prop_clauses_file            -
% 3.24/1.00  --dbg_out_stat                          false
% 3.24/1.00  
% 3.24/1.00  
% 3.24/1.00  
% 3.24/1.00  
% 3.24/1.00  ------ Proving...
% 3.24/1.00  
% 3.24/1.00  
% 3.24/1.00  % SZS status Theorem for theBenchmark.p
% 3.24/1.00  
% 3.24/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.24/1.00  
% 3.24/1.00  fof(f8,axiom,(
% 3.24/1.00    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f23,plain,(
% 3.24/1.00    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 3.24/1.00    inference(ennf_transformation,[],[f8])).
% 3.24/1.00  
% 3.24/1.00  fof(f52,plain,(
% 3.24/1.00    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f23])).
% 3.24/1.00  
% 3.24/1.00  fof(f6,axiom,(
% 3.24/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f20,plain,(
% 3.24/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.24/1.00    inference(ennf_transformation,[],[f6])).
% 3.24/1.00  
% 3.24/1.00  fof(f35,plain,(
% 3.24/1.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.24/1.00    inference(nnf_transformation,[],[f20])).
% 3.24/1.00  
% 3.24/1.00  fof(f47,plain,(
% 3.24/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f35])).
% 3.24/1.00  
% 3.24/1.00  fof(f13,conjecture,(
% 3.24/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f14,negated_conjecture,(
% 3.24/1.00    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 3.24/1.00    inference(negated_conjecture,[],[f13])).
% 3.24/1.00  
% 3.24/1.00  fof(f29,plain,(
% 3.24/1.00    ? [X0,X1,X2,X3] : (~m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.24/1.00    inference(ennf_transformation,[],[f14])).
% 3.24/1.00  
% 3.24/1.00  fof(f36,plain,(
% 3.24/1.00    ? [X0,X1,X2,X3] : (~m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) => (~m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))))),
% 3.24/1.00    introduced(choice_axiom,[])).
% 3.24/1.00  
% 3.24/1.00  fof(f37,plain,(
% 3.24/1.00    ~m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 3.24/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f29,f36])).
% 3.24/1.00  
% 3.24/1.00  fof(f57,plain,(
% 3.24/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 3.24/1.00    inference(cnf_transformation,[],[f37])).
% 3.24/1.00  
% 3.24/1.00  fof(f5,axiom,(
% 3.24/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f34,plain,(
% 3.24/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.24/1.00    inference(nnf_transformation,[],[f5])).
% 3.24/1.00  
% 3.24/1.00  fof(f45,plain,(
% 3.24/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.24/1.00    inference(cnf_transformation,[],[f34])).
% 3.24/1.00  
% 3.24/1.00  fof(f1,axiom,(
% 3.24/1.00    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f16,plain,(
% 3.24/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.24/1.00    inference(ennf_transformation,[],[f1])).
% 3.24/1.00  
% 3.24/1.00  fof(f17,plain,(
% 3.24/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.24/1.00    inference(flattening,[],[f16])).
% 3.24/1.00  
% 3.24/1.00  fof(f38,plain,(
% 3.24/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f17])).
% 3.24/1.00  
% 3.24/1.00  fof(f46,plain,(
% 3.24/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f34])).
% 3.24/1.00  
% 3.24/1.00  fof(f12,axiom,(
% 3.24/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f27,plain,(
% 3.24/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.24/1.00    inference(ennf_transformation,[],[f12])).
% 3.24/1.00  
% 3.24/1.00  fof(f28,plain,(
% 3.24/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.24/1.00    inference(flattening,[],[f27])).
% 3.24/1.00  
% 3.24/1.00  fof(f56,plain,(
% 3.24/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 3.24/1.00    inference(cnf_transformation,[],[f28])).
% 3.24/1.00  
% 3.24/1.00  fof(f11,axiom,(
% 3.24/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f26,plain,(
% 3.24/1.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.24/1.00    inference(ennf_transformation,[],[f11])).
% 3.24/1.00  
% 3.24/1.00  fof(f55,plain,(
% 3.24/1.00    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.24/1.00    inference(cnf_transformation,[],[f26])).
% 3.24/1.00  
% 3.24/1.00  fof(f58,plain,(
% 3.24/1.00    ~m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.24/1.00    inference(cnf_transformation,[],[f37])).
% 3.24/1.00  
% 3.24/1.00  fof(f9,axiom,(
% 3.24/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f24,plain,(
% 3.24/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.24/1.00    inference(ennf_transformation,[],[f9])).
% 3.24/1.00  
% 3.24/1.00  fof(f53,plain,(
% 3.24/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.24/1.00    inference(cnf_transformation,[],[f24])).
% 3.24/1.00  
% 3.24/1.00  fof(f10,axiom,(
% 3.24/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f15,plain,(
% 3.24/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.24/1.00    inference(pure_predicate_removal,[],[f10])).
% 3.24/1.00  
% 3.24/1.00  fof(f25,plain,(
% 3.24/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.24/1.00    inference(ennf_transformation,[],[f15])).
% 3.24/1.00  
% 3.24/1.00  fof(f54,plain,(
% 3.24/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.24/1.00    inference(cnf_transformation,[],[f25])).
% 3.24/1.00  
% 3.24/1.00  fof(f7,axiom,(
% 3.24/1.00    ! [X0,X1,X2] : ((v4_relat_1(X2,X1) & v1_relat_1(X2)) => (v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))))),
% 3.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.00  
% 3.24/1.00  fof(f21,plain,(
% 3.24/1.00    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | (~v4_relat_1(X2,X1) | ~v1_relat_1(X2)))),
% 3.24/1.00    inference(ennf_transformation,[],[f7])).
% 3.24/1.00  
% 3.24/1.00  fof(f22,plain,(
% 3.24/1.00    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2))),
% 3.24/1.00    inference(flattening,[],[f21])).
% 3.24/1.00  
% 3.24/1.00  fof(f50,plain,(
% 3.24/1.00    ( ! [X2,X0,X1] : (v4_relat_1(k7_relat_1(X2,X0),X0) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 3.24/1.00    inference(cnf_transformation,[],[f22])).
% 3.24/1.00  
% 3.24/1.00  cnf(c_14,plain,
% 3.24/1.00      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 3.24/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_733,plain,
% 3.24/1.00      ( r1_tarski(k7_relat_1(X0_44,X1_44),X0_44) | ~ v1_relat_1(X0_44) ),
% 3.24/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1207,plain,
% 3.24/1.00      ( r1_tarski(k7_relat_1(X0_44,X1_44),X0_44) = iProver_top
% 3.24/1.00      | v1_relat_1(X0_44) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_733]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_10,plain,
% 3.24/1.00      ( ~ v4_relat_1(X0,X1)
% 3.24/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 3.24/1.00      | ~ v1_relat_1(X0) ),
% 3.24/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_737,plain,
% 3.24/1.00      ( ~ v4_relat_1(X0_44,X1_44)
% 3.24/1.00      | r1_tarski(k1_relat_1(X0_44),X1_44)
% 3.24/1.00      | ~ v1_relat_1(X0_44) ),
% 3.24/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1203,plain,
% 3.24/1.00      ( v4_relat_1(X0_44,X1_44) != iProver_top
% 3.24/1.00      | r1_tarski(k1_relat_1(X0_44),X1_44) = iProver_top
% 3.24/1.00      | v1_relat_1(X0_44) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_737]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_20,negated_conjecture,
% 3.24/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
% 3.24/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_727,negated_conjecture,
% 3.24/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
% 3.24/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1213,plain,
% 3.24/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_727]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_8,plain,
% 3.24/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.24/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_739,plain,
% 3.24/1.00      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
% 3.24/1.00      | r1_tarski(X0_44,X1_44) ),
% 3.24/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1201,plain,
% 3.24/1.00      ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44)) != iProver_top
% 3.24/1.00      | r1_tarski(X0_44,X1_44) = iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_739]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1369,plain,
% 3.24/1.00      ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK3)) = iProver_top ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_1213,c_1201]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_0,plain,
% 3.24/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 3.24/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_741,plain,
% 3.24/1.00      ( ~ r1_tarski(X0_44,X1_44)
% 3.24/1.00      | ~ r1_tarski(X2_44,X0_44)
% 3.24/1.00      | r1_tarski(X2_44,X1_44) ),
% 3.24/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1199,plain,
% 3.24/1.00      ( r1_tarski(X0_44,X1_44) != iProver_top
% 3.24/1.00      | r1_tarski(X2_44,X0_44) != iProver_top
% 3.24/1.00      | r1_tarski(X2_44,X1_44) = iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_741]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1614,plain,
% 3.24/1.00      ( r1_tarski(X0_44,k2_zfmisc_1(sK1,sK3)) = iProver_top
% 3.24/1.00      | r1_tarski(X0_44,sK4) != iProver_top ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_1369,c_1199]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_7,plain,
% 3.24/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.24/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_740,plain,
% 3.24/1.00      ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
% 3.24/1.00      | ~ r1_tarski(X0_44,X1_44) ),
% 3.24/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1200,plain,
% 3.24/1.00      ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44)) = iProver_top
% 3.24/1.00      | r1_tarski(X0_44,X1_44) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_740]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_18,plain,
% 3.24/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.24/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 3.24/1.00      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 3.24/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_729,plain,
% 3.24/1.00      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X0_46)))
% 3.24/1.00      | m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X2_44,X0_46)))
% 3.24/1.00      | ~ r1_tarski(k1_relat_1(X0_44),X2_44) ),
% 3.24/1.00      inference(subtyping,[status(esa)],[c_18]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1211,plain,
% 3.24/1.00      ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X0_46))) != iProver_top
% 3.24/1.00      | m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X2_44,X0_46))) = iProver_top
% 3.24/1.00      | r1_tarski(k1_relat_1(X0_44),X2_44) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_729]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2854,plain,
% 3.24/1.00      ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X0_46))) = iProver_top
% 3.24/1.00      | r1_tarski(X0_44,k2_zfmisc_1(X2_44,X0_46)) != iProver_top
% 3.24/1.00      | r1_tarski(k1_relat_1(X0_44),X1_44) != iProver_top ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_1200,c_1211]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_8701,plain,
% 3.24/1.00      ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,sK3))) = iProver_top
% 3.24/1.00      | r1_tarski(X0_44,sK4) != iProver_top
% 3.24/1.00      | r1_tarski(k1_relat_1(X0_44),X1_44) != iProver_top ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_1614,c_2854]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_17,plain,
% 3.24/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.24/1.00      | k5_relset_1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.24/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_730,plain,
% 3.24/1.00      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X0_46)))
% 3.24/1.00      | k5_relset_1(X1_44,X0_46,X0_44,X2_44) = k7_relat_1(X0_44,X2_44) ),
% 3.24/1.00      inference(subtyping,[status(esa)],[c_17]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1210,plain,
% 3.24/1.00      ( k5_relset_1(X0_44,X0_46,X1_44,X2_44) = k7_relat_1(X1_44,X2_44)
% 3.24/1.00      | m1_subset_1(X1_44,k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_46))) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_730]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2360,plain,
% 3.24/1.00      ( k5_relset_1(sK1,sK3,sK4,X0_44) = k7_relat_1(sK4,X0_44) ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_1213,c_1210]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_19,negated_conjecture,
% 3.24/1.00      ( ~ m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.24/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_728,negated_conjecture,
% 3.24/1.00      ( ~ m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.24/1.00      inference(subtyping,[status(esa)],[c_19]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1212,plain,
% 3.24/1.00      ( m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_728]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2871,plain,
% 3.24/1.00      ( m1_subset_1(k7_relat_1(sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 3.24/1.00      inference(demodulation,[status(thm)],[c_2360,c_1212]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_9406,plain,
% 3.24/1.00      ( r1_tarski(k7_relat_1(sK4,sK2),sK4) != iProver_top
% 3.24/1.00      | r1_tarski(k1_relat_1(k7_relat_1(sK4,sK2)),sK2) != iProver_top ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_8701,c_2871]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_9441,plain,
% 3.24/1.00      ( v4_relat_1(k7_relat_1(sK4,sK2),sK2) != iProver_top
% 3.24/1.00      | r1_tarski(k7_relat_1(sK4,sK2),sK4) != iProver_top
% 3.24/1.00      | v1_relat_1(k7_relat_1(sK4,sK2)) != iProver_top ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_1203,c_9406]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_15,plain,
% 3.24/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.24/1.00      | v1_relat_1(X0) ),
% 3.24/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_732,plain,
% 3.24/1.00      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X0_46)))
% 3.24/1.00      | v1_relat_1(X0_44) ),
% 3.24/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1208,plain,
% 3.24/1.00      ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X0_46))) != iProver_top
% 3.24/1.00      | v1_relat_1(X0_44) = iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_732]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1477,plain,
% 3.24/1.00      ( r1_tarski(X0_44,k2_zfmisc_1(X1_44,X0_46)) != iProver_top
% 3.24/1.00      | v1_relat_1(X0_44) = iProver_top ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_1200,c_1208]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_3549,plain,
% 3.24/1.00      ( r1_tarski(X0_44,sK4) != iProver_top
% 3.24/1.00      | v1_relat_1(X0_44) = iProver_top ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_1614,c_1477]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_16,plain,
% 3.24/1.00      ( v4_relat_1(X0,X1)
% 3.24/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.24/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_731,plain,
% 3.24/1.00      ( v4_relat_1(X0_44,X1_44)
% 3.24/1.00      | ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X0_46))) ),
% 3.24/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1209,plain,
% 3.24/1.00      ( v4_relat_1(X0_44,X1_44) = iProver_top
% 3.24/1.00      | m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X0_46))) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_731]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1598,plain,
% 3.24/1.00      ( v4_relat_1(sK4,sK1) = iProver_top ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_1213,c_1209]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_12,plain,
% 3.24/1.00      ( ~ v4_relat_1(X0,X1)
% 3.24/1.00      | v4_relat_1(k7_relat_1(X0,X2),X2)
% 3.24/1.00      | ~ v1_relat_1(X0) ),
% 3.24/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_735,plain,
% 3.24/1.00      ( ~ v4_relat_1(X0_44,X1_44)
% 3.24/1.00      | v4_relat_1(k7_relat_1(X0_44,X2_44),X2_44)
% 3.24/1.00      | ~ v1_relat_1(X0_44) ),
% 3.24/1.00      inference(subtyping,[status(esa)],[c_12]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1205,plain,
% 3.24/1.00      ( v4_relat_1(X0_44,X1_44) != iProver_top
% 3.24/1.00      | v4_relat_1(k7_relat_1(X0_44,X2_44),X2_44) = iProver_top
% 3.24/1.00      | v1_relat_1(X0_44) != iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_735]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_2507,plain,
% 3.24/1.00      ( v4_relat_1(k7_relat_1(sK4,X0_44),X0_44) = iProver_top
% 3.24/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_1598,c_1205]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_21,plain,
% 3.24/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1336,plain,
% 3.24/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 3.24/1.00      | v1_relat_1(sK4) ),
% 3.24/1.00      inference(instantiation,[status(thm)],[c_732]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_1337,plain,
% 3.24/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 3.24/1.00      | v1_relat_1(sK4) = iProver_top ),
% 3.24/1.00      inference(predicate_to_equality,[status(thm)],[c_1336]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_3066,plain,
% 3.24/1.00      ( v4_relat_1(k7_relat_1(sK4,X0_44),X0_44) = iProver_top ),
% 3.24/1.00      inference(global_propositional_subsumption,
% 3.24/1.00                [status(thm)],
% 3.24/1.00                [c_2507,c_21,c_1337]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_9582,plain,
% 3.24/1.00      ( r1_tarski(k7_relat_1(sK4,sK2),sK4) != iProver_top ),
% 3.24/1.00      inference(forward_subsumption_resolution,
% 3.24/1.00                [status(thm)],
% 3.24/1.00                [c_9441,c_3549,c_3066]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(c_9584,plain,
% 3.24/1.00      ( v1_relat_1(sK4) != iProver_top ),
% 3.24/1.00      inference(superposition,[status(thm)],[c_1207,c_9582]) ).
% 3.24/1.00  
% 3.24/1.00  cnf(contradiction,plain,
% 3.24/1.00      ( $false ),
% 3.24/1.00      inference(minisat,[status(thm)],[c_9584,c_1337,c_21]) ).
% 3.24/1.00  
% 3.24/1.00  
% 3.24/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.24/1.00  
% 3.24/1.00  ------                               Statistics
% 3.24/1.00  
% 3.24/1.00  ------ General
% 3.24/1.00  
% 3.24/1.00  abstr_ref_over_cycles:                  0
% 3.24/1.00  abstr_ref_under_cycles:                 0
% 3.24/1.00  gc_basic_clause_elim:                   0
% 3.24/1.00  forced_gc_time:                         0
% 3.24/1.00  parsing_time:                           0.009
% 3.24/1.00  unif_index_cands_time:                  0.
% 3.24/1.00  unif_index_add_time:                    0.
% 3.24/1.00  orderings_time:                         0.
% 3.24/1.00  out_proof_time:                         0.01
% 3.24/1.00  total_time:                             0.404
% 3.24/1.00  num_of_symbols:                         50
% 3.24/1.00  num_of_terms:                           8461
% 3.24/1.00  
% 3.24/1.00  ------ Preprocessing
% 3.24/1.00  
% 3.24/1.00  num_of_splits:                          0
% 3.24/1.00  num_of_split_atoms:                     0
% 3.24/1.00  num_of_reused_defs:                     0
% 3.24/1.00  num_eq_ax_congr_red:                    28
% 3.24/1.00  num_of_sem_filtered_clauses:            1
% 3.24/1.00  num_of_subtypes:                        3
% 3.24/1.00  monotx_restored_types:                  0
% 3.24/1.00  sat_num_of_epr_types:                   0
% 3.24/1.00  sat_num_of_non_cyclic_types:            0
% 3.24/1.00  sat_guarded_non_collapsed_types:        0
% 3.24/1.00  num_pure_diseq_elim:                    0
% 3.24/1.00  simp_replaced_by:                       0
% 3.24/1.00  res_preprocessed:                       116
% 3.24/1.00  prep_upred:                             0
% 3.24/1.00  prep_unflattend:                        11
% 3.24/1.00  smt_new_axioms:                         0
% 3.24/1.00  pred_elim_cands:                        4
% 3.24/1.00  pred_elim:                              2
% 3.24/1.00  pred_elim_cl:                           3
% 3.24/1.00  pred_elim_cycles:                       5
% 3.24/1.00  merged_defs:                            14
% 3.24/1.00  merged_defs_ncl:                        0
% 3.24/1.00  bin_hyper_res:                          15
% 3.24/1.00  prep_cycles:                            5
% 3.24/1.00  pred_elim_time:                         0.003
% 3.24/1.00  splitting_time:                         0.
% 3.24/1.00  sem_filter_time:                        0.
% 3.24/1.00  monotx_time:                            0.
% 3.24/1.00  subtype_inf_time:                       0.
% 3.24/1.00  
% 3.24/1.00  ------ Problem properties
% 3.24/1.00  
% 3.24/1.00  clauses:                                17
% 3.24/1.00  conjectures:                            2
% 3.24/1.00  epr:                                    1
% 3.24/1.00  horn:                                   16
% 3.24/1.00  ground:                                 2
% 3.24/1.00  unary:                                  2
% 3.24/1.00  binary:                                 6
% 3.24/1.00  lits:                                   41
% 3.24/1.00  lits_eq:                                3
% 3.24/1.00  fd_pure:                                0
% 3.24/1.00  fd_pseudo:                              0
% 3.24/1.00  fd_cond:                                0
% 3.24/1.00  fd_pseudo_cond:                         0
% 3.24/1.00  ac_symbols:                             0
% 3.24/1.00  
% 3.24/1.00  ------ Propositional Solver
% 3.24/1.00  
% 3.24/1.00  prop_solver_calls:                      31
% 3.24/1.00  prop_fast_solver_calls:                 833
% 3.24/1.00  smt_solver_calls:                       0
% 3.24/1.00  smt_fast_solver_calls:                  0
% 3.24/1.00  prop_num_of_clauses:                    4141
% 3.24/1.00  prop_preprocess_simplified:             8957
% 3.24/1.00  prop_fo_subsumed:                       17
% 3.24/1.00  prop_solver_time:                       0.
% 3.24/1.00  smt_solver_time:                        0.
% 3.24/1.00  smt_fast_solver_time:                   0.
% 3.24/1.00  prop_fast_solver_time:                  0.
% 3.24/1.00  prop_unsat_core_time:                   0.
% 3.24/1.00  
% 3.24/1.00  ------ QBF
% 3.24/1.00  
% 3.24/1.00  qbf_q_res:                              0
% 3.24/1.00  qbf_num_tautologies:                    0
% 3.24/1.00  qbf_prep_cycles:                        0
% 3.24/1.00  
% 3.24/1.00  ------ BMC1
% 3.24/1.00  
% 3.24/1.00  bmc1_current_bound:                     -1
% 3.24/1.00  bmc1_last_solved_bound:                 -1
% 3.24/1.00  bmc1_unsat_core_size:                   -1
% 3.24/1.00  bmc1_unsat_core_parents_size:           -1
% 3.24/1.00  bmc1_merge_next_fun:                    0
% 3.24/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.24/1.00  
% 3.24/1.00  ------ Instantiation
% 3.24/1.00  
% 3.24/1.00  inst_num_of_clauses:                    962
% 3.24/1.00  inst_num_in_passive:                    61
% 3.24/1.00  inst_num_in_active:                     456
% 3.24/1.00  inst_num_in_unprocessed:                446
% 3.24/1.00  inst_num_of_loops:                      480
% 3.24/1.00  inst_num_of_learning_restarts:          0
% 3.24/1.00  inst_num_moves_active_passive:          21
% 3.24/1.00  inst_lit_activity:                      0
% 3.24/1.00  inst_lit_activity_moves:                0
% 3.24/1.00  inst_num_tautologies:                   0
% 3.24/1.00  inst_num_prop_implied:                  0
% 3.24/1.00  inst_num_existing_simplified:           0
% 3.24/1.00  inst_num_eq_res_simplified:             0
% 3.24/1.00  inst_num_child_elim:                    0
% 3.24/1.00  inst_num_of_dismatching_blockings:      267
% 3.24/1.00  inst_num_of_non_proper_insts:           808
% 3.24/1.00  inst_num_of_duplicates:                 0
% 3.24/1.00  inst_inst_num_from_inst_to_res:         0
% 3.24/1.00  inst_dismatching_checking_time:         0.
% 3.24/1.00  
% 3.24/1.00  ------ Resolution
% 3.24/1.00  
% 3.24/1.00  res_num_of_clauses:                     0
% 3.24/1.00  res_num_in_passive:                     0
% 3.24/1.00  res_num_in_active:                      0
% 3.24/1.00  res_num_of_loops:                       121
% 3.24/1.00  res_forward_subset_subsumed:            32
% 3.24/1.00  res_backward_subset_subsumed:           4
% 3.24/1.00  res_forward_subsumed:                   0
% 3.24/1.00  res_backward_subsumed:                  0
% 3.24/1.00  res_forward_subsumption_resolution:     0
% 3.24/1.00  res_backward_subsumption_resolution:    0
% 3.24/1.00  res_clause_to_clause_subsumption:       709
% 3.24/1.00  res_orphan_elimination:                 0
% 3.24/1.00  res_tautology_del:                      136
% 3.24/1.00  res_num_eq_res_simplified:              0
% 3.24/1.00  res_num_sel_changes:                    0
% 3.24/1.00  res_moves_from_active_to_pass:          0
% 3.24/1.00  
% 3.24/1.00  ------ Superposition
% 3.24/1.00  
% 3.24/1.00  sup_time_total:                         0.
% 3.24/1.00  sup_time_generating:                    0.
% 3.24/1.00  sup_time_sim_full:                      0.
% 3.24/1.00  sup_time_sim_immed:                     0.
% 3.24/1.00  
% 3.24/1.00  sup_num_of_clauses:                     221
% 3.24/1.00  sup_num_in_active:                      92
% 3.24/1.00  sup_num_in_passive:                     129
% 3.24/1.00  sup_num_of_loops:                       95
% 3.24/1.00  sup_fw_superposition:                   141
% 3.24/1.00  sup_bw_superposition:                   139
% 3.24/1.00  sup_immediate_simplified:               49
% 3.24/1.00  sup_given_eliminated:                   0
% 3.24/1.00  comparisons_done:                       0
% 3.24/1.00  comparisons_avoided:                    0
% 3.24/1.00  
% 3.24/1.00  ------ Simplifications
% 3.24/1.00  
% 3.24/1.00  
% 3.24/1.00  sim_fw_subset_subsumed:                 21
% 3.24/1.00  sim_bw_subset_subsumed:                 3
% 3.24/1.00  sim_fw_subsumed:                        26
% 3.24/1.00  sim_bw_subsumed:                        0
% 3.24/1.00  sim_fw_subsumption_res:                 6
% 3.24/1.00  sim_bw_subsumption_res:                 1
% 3.24/1.00  sim_tautology_del:                      5
% 3.24/1.00  sim_eq_tautology_del:                   4
% 3.24/1.00  sim_eq_res_simp:                        0
% 3.24/1.00  sim_fw_demodulated:                     0
% 3.24/1.00  sim_bw_demodulated:                     2
% 3.24/1.00  sim_light_normalised:                   0
% 3.24/1.00  sim_joinable_taut:                      0
% 3.24/1.00  sim_joinable_simp:                      0
% 3.24/1.00  sim_ac_normalised:                      0
% 3.24/1.00  sim_smt_subsumption:                    0
% 3.24/1.00  
%------------------------------------------------------------------------------
