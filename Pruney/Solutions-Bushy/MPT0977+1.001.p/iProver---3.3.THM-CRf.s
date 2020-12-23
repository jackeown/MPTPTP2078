%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0977+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:33 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 254 expanded)
%              Number of clauses        :   75 ( 115 expanded)
%              Number of leaves         :   17 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  297 ( 605 expanded)
%              Number of equality atoms :  126 ( 171 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
          & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        | ~ r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
          | ~ r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
        | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
      | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f33])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f10])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f38,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f38,f42])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f22])).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f49,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
    | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f51,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_relat_1(sK1)),sK2)
    | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_relat_1(sK0),sK2),sK2) ),
    inference(definition_unfolding,[],[f49,f42,f42])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f44])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_402,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_676,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_402])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_407,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | k2_relset_1(X0_46,X1_46,X0_44) = k2_relat_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_671,plain,
    ( k2_relset_1(X0_46,X1_46,X0_44) = k2_relat_1(X0_44)
    | m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_407])).

cnf(c_1172,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_676,c_671])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_410,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | m1_subset_1(k2_relset_1(X0_46,X1_46,X0_44),k1_zfmisc_1(X1_46)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_668,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top
    | m1_subset_1(k2_relset_1(X0_46,X1_46,X0_44),k1_zfmisc_1(X1_46)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_410])).

cnf(c_1360,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1172,c_668])).

cnf(c_14,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1674,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1360,c_14])).

cnf(c_9,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_11,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_218,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X2)
    | X3 != X1
    | k5_relat_1(X2,k6_relat_1(X3)) = X2
    | k2_relat_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_11])).

cnf(c_219,plain,
    ( ~ m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X1))
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(unflattening,[status(thm)],[c_218])).

cnf(c_400,plain,
    ( ~ m1_subset_1(k2_relat_1(X0_44),k1_zfmisc_1(X0_46))
    | ~ v1_relat_1(X0_44)
    | k5_relat_1(X0_44,k6_relat_1(X0_46)) = X0_44 ),
    inference(subtyping,[status(esa)],[c_219])).

cnf(c_678,plain,
    ( k5_relat_1(X0_44,k6_relat_1(X0_46)) = X0_44
    | m1_subset_1(k2_relat_1(X0_44),k1_zfmisc_1(X0_46)) != iProver_top
    | v1_relat_1(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_400])).

cnf(c_3349,plain,
    ( k5_relat_1(sK2,k6_relat_1(sK1)) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1674,c_678])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_408,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | k1_relset_1(X0_46,X1_46,X0_44) = k1_relat_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_670,plain,
    ( k1_relset_1(X0_46,X1_46,X0_44) = k1_relat_1(X0_44)
    | m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_408])).

cnf(c_963,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_676,c_670])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_411,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | m1_subset_1(k1_relset_1(X0_46,X1_46,X0_44),k1_zfmisc_1(X0_46)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_667,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top
    | m1_subset_1(k1_relset_1(X0_46,X1_46,X0_44),k1_zfmisc_1(X0_46)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_411])).

cnf(c_1147,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_963,c_667])).

cnf(c_1589,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1147,c_14])).

cnf(c_10,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_203,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X2)
    | X3 != X1
    | k5_relat_1(k6_relat_1(X3),X2) = X2
    | k1_relat_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_10])).

cnf(c_204,plain,
    ( ~ m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(X1))
    | ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_203])).

cnf(c_401,plain,
    ( ~ m1_subset_1(k1_relat_1(X0_44),k1_zfmisc_1(X0_46))
    | ~ v1_relat_1(X0_44)
    | k5_relat_1(k6_relat_1(X0_46),X0_44) = X0_44 ),
    inference(subtyping,[status(esa)],[c_204])).

cnf(c_677,plain,
    ( k5_relat_1(k6_relat_1(X0_46),X0_44) = X0_44
    | m1_subset_1(k1_relat_1(X0_44),k1_zfmisc_1(X0_46)) != iProver_top
    | v1_relat_1(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_401])).

cnf(c_2515,plain,
    ( k5_relat_1(k6_relat_1(sK0),sK2) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1589,c_677])).

cnf(c_451,plain,
    ( k5_relat_1(k6_relat_1(X0_46),X0_44) = X0_44
    | m1_subset_1(k1_relat_1(X0_44),k1_zfmisc_1(X0_46)) != iProver_top
    | v1_relat_1(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_401])).

cnf(c_453,plain,
    ( k5_relat_1(k6_relat_1(sK0),sK2) = sK2
    | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_451])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_412,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | v1_relat_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_765,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_412])).

cnf(c_766,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_765])).

cnf(c_2799,plain,
    ( k5_relat_1(k6_relat_1(sK0),sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2515,c_14,c_453,c_766,c_1147])).

cnf(c_3,plain,
    ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_409,plain,
    ( m1_subset_1(k6_relat_1(X0_46),k1_zfmisc_1(k2_zfmisc_1(X0_46,X0_46))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_669,plain,
    ( m1_subset_1(k6_relat_1(X0_46),k1_zfmisc_1(k2_zfmisc_1(X0_46,X0_46))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_409])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_406,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(k2_zfmisc_1(X2_46,X3_46)))
    | k4_relset_1(X2_46,X3_46,X0_46,X1_46,X1_44,X0_44) = k5_relat_1(X1_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_672,plain,
    ( k4_relset_1(X0_46,X1_46,X2_46,X3_46,X0_44,X1_44) = k5_relat_1(X0_44,X1_44)
    | m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top
    | m1_subset_1(X1_44,k1_zfmisc_1(k2_zfmisc_1(X2_46,X3_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_406])).

cnf(c_1323,plain,
    ( k4_relset_1(X0_46,X1_46,sK0,sK1,X0_44,sK2) = k5_relat_1(X0_44,sK2)
    | m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
    inference(superposition,[status(thm)],[c_676,c_672])).

cnf(c_1432,plain,
    ( k4_relset_1(X0_46,X0_46,sK0,sK1,k6_relat_1(X0_46),sK2) = k5_relat_1(k6_relat_1(X0_46),sK2) ),
    inference(superposition,[status(thm)],[c_669,c_1323])).

cnf(c_12,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_relat_1(sK1)),sK2)
    | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_relat_1(sK0),sK2),sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_403,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_relat_1(sK1)),sK2)
    | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_relat_1(sK0),sK2),sK2) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_675,plain,
    ( r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_relat_1(sK1)),sK2) != iProver_top
    | r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_relat_1(sK0),sK2),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_403])).

cnf(c_1520,plain,
    ( r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_relat_1(sK1)),sK2) != iProver_top
    | r2_relset_1(sK0,sK1,k5_relat_1(k6_relat_1(sK0),sK2),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1432,c_675])).

cnf(c_2802,plain,
    ( r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_relat_1(sK1)),sK2) != iProver_top
    | r2_relset_1(sK0,sK1,sK2,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2799,c_1520])).

cnf(c_1756,plain,
    ( m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_409])).

cnf(c_415,plain,
    ( X0_44 != X1_44
    | X2_44 != X1_44
    | X2_44 = X0_44 ),
    theory(equality)).

cnf(c_1657,plain,
    ( k5_relat_1(sK2,k6_relat_1(sK1)) != X0_44
    | sK2 != X0_44
    | sK2 = k5_relat_1(sK2,k6_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_415])).

cnf(c_1658,plain,
    ( k5_relat_1(sK2,k6_relat_1(sK1)) != sK2
    | sK2 = k5_relat_1(sK2,k6_relat_1(sK1))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1657])).

cnf(c_831,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | ~ m1_subset_1(k6_relat_1(X2_46),k1_zfmisc_1(k2_zfmisc_1(X2_46,X2_46)))
    | k4_relset_1(X0_46,X1_46,X2_46,X2_46,X0_44,k6_relat_1(X2_46)) = k5_relat_1(X0_44,k6_relat_1(X2_46)) ),
    inference(instantiation,[status(thm)],[c_406])).

cnf(c_1126,plain,
    ( ~ m1_subset_1(k6_relat_1(X0_46),k1_zfmisc_1(k2_zfmisc_1(X0_46,X0_46)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k4_relset_1(sK0,sK1,X0_46,X0_46,sK2,k6_relat_1(X0_46)) = k5_relat_1(sK2,k6_relat_1(X0_46)) ),
    inference(instantiation,[status(thm)],[c_831])).

cnf(c_1232,plain,
    ( ~ m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_relat_1(sK1)) = k5_relat_1(sK2,k6_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1126])).

cnf(c_1192,plain,
    ( k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_relat_1(sK1)) != X0_44
    | k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_relat_1(sK1)) = sK2
    | sK2 != X0_44 ),
    inference(instantiation,[status(thm)],[c_415])).

cnf(c_1231,plain,
    ( k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_relat_1(sK1)) != k5_relat_1(sK2,k6_relat_1(sK1))
    | k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_relat_1(sK1)) = sK2
    | sK2 != k5_relat_1(sK2,k6_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1192])).

cnf(c_419,plain,
    ( ~ r2_relset_1(X0_46,X1_46,X0_44,X1_44)
    | r2_relset_1(X0_46,X1_46,X2_44,X3_44)
    | X2_44 != X0_44
    | X3_44 != X1_44 ),
    theory(equality)).

cnf(c_851,plain,
    ( r2_relset_1(sK0,sK1,X0_44,X1_44)
    | ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | X0_44 != sK2
    | X1_44 != sK2 ),
    inference(instantiation,[status(thm)],[c_419])).

cnf(c_945,plain,
    ( r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_relat_1(sK1)),sK2)
    | ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_relat_1(sK1)) != sK2
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_851])).

cnf(c_946,plain,
    ( k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_relat_1(sK1)) != sK2
    | sK2 != sK2
    | r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_relat_1(sK1)),sK2) = iProver_top
    | r2_relset_1(sK0,sK1,sK2,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_945])).

cnf(c_7,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_405,plain,
    ( r2_relset_1(X0_46,X1_46,X0_44,X0_44)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_781,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_405])).

cnf(c_782,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_781])).

cnf(c_414,plain,
    ( X0_44 = X0_44 ),
    theory(equality)).

cnf(c_425,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_414])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3349,c_2802,c_1756,c_1658,c_1232,c_1231,c_946,c_782,c_766,c_425,c_14,c_13])).


%------------------------------------------------------------------------------
