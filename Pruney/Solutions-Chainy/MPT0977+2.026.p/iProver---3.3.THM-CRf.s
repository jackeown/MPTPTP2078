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
% DateTime   : Thu Dec  3 12:01:28 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 297 expanded)
%              Number of clauses        :   61 ( 116 expanded)
%              Number of leaves         :   15 (  57 expanded)
%              Depth                    :   16
%              Number of atoms          :  267 ( 729 expanded)
%              Number of equality atoms :   89 ( 139 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
          & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        | ~ r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
          | ~ r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
        | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
      | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f34])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f53,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
    | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
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
    inference(nnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_partfun1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f42,f51])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f49])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_partfun1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f43,f51])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1072,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_14,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1074,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1077,plain,
    ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2186,plain,
    ( k4_relset_1(X0,X1,X2,X2,X3,k6_partfun1(X2)) = k5_relat_1(X3,k6_partfun1(X2))
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1074,c_1077])).

cnf(c_4548,plain,
    ( k4_relset_1(sK0,sK1,X0,X0,sK2,k6_partfun1(X0)) = k5_relat_1(sK2,k6_partfun1(X0)) ),
    inference(superposition,[status(thm)],[c_1072,c_2186])).

cnf(c_2187,plain,
    ( k4_relset_1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1072,c_1077])).

cnf(c_2340,plain,
    ( k4_relset_1(X0,X0,sK0,sK1,k6_partfun1(X0),sK2) = k5_relat_1(k6_partfun1(X0),sK2) ),
    inference(superposition,[status(thm)],[c_1074,c_2187])).

cnf(c_15,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
    | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1073,plain,
    ( r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) != iProver_top
    | r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2531,plain,
    ( r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) != iProver_top
    | r2_relset_1(sK0,sK1,k5_relat_1(k6_partfun1(sK0),sK2),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2340,c_1073])).

cnf(c_8,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_4,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_236,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_8,c_4])).

cnf(c_1070,plain,
    ( r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_236])).

cnf(c_1482,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1072,c_1070])).

cnf(c_17,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1192,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1193,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1192])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_139,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_172,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_2,c_139])).

cnf(c_1263,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_172])).

cnf(c_1425,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1263])).

cnf(c_1426,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1425])).

cnf(c_5,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1550,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1551,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1550])).

cnf(c_1770,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1482,c_17,c_1193,c_1426,c_1551])).

cnf(c_6,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1081,plain,
    ( k5_relat_1(k6_partfun1(X0),X1) = X1
    | r1_tarski(k1_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2178,plain,
    ( k5_relat_1(k6_partfun1(sK0),sK2) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1770,c_1081])).

cnf(c_1503,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1482])).

cnf(c_1742,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),X0)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k6_partfun1(X0),sK2) = sK2 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1744,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k6_partfun1(sK0),sK2) = sK2 ),
    inference(instantiation,[status(thm)],[c_1742])).

cnf(c_2332,plain,
    ( k5_relat_1(k6_partfun1(sK0),sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2178,c_16,c_1192,c_1425,c_1503,c_1550,c_1744])).

cnf(c_2532,plain,
    ( r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) != iProver_top
    | r2_relset_1(sK0,sK1,sK2,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2531,c_2332])).

cnf(c_12,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1236,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1237,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1236])).

cnf(c_2583,plain,
    ( r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2532,c_17,c_1237])).

cnf(c_4574,plain,
    ( r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_partfun1(sK1)),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4548,c_2583])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1078,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1560,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1072,c_1078])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1079,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1767,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1560,c_1079])).

cnf(c_1849,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1767,c_17])).

cnf(c_1083,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1854,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1849,c_1083])).

cnf(c_7,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1080,plain,
    ( k5_relat_1(X0,k6_partfun1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1858,plain,
    ( k5_relat_1(sK2,k6_partfun1(sK1)) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1854,c_1080])).

cnf(c_1897,plain,
    ( k5_relat_1(sK2,k6_partfun1(sK1)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1858,c_17,c_1193,c_1426,c_1551])).

cnf(c_4575,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4574,c_1897])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4575,c_1237,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:37:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.09/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/0.99  
% 2.09/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.09/0.99  
% 2.09/0.99  ------  iProver source info
% 2.09/0.99  
% 2.09/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.09/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.09/0.99  git: non_committed_changes: false
% 2.09/0.99  git: last_make_outside_of_git: false
% 2.09/0.99  
% 2.09/0.99  ------ 
% 2.09/0.99  
% 2.09/0.99  ------ Input Options
% 2.09/0.99  
% 2.09/0.99  --out_options                           all
% 2.09/0.99  --tptp_safe_out                         true
% 2.09/0.99  --problem_path                          ""
% 2.09/0.99  --include_path                          ""
% 2.09/0.99  --clausifier                            res/vclausify_rel
% 2.09/0.99  --clausifier_options                    --mode clausify
% 2.09/0.99  --stdin                                 false
% 2.09/0.99  --stats_out                             all
% 2.09/0.99  
% 2.09/0.99  ------ General Options
% 2.09/0.99  
% 2.09/0.99  --fof                                   false
% 2.09/0.99  --time_out_real                         305.
% 2.09/0.99  --time_out_virtual                      -1.
% 2.09/0.99  --symbol_type_check                     false
% 2.09/0.99  --clausify_out                          false
% 2.09/0.99  --sig_cnt_out                           false
% 2.09/0.99  --trig_cnt_out                          false
% 2.09/0.99  --trig_cnt_out_tolerance                1.
% 2.09/0.99  --trig_cnt_out_sk_spl                   false
% 2.09/0.99  --abstr_cl_out                          false
% 2.09/0.99  
% 2.09/0.99  ------ Global Options
% 2.09/0.99  
% 2.09/0.99  --schedule                              default
% 2.09/0.99  --add_important_lit                     false
% 2.09/0.99  --prop_solver_per_cl                    1000
% 2.09/0.99  --min_unsat_core                        false
% 2.09/0.99  --soft_assumptions                      false
% 2.09/0.99  --soft_lemma_size                       3
% 2.09/0.99  --prop_impl_unit_size                   0
% 2.09/0.99  --prop_impl_unit                        []
% 2.09/0.99  --share_sel_clauses                     true
% 2.09/0.99  --reset_solvers                         false
% 2.09/0.99  --bc_imp_inh                            [conj_cone]
% 2.09/0.99  --conj_cone_tolerance                   3.
% 2.09/0.99  --extra_neg_conj                        none
% 2.09/0.99  --large_theory_mode                     true
% 2.09/0.99  --prolific_symb_bound                   200
% 2.09/0.99  --lt_threshold                          2000
% 2.09/0.99  --clause_weak_htbl                      true
% 2.09/0.99  --gc_record_bc_elim                     false
% 2.09/0.99  
% 2.09/0.99  ------ Preprocessing Options
% 2.09/0.99  
% 2.09/0.99  --preprocessing_flag                    true
% 2.09/0.99  --time_out_prep_mult                    0.1
% 2.09/0.99  --splitting_mode                        input
% 2.09/0.99  --splitting_grd                         true
% 2.09/0.99  --splitting_cvd                         false
% 2.09/0.99  --splitting_cvd_svl                     false
% 2.09/0.99  --splitting_nvd                         32
% 2.09/0.99  --sub_typing                            true
% 2.09/0.99  --prep_gs_sim                           true
% 2.09/0.99  --prep_unflatten                        true
% 2.09/0.99  --prep_res_sim                          true
% 2.09/0.99  --prep_upred                            true
% 2.09/0.99  --prep_sem_filter                       exhaustive
% 2.09/0.99  --prep_sem_filter_out                   false
% 2.09/0.99  --pred_elim                             true
% 2.09/0.99  --res_sim_input                         true
% 2.09/0.99  --eq_ax_congr_red                       true
% 2.09/0.99  --pure_diseq_elim                       true
% 2.09/0.99  --brand_transform                       false
% 2.09/0.99  --non_eq_to_eq                          false
% 2.09/0.99  --prep_def_merge                        true
% 2.09/0.99  --prep_def_merge_prop_impl              false
% 2.09/0.99  --prep_def_merge_mbd                    true
% 2.09/0.99  --prep_def_merge_tr_red                 false
% 2.09/0.99  --prep_def_merge_tr_cl                  false
% 2.09/0.99  --smt_preprocessing                     true
% 2.09/0.99  --smt_ac_axioms                         fast
% 2.09/0.99  --preprocessed_out                      false
% 2.09/0.99  --preprocessed_stats                    false
% 2.09/0.99  
% 2.09/0.99  ------ Abstraction refinement Options
% 2.09/0.99  
% 2.09/0.99  --abstr_ref                             []
% 2.09/0.99  --abstr_ref_prep                        false
% 2.09/0.99  --abstr_ref_until_sat                   false
% 2.09/0.99  --abstr_ref_sig_restrict                funpre
% 2.09/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.09/0.99  --abstr_ref_under                       []
% 2.09/0.99  
% 2.09/0.99  ------ SAT Options
% 2.09/0.99  
% 2.09/0.99  --sat_mode                              false
% 2.09/0.99  --sat_fm_restart_options                ""
% 2.09/0.99  --sat_gr_def                            false
% 2.09/0.99  --sat_epr_types                         true
% 2.09/0.99  --sat_non_cyclic_types                  false
% 2.09/0.99  --sat_finite_models                     false
% 2.09/0.99  --sat_fm_lemmas                         false
% 2.09/0.99  --sat_fm_prep                           false
% 2.09/0.99  --sat_fm_uc_incr                        true
% 2.09/0.99  --sat_out_model                         small
% 2.09/0.99  --sat_out_clauses                       false
% 2.09/0.99  
% 2.09/0.99  ------ QBF Options
% 2.09/0.99  
% 2.09/0.99  --qbf_mode                              false
% 2.09/0.99  --qbf_elim_univ                         false
% 2.09/0.99  --qbf_dom_inst                          none
% 2.09/0.99  --qbf_dom_pre_inst                      false
% 2.09/0.99  --qbf_sk_in                             false
% 2.09/0.99  --qbf_pred_elim                         true
% 2.09/0.99  --qbf_split                             512
% 2.09/0.99  
% 2.09/0.99  ------ BMC1 Options
% 2.09/0.99  
% 2.09/0.99  --bmc1_incremental                      false
% 2.09/0.99  --bmc1_axioms                           reachable_all
% 2.09/0.99  --bmc1_min_bound                        0
% 2.09/0.99  --bmc1_max_bound                        -1
% 2.09/0.99  --bmc1_max_bound_default                -1
% 2.09/0.99  --bmc1_symbol_reachability              true
% 2.09/0.99  --bmc1_property_lemmas                  false
% 2.09/0.99  --bmc1_k_induction                      false
% 2.09/0.99  --bmc1_non_equiv_states                 false
% 2.09/0.99  --bmc1_deadlock                         false
% 2.09/0.99  --bmc1_ucm                              false
% 2.09/0.99  --bmc1_add_unsat_core                   none
% 2.09/0.99  --bmc1_unsat_core_children              false
% 2.09/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.09/0.99  --bmc1_out_stat                         full
% 2.09/0.99  --bmc1_ground_init                      false
% 2.09/0.99  --bmc1_pre_inst_next_state              false
% 2.09/0.99  --bmc1_pre_inst_state                   false
% 2.09/0.99  --bmc1_pre_inst_reach_state             false
% 2.09/0.99  --bmc1_out_unsat_core                   false
% 2.09/0.99  --bmc1_aig_witness_out                  false
% 2.09/0.99  --bmc1_verbose                          false
% 2.09/0.99  --bmc1_dump_clauses_tptp                false
% 2.09/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.09/0.99  --bmc1_dump_file                        -
% 2.09/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.09/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.09/0.99  --bmc1_ucm_extend_mode                  1
% 2.09/0.99  --bmc1_ucm_init_mode                    2
% 2.09/0.99  --bmc1_ucm_cone_mode                    none
% 2.09/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.09/0.99  --bmc1_ucm_relax_model                  4
% 2.09/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.09/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.09/0.99  --bmc1_ucm_layered_model                none
% 2.09/0.99  --bmc1_ucm_max_lemma_size               10
% 2.09/0.99  
% 2.09/0.99  ------ AIG Options
% 2.09/0.99  
% 2.09/0.99  --aig_mode                              false
% 2.09/0.99  
% 2.09/0.99  ------ Instantiation Options
% 2.09/0.99  
% 2.09/0.99  --instantiation_flag                    true
% 2.09/0.99  --inst_sos_flag                         false
% 2.09/0.99  --inst_sos_phase                        true
% 2.09/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.09/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.09/0.99  --inst_lit_sel_side                     num_symb
% 2.09/0.99  --inst_solver_per_active                1400
% 2.09/0.99  --inst_solver_calls_frac                1.
% 2.09/0.99  --inst_passive_queue_type               priority_queues
% 2.09/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.09/0.99  --inst_passive_queues_freq              [25;2]
% 2.09/0.99  --inst_dismatching                      true
% 2.09/0.99  --inst_eager_unprocessed_to_passive     true
% 2.09/0.99  --inst_prop_sim_given                   true
% 2.09/0.99  --inst_prop_sim_new                     false
% 2.09/0.99  --inst_subs_new                         false
% 2.09/0.99  --inst_eq_res_simp                      false
% 2.09/0.99  --inst_subs_given                       false
% 2.09/0.99  --inst_orphan_elimination               true
% 2.09/0.99  --inst_learning_loop_flag               true
% 2.09/0.99  --inst_learning_start                   3000
% 2.09/0.99  --inst_learning_factor                  2
% 2.09/0.99  --inst_start_prop_sim_after_learn       3
% 2.09/0.99  --inst_sel_renew                        solver
% 2.09/0.99  --inst_lit_activity_flag                true
% 2.09/0.99  --inst_restr_to_given                   false
% 2.09/0.99  --inst_activity_threshold               500
% 2.09/0.99  --inst_out_proof                        true
% 2.09/0.99  
% 2.09/0.99  ------ Resolution Options
% 2.09/0.99  
% 2.09/0.99  --resolution_flag                       true
% 2.09/0.99  --res_lit_sel                           adaptive
% 2.09/0.99  --res_lit_sel_side                      none
% 2.09/0.99  --res_ordering                          kbo
% 2.09/0.99  --res_to_prop_solver                    active
% 2.09/0.99  --res_prop_simpl_new                    false
% 2.09/0.99  --res_prop_simpl_given                  true
% 2.09/0.99  --res_passive_queue_type                priority_queues
% 2.09/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.09/0.99  --res_passive_queues_freq               [15;5]
% 2.09/0.99  --res_forward_subs                      full
% 2.09/0.99  --res_backward_subs                     full
% 2.09/0.99  --res_forward_subs_resolution           true
% 2.09/0.99  --res_backward_subs_resolution          true
% 2.09/0.99  --res_orphan_elimination                true
% 2.09/0.99  --res_time_limit                        2.
% 2.09/0.99  --res_out_proof                         true
% 2.09/0.99  
% 2.09/0.99  ------ Superposition Options
% 2.09/0.99  
% 2.09/0.99  --superposition_flag                    true
% 2.09/0.99  --sup_passive_queue_type                priority_queues
% 2.09/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.09/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.09/0.99  --demod_completeness_check              fast
% 2.09/0.99  --demod_use_ground                      true
% 2.09/0.99  --sup_to_prop_solver                    passive
% 2.09/0.99  --sup_prop_simpl_new                    true
% 2.09/0.99  --sup_prop_simpl_given                  true
% 2.09/0.99  --sup_fun_splitting                     false
% 2.09/0.99  --sup_smt_interval                      50000
% 2.09/0.99  
% 2.09/0.99  ------ Superposition Simplification Setup
% 2.09/0.99  
% 2.09/0.99  --sup_indices_passive                   []
% 2.09/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.09/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_full_bw                           [BwDemod]
% 2.09/0.99  --sup_immed_triv                        [TrivRules]
% 2.09/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.09/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_immed_bw_main                     []
% 2.09/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.09/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/0.99  
% 2.09/0.99  ------ Combination Options
% 2.09/0.99  
% 2.09/0.99  --comb_res_mult                         3
% 2.09/0.99  --comb_sup_mult                         2
% 2.09/0.99  --comb_inst_mult                        10
% 2.09/0.99  
% 2.09/0.99  ------ Debug Options
% 2.09/0.99  
% 2.09/0.99  --dbg_backtrace                         false
% 2.09/0.99  --dbg_dump_prop_clauses                 false
% 2.09/0.99  --dbg_dump_prop_clauses_file            -
% 2.09/0.99  --dbg_out_stat                          false
% 2.09/0.99  ------ Parsing...
% 2.09/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.09/0.99  
% 2.09/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.09/0.99  
% 2.09/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.09/0.99  
% 2.09/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.09/0.99  ------ Proving...
% 2.09/0.99  ------ Problem Properties 
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  clauses                                 15
% 2.09/0.99  conjectures                             2
% 2.09/0.99  EPR                                     1
% 2.09/0.99  Horn                                    15
% 2.09/0.99  unary                                   3
% 2.09/0.99  binary                                  6
% 2.09/0.99  lits                                    34
% 2.09/0.99  lits eq                                 5
% 2.09/0.99  fd_pure                                 0
% 2.09/0.99  fd_pseudo                               0
% 2.09/0.99  fd_cond                                 0
% 2.09/0.99  fd_pseudo_cond                          1
% 2.09/0.99  AC symbols                              0
% 2.09/0.99  
% 2.09/0.99  ------ Schedule dynamic 5 is on 
% 2.09/0.99  
% 2.09/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  ------ 
% 2.09/0.99  Current options:
% 2.09/0.99  ------ 
% 2.09/0.99  
% 2.09/0.99  ------ Input Options
% 2.09/0.99  
% 2.09/0.99  --out_options                           all
% 2.09/0.99  --tptp_safe_out                         true
% 2.09/0.99  --problem_path                          ""
% 2.09/0.99  --include_path                          ""
% 2.09/0.99  --clausifier                            res/vclausify_rel
% 2.09/0.99  --clausifier_options                    --mode clausify
% 2.09/0.99  --stdin                                 false
% 2.09/0.99  --stats_out                             all
% 2.09/0.99  
% 2.09/0.99  ------ General Options
% 2.09/0.99  
% 2.09/0.99  --fof                                   false
% 2.09/0.99  --time_out_real                         305.
% 2.09/0.99  --time_out_virtual                      -1.
% 2.09/0.99  --symbol_type_check                     false
% 2.09/0.99  --clausify_out                          false
% 2.09/0.99  --sig_cnt_out                           false
% 2.09/0.99  --trig_cnt_out                          false
% 2.09/0.99  --trig_cnt_out_tolerance                1.
% 2.09/0.99  --trig_cnt_out_sk_spl                   false
% 2.09/0.99  --abstr_cl_out                          false
% 2.09/0.99  
% 2.09/0.99  ------ Global Options
% 2.09/0.99  
% 2.09/0.99  --schedule                              default
% 2.09/0.99  --add_important_lit                     false
% 2.09/0.99  --prop_solver_per_cl                    1000
% 2.09/0.99  --min_unsat_core                        false
% 2.09/0.99  --soft_assumptions                      false
% 2.09/0.99  --soft_lemma_size                       3
% 2.09/0.99  --prop_impl_unit_size                   0
% 2.09/0.99  --prop_impl_unit                        []
% 2.09/0.99  --share_sel_clauses                     true
% 2.09/0.99  --reset_solvers                         false
% 2.09/0.99  --bc_imp_inh                            [conj_cone]
% 2.09/0.99  --conj_cone_tolerance                   3.
% 2.09/0.99  --extra_neg_conj                        none
% 2.09/0.99  --large_theory_mode                     true
% 2.09/0.99  --prolific_symb_bound                   200
% 2.09/0.99  --lt_threshold                          2000
% 2.09/0.99  --clause_weak_htbl                      true
% 2.09/0.99  --gc_record_bc_elim                     false
% 2.09/0.99  
% 2.09/0.99  ------ Preprocessing Options
% 2.09/0.99  
% 2.09/0.99  --preprocessing_flag                    true
% 2.09/0.99  --time_out_prep_mult                    0.1
% 2.09/0.99  --splitting_mode                        input
% 2.09/0.99  --splitting_grd                         true
% 2.09/0.99  --splitting_cvd                         false
% 2.09/0.99  --splitting_cvd_svl                     false
% 2.09/0.99  --splitting_nvd                         32
% 2.09/0.99  --sub_typing                            true
% 2.09/0.99  --prep_gs_sim                           true
% 2.09/0.99  --prep_unflatten                        true
% 2.09/0.99  --prep_res_sim                          true
% 2.09/0.99  --prep_upred                            true
% 2.09/0.99  --prep_sem_filter                       exhaustive
% 2.09/0.99  --prep_sem_filter_out                   false
% 2.09/0.99  --pred_elim                             true
% 2.09/0.99  --res_sim_input                         true
% 2.09/0.99  --eq_ax_congr_red                       true
% 2.09/0.99  --pure_diseq_elim                       true
% 2.09/0.99  --brand_transform                       false
% 2.09/0.99  --non_eq_to_eq                          false
% 2.09/0.99  --prep_def_merge                        true
% 2.09/0.99  --prep_def_merge_prop_impl              false
% 2.09/0.99  --prep_def_merge_mbd                    true
% 2.09/0.99  --prep_def_merge_tr_red                 false
% 2.09/0.99  --prep_def_merge_tr_cl                  false
% 2.09/0.99  --smt_preprocessing                     true
% 2.09/0.99  --smt_ac_axioms                         fast
% 2.09/0.99  --preprocessed_out                      false
% 2.09/0.99  --preprocessed_stats                    false
% 2.09/0.99  
% 2.09/0.99  ------ Abstraction refinement Options
% 2.09/0.99  
% 2.09/0.99  --abstr_ref                             []
% 2.09/0.99  --abstr_ref_prep                        false
% 2.09/0.99  --abstr_ref_until_sat                   false
% 2.09/0.99  --abstr_ref_sig_restrict                funpre
% 2.09/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.09/0.99  --abstr_ref_under                       []
% 2.09/0.99  
% 2.09/0.99  ------ SAT Options
% 2.09/0.99  
% 2.09/0.99  --sat_mode                              false
% 2.09/0.99  --sat_fm_restart_options                ""
% 2.09/0.99  --sat_gr_def                            false
% 2.09/0.99  --sat_epr_types                         true
% 2.09/0.99  --sat_non_cyclic_types                  false
% 2.09/0.99  --sat_finite_models                     false
% 2.09/0.99  --sat_fm_lemmas                         false
% 2.09/0.99  --sat_fm_prep                           false
% 2.09/0.99  --sat_fm_uc_incr                        true
% 2.09/0.99  --sat_out_model                         small
% 2.09/0.99  --sat_out_clauses                       false
% 2.09/0.99  
% 2.09/0.99  ------ QBF Options
% 2.09/0.99  
% 2.09/0.99  --qbf_mode                              false
% 2.09/0.99  --qbf_elim_univ                         false
% 2.09/0.99  --qbf_dom_inst                          none
% 2.09/0.99  --qbf_dom_pre_inst                      false
% 2.09/0.99  --qbf_sk_in                             false
% 2.09/0.99  --qbf_pred_elim                         true
% 2.09/0.99  --qbf_split                             512
% 2.09/0.99  
% 2.09/0.99  ------ BMC1 Options
% 2.09/0.99  
% 2.09/0.99  --bmc1_incremental                      false
% 2.09/0.99  --bmc1_axioms                           reachable_all
% 2.09/0.99  --bmc1_min_bound                        0
% 2.09/0.99  --bmc1_max_bound                        -1
% 2.09/0.99  --bmc1_max_bound_default                -1
% 2.09/0.99  --bmc1_symbol_reachability              true
% 2.09/0.99  --bmc1_property_lemmas                  false
% 2.09/0.99  --bmc1_k_induction                      false
% 2.09/0.99  --bmc1_non_equiv_states                 false
% 2.09/0.99  --bmc1_deadlock                         false
% 2.09/0.99  --bmc1_ucm                              false
% 2.09/0.99  --bmc1_add_unsat_core                   none
% 2.09/0.99  --bmc1_unsat_core_children              false
% 2.09/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.09/0.99  --bmc1_out_stat                         full
% 2.09/0.99  --bmc1_ground_init                      false
% 2.09/0.99  --bmc1_pre_inst_next_state              false
% 2.09/0.99  --bmc1_pre_inst_state                   false
% 2.09/0.99  --bmc1_pre_inst_reach_state             false
% 2.09/0.99  --bmc1_out_unsat_core                   false
% 2.09/0.99  --bmc1_aig_witness_out                  false
% 2.09/0.99  --bmc1_verbose                          false
% 2.09/0.99  --bmc1_dump_clauses_tptp                false
% 2.09/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.09/0.99  --bmc1_dump_file                        -
% 2.09/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.09/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.09/0.99  --bmc1_ucm_extend_mode                  1
% 2.09/0.99  --bmc1_ucm_init_mode                    2
% 2.09/0.99  --bmc1_ucm_cone_mode                    none
% 2.09/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.09/0.99  --bmc1_ucm_relax_model                  4
% 2.09/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.09/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.09/0.99  --bmc1_ucm_layered_model                none
% 2.09/0.99  --bmc1_ucm_max_lemma_size               10
% 2.09/0.99  
% 2.09/0.99  ------ AIG Options
% 2.09/0.99  
% 2.09/0.99  --aig_mode                              false
% 2.09/0.99  
% 2.09/0.99  ------ Instantiation Options
% 2.09/0.99  
% 2.09/0.99  --instantiation_flag                    true
% 2.09/0.99  --inst_sos_flag                         false
% 2.09/0.99  --inst_sos_phase                        true
% 2.09/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.09/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.09/0.99  --inst_lit_sel_side                     none
% 2.09/0.99  --inst_solver_per_active                1400
% 2.09/0.99  --inst_solver_calls_frac                1.
% 2.09/0.99  --inst_passive_queue_type               priority_queues
% 2.09/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.09/0.99  --inst_passive_queues_freq              [25;2]
% 2.09/0.99  --inst_dismatching                      true
% 2.09/0.99  --inst_eager_unprocessed_to_passive     true
% 2.09/0.99  --inst_prop_sim_given                   true
% 2.09/0.99  --inst_prop_sim_new                     false
% 2.09/0.99  --inst_subs_new                         false
% 2.09/0.99  --inst_eq_res_simp                      false
% 2.09/0.99  --inst_subs_given                       false
% 2.09/0.99  --inst_orphan_elimination               true
% 2.09/0.99  --inst_learning_loop_flag               true
% 2.09/0.99  --inst_learning_start                   3000
% 2.09/0.99  --inst_learning_factor                  2
% 2.09/0.99  --inst_start_prop_sim_after_learn       3
% 2.09/0.99  --inst_sel_renew                        solver
% 2.09/0.99  --inst_lit_activity_flag                true
% 2.09/0.99  --inst_restr_to_given                   false
% 2.09/0.99  --inst_activity_threshold               500
% 2.09/0.99  --inst_out_proof                        true
% 2.09/0.99  
% 2.09/0.99  ------ Resolution Options
% 2.09/0.99  
% 2.09/0.99  --resolution_flag                       false
% 2.09/0.99  --res_lit_sel                           adaptive
% 2.09/0.99  --res_lit_sel_side                      none
% 2.09/0.99  --res_ordering                          kbo
% 2.09/0.99  --res_to_prop_solver                    active
% 2.09/0.99  --res_prop_simpl_new                    false
% 2.09/0.99  --res_prop_simpl_given                  true
% 2.09/0.99  --res_passive_queue_type                priority_queues
% 2.09/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.09/0.99  --res_passive_queues_freq               [15;5]
% 2.09/0.99  --res_forward_subs                      full
% 2.09/0.99  --res_backward_subs                     full
% 2.09/0.99  --res_forward_subs_resolution           true
% 2.09/0.99  --res_backward_subs_resolution          true
% 2.09/0.99  --res_orphan_elimination                true
% 2.09/0.99  --res_time_limit                        2.
% 2.09/0.99  --res_out_proof                         true
% 2.09/0.99  
% 2.09/0.99  ------ Superposition Options
% 2.09/0.99  
% 2.09/0.99  --superposition_flag                    true
% 2.09/0.99  --sup_passive_queue_type                priority_queues
% 2.09/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.09/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.09/0.99  --demod_completeness_check              fast
% 2.09/0.99  --demod_use_ground                      true
% 2.09/0.99  --sup_to_prop_solver                    passive
% 2.09/0.99  --sup_prop_simpl_new                    true
% 2.09/0.99  --sup_prop_simpl_given                  true
% 2.09/0.99  --sup_fun_splitting                     false
% 2.09/0.99  --sup_smt_interval                      50000
% 2.09/0.99  
% 2.09/0.99  ------ Superposition Simplification Setup
% 2.09/0.99  
% 2.09/0.99  --sup_indices_passive                   []
% 2.09/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.09/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.09/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_full_bw                           [BwDemod]
% 2.09/0.99  --sup_immed_triv                        [TrivRules]
% 2.09/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.09/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_immed_bw_main                     []
% 2.09/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.09/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.09/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.09/0.99  
% 2.09/0.99  ------ Combination Options
% 2.09/0.99  
% 2.09/0.99  --comb_res_mult                         3
% 2.09/0.99  --comb_sup_mult                         2
% 2.09/0.99  --comb_inst_mult                        10
% 2.09/0.99  
% 2.09/0.99  ------ Debug Options
% 2.09/0.99  
% 2.09/0.99  --dbg_backtrace                         false
% 2.09/0.99  --dbg_dump_prop_clauses                 false
% 2.09/0.99  --dbg_dump_prop_clauses_file            -
% 2.09/0.99  --dbg_out_stat                          false
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  ------ Proving...
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  % SZS status Theorem for theBenchmark.p
% 2.09/0.99  
% 2.09/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.09/0.99  
% 2.09/0.99  fof(f14,conjecture,(
% 2.09/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)))),
% 2.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f15,negated_conjecture,(
% 2.09/0.99    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)))),
% 2.09/0.99    inference(negated_conjecture,[],[f14])).
% 2.09/0.99  
% 2.09/0.99  fof(f30,plain,(
% 2.09/0.99    ? [X0,X1,X2] : ((~r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) | ~r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.09/0.99    inference(ennf_transformation,[],[f15])).
% 2.09/0.99  
% 2.09/0.99  fof(f34,plain,(
% 2.09/0.99    ? [X0,X1,X2] : ((~r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) | ~r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 2.09/0.99    introduced(choice_axiom,[])).
% 2.09/0.99  
% 2.09/0.99  fof(f35,plain,(
% 2.09/0.99    (~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.09/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f34])).
% 2.09/0.99  
% 2.09/0.99  fof(f52,plain,(
% 2.09/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.09/0.99    inference(cnf_transformation,[],[f35])).
% 2.09/0.99  
% 2.09/0.99  fof(f12,axiom,(
% 2.09/0.99    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f50,plain,(
% 2.09/0.99    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.09/0.99    inference(cnf_transformation,[],[f12])).
% 2.09/0.99  
% 2.09/0.99  fof(f13,axiom,(
% 2.09/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f51,plain,(
% 2.09/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f13])).
% 2.09/0.99  
% 2.09/0.99  fof(f56,plain,(
% 2.09/0.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.09/0.99    inference(definition_unfolding,[],[f50,f51])).
% 2.09/0.99  
% 2.09/0.99  fof(f10,axiom,(
% 2.09/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5))),
% 2.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f26,plain,(
% 2.09/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.09/0.99    inference(ennf_transformation,[],[f10])).
% 2.09/0.99  
% 2.09/0.99  fof(f27,plain,(
% 2.09/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.09/0.99    inference(flattening,[],[f26])).
% 2.09/0.99  
% 2.09/0.99  fof(f47,plain,(
% 2.09/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.09/0.99    inference(cnf_transformation,[],[f27])).
% 2.09/0.99  
% 2.09/0.99  fof(f53,plain,(
% 2.09/0.99    ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)),
% 2.09/0.99    inference(cnf_transformation,[],[f35])).
% 2.09/0.99  
% 2.09/0.99  fof(f7,axiom,(
% 2.09/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f16,plain,(
% 2.09/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.09/0.99    inference(pure_predicate_removal,[],[f7])).
% 2.09/0.99  
% 2.09/0.99  fof(f23,plain,(
% 2.09/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.09/0.99    inference(ennf_transformation,[],[f16])).
% 2.09/0.99  
% 2.09/0.99  fof(f44,plain,(
% 2.09/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.09/0.99    inference(cnf_transformation,[],[f23])).
% 2.09/0.99  
% 2.09/0.99  fof(f3,axiom,(
% 2.09/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f18,plain,(
% 2.09/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.09/0.99    inference(ennf_transformation,[],[f3])).
% 2.09/0.99  
% 2.09/0.99  fof(f32,plain,(
% 2.09/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.09/0.99    inference(nnf_transformation,[],[f18])).
% 2.09/0.99  
% 2.09/0.99  fof(f39,plain,(
% 2.09/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f32])).
% 2.09/0.99  
% 2.09/0.99  fof(f1,axiom,(
% 2.09/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f31,plain,(
% 2.09/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.09/0.99    inference(nnf_transformation,[],[f1])).
% 2.09/0.99  
% 2.09/0.99  fof(f36,plain,(
% 2.09/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.09/0.99    inference(cnf_transformation,[],[f31])).
% 2.09/0.99  
% 2.09/0.99  fof(f2,axiom,(
% 2.09/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f17,plain,(
% 2.09/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.09/0.99    inference(ennf_transformation,[],[f2])).
% 2.09/0.99  
% 2.09/0.99  fof(f38,plain,(
% 2.09/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f17])).
% 2.09/0.99  
% 2.09/0.99  fof(f37,plain,(
% 2.09/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f31])).
% 2.09/0.99  
% 2.09/0.99  fof(f4,axiom,(
% 2.09/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f41,plain,(
% 2.09/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.09/0.99    inference(cnf_transformation,[],[f4])).
% 2.09/0.99  
% 2.09/0.99  fof(f5,axiom,(
% 2.09/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 2.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f19,plain,(
% 2.09/0.99    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.09/0.99    inference(ennf_transformation,[],[f5])).
% 2.09/0.99  
% 2.09/0.99  fof(f20,plain,(
% 2.09/0.99    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.09/0.99    inference(flattening,[],[f19])).
% 2.09/0.99  
% 2.09/0.99  fof(f42,plain,(
% 2.09/0.99    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f20])).
% 2.09/0.99  
% 2.09/0.99  fof(f54,plain,(
% 2.09/0.99    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.09/0.99    inference(definition_unfolding,[],[f42,f51])).
% 2.09/0.99  
% 2.09/0.99  fof(f11,axiom,(
% 2.09/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f28,plain,(
% 2.09/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.09/0.99    inference(ennf_transformation,[],[f11])).
% 2.09/0.99  
% 2.09/0.99  fof(f29,plain,(
% 2.09/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.09/0.99    inference(flattening,[],[f28])).
% 2.09/0.99  
% 2.09/0.99  fof(f33,plain,(
% 2.09/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.09/0.99    inference(nnf_transformation,[],[f29])).
% 2.09/0.99  
% 2.09/0.99  fof(f49,plain,(
% 2.09/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.09/0.99    inference(cnf_transformation,[],[f33])).
% 2.09/0.99  
% 2.09/0.99  fof(f57,plain,(
% 2.09/0.99    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.09/0.99    inference(equality_resolution,[],[f49])).
% 2.09/0.99  
% 2.09/0.99  fof(f9,axiom,(
% 2.09/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f25,plain,(
% 2.09/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.09/0.99    inference(ennf_transformation,[],[f9])).
% 2.09/0.99  
% 2.09/0.99  fof(f46,plain,(
% 2.09/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.09/0.99    inference(cnf_transformation,[],[f25])).
% 2.09/0.99  
% 2.09/0.99  fof(f8,axiom,(
% 2.09/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 2.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f24,plain,(
% 2.09/0.99    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.09/0.99    inference(ennf_transformation,[],[f8])).
% 2.09/0.99  
% 2.09/0.99  fof(f45,plain,(
% 2.09/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.09/0.99    inference(cnf_transformation,[],[f24])).
% 2.09/0.99  
% 2.09/0.99  fof(f6,axiom,(
% 2.09/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 2.09/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.09/0.99  
% 2.09/0.99  fof(f21,plain,(
% 2.09/0.99    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.09/0.99    inference(ennf_transformation,[],[f6])).
% 2.09/0.99  
% 2.09/0.99  fof(f22,plain,(
% 2.09/0.99    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.09/0.99    inference(flattening,[],[f21])).
% 2.09/0.99  
% 2.09/0.99  fof(f43,plain,(
% 2.09/0.99    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.09/0.99    inference(cnf_transformation,[],[f22])).
% 2.09/0.99  
% 2.09/0.99  fof(f55,plain,(
% 2.09/0.99    ( ! [X0,X1] : (k5_relat_1(X1,k6_partfun1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.09/0.99    inference(definition_unfolding,[],[f43,f51])).
% 2.09/0.99  
% 2.09/0.99  cnf(c_16,negated_conjecture,
% 2.09/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.09/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1072,plain,
% 2.09/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_14,plain,
% 2.09/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.09/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1074,plain,
% 2.09/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_11,plain,
% 2.09/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.09/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.09/0.99      | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 2.09/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1077,plain,
% 2.09/0.99      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 2.09/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 2.09/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2186,plain,
% 2.09/0.99      ( k4_relset_1(X0,X1,X2,X2,X3,k6_partfun1(X2)) = k5_relat_1(X3,k6_partfun1(X2))
% 2.09/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.09/0.99      inference(superposition,[status(thm)],[c_1074,c_1077]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_4548,plain,
% 2.09/0.99      ( k4_relset_1(sK0,sK1,X0,X0,sK2,k6_partfun1(X0)) = k5_relat_1(sK2,k6_partfun1(X0)) ),
% 2.09/0.99      inference(superposition,[status(thm)],[c_1072,c_2186]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2187,plain,
% 2.09/0.99      ( k4_relset_1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
% 2.09/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.09/0.99      inference(superposition,[status(thm)],[c_1072,c_1077]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2340,plain,
% 2.09/0.99      ( k4_relset_1(X0,X0,sK0,sK1,k6_partfun1(X0),sK2) = k5_relat_1(k6_partfun1(X0),sK2) ),
% 2.09/0.99      inference(superposition,[status(thm)],[c_1074,c_2187]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_15,negated_conjecture,
% 2.09/0.99      ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
% 2.09/0.99      | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) ),
% 2.09/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1073,plain,
% 2.09/0.99      ( r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) != iProver_top
% 2.09/0.99      | r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2531,plain,
% 2.09/0.99      ( r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) != iProver_top
% 2.09/0.99      | r2_relset_1(sK0,sK1,k5_relat_1(k6_partfun1(sK0),sK2),sK2) != iProver_top ),
% 2.09/0.99      inference(demodulation,[status(thm)],[c_2340,c_1073]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_8,plain,
% 2.09/0.99      ( v4_relat_1(X0,X1)
% 2.09/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.09/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_4,plain,
% 2.09/0.99      ( ~ v4_relat_1(X0,X1)
% 2.09/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 2.09/0.99      | ~ v1_relat_1(X0) ),
% 2.09/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_236,plain,
% 2.09/0.99      ( r1_tarski(k1_relat_1(X0),X1)
% 2.09/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.09/0.99      | ~ v1_relat_1(X0) ),
% 2.09/0.99      inference(resolution,[status(thm)],[c_8,c_4]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1070,plain,
% 2.09/0.99      ( r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 2.09/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.09/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_236]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1482,plain,
% 2.09/0.99      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
% 2.09/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.09/0.99      inference(superposition,[status(thm)],[c_1072,c_1070]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_17,plain,
% 2.09/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1,plain,
% 2.09/0.99      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.09/0.99      inference(cnf_transformation,[],[f36]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1192,plain,
% 2.09/0.99      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
% 2.09/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1193,plain,
% 2.09/0.99      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top
% 2.09/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_1192]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2,plain,
% 2.09/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.09/0.99      | ~ v1_relat_1(X1)
% 2.09/0.99      | v1_relat_1(X0) ),
% 2.09/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_0,plain,
% 2.09/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.09/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_139,plain,
% 2.09/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.09/0.99      inference(prop_impl,[status(thm)],[c_0]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_172,plain,
% 2.09/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.09/0.99      inference(bin_hyper_res,[status(thm)],[c_2,c_139]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1263,plain,
% 2.09/0.99      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 2.09/0.99      | v1_relat_1(X0)
% 2.09/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_172]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1425,plain,
% 2.09/0.99      ( ~ r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
% 2.09/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 2.09/0.99      | v1_relat_1(sK2) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_1263]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1426,plain,
% 2.09/0.99      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) != iProver_top
% 2.09/0.99      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 2.09/0.99      | v1_relat_1(sK2) = iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_1425]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_5,plain,
% 2.09/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.09/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1550,plain,
% 2.09/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1551,plain,
% 2.09/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_1550]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1770,plain,
% 2.09/0.99      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 2.09/0.99      inference(global_propositional_subsumption,
% 2.09/0.99                [status(thm)],
% 2.09/0.99                [c_1482,c_17,c_1193,c_1426,c_1551]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_6,plain,
% 2.09/0.99      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 2.09/0.99      | ~ v1_relat_1(X0)
% 2.09/0.99      | k5_relat_1(k6_partfun1(X1),X0) = X0 ),
% 2.09/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1081,plain,
% 2.09/0.99      ( k5_relat_1(k6_partfun1(X0),X1) = X1
% 2.09/0.99      | r1_tarski(k1_relat_1(X1),X0) != iProver_top
% 2.09/0.99      | v1_relat_1(X1) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2178,plain,
% 2.09/0.99      ( k5_relat_1(k6_partfun1(sK0),sK2) = sK2
% 2.09/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.09/0.99      inference(superposition,[status(thm)],[c_1770,c_1081]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1503,plain,
% 2.09/0.99      ( r1_tarski(k1_relat_1(sK2),sK0) | ~ v1_relat_1(sK2) ),
% 2.09/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1482]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1742,plain,
% 2.09/0.99      ( ~ r1_tarski(k1_relat_1(sK2),X0)
% 2.09/0.99      | ~ v1_relat_1(sK2)
% 2.09/0.99      | k5_relat_1(k6_partfun1(X0),sK2) = sK2 ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1744,plain,
% 2.09/0.99      ( ~ r1_tarski(k1_relat_1(sK2),sK0)
% 2.09/0.99      | ~ v1_relat_1(sK2)
% 2.09/0.99      | k5_relat_1(k6_partfun1(sK0),sK2) = sK2 ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_1742]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2332,plain,
% 2.09/0.99      ( k5_relat_1(k6_partfun1(sK0),sK2) = sK2 ),
% 2.09/0.99      inference(global_propositional_subsumption,
% 2.09/0.99                [status(thm)],
% 2.09/0.99                [c_2178,c_16,c_1192,c_1425,c_1503,c_1550,c_1744]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2532,plain,
% 2.09/0.99      ( r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) != iProver_top
% 2.09/0.99      | r2_relset_1(sK0,sK1,sK2,sK2) != iProver_top ),
% 2.09/0.99      inference(light_normalisation,[status(thm)],[c_2531,c_2332]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_12,plain,
% 2.09/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 2.09/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.09/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1236,plain,
% 2.09/0.99      ( r2_relset_1(sK0,sK1,sK2,sK2)
% 2.09/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.09/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1237,plain,
% 2.09/0.99      ( r2_relset_1(sK0,sK1,sK2,sK2) = iProver_top
% 2.09/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_1236]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_2583,plain,
% 2.09/0.99      ( r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) != iProver_top ),
% 2.09/0.99      inference(global_propositional_subsumption,
% 2.09/0.99                [status(thm)],
% 2.09/0.99                [c_2532,c_17,c_1237]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_4574,plain,
% 2.09/0.99      ( r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_partfun1(sK1)),sK2) != iProver_top ),
% 2.09/0.99      inference(demodulation,[status(thm)],[c_4548,c_2583]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_10,plain,
% 2.09/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.09/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.09/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1078,plain,
% 2.09/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.09/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1560,plain,
% 2.09/0.99      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 2.09/0.99      inference(superposition,[status(thm)],[c_1072,c_1078]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_9,plain,
% 2.09/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.09/0.99      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 2.09/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1079,plain,
% 2.09/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.09/0.99      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1767,plain,
% 2.09/0.99      ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top
% 2.09/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 2.09/0.99      inference(superposition,[status(thm)],[c_1560,c_1079]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1849,plain,
% 2.09/0.99      ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top ),
% 2.09/0.99      inference(global_propositional_subsumption,
% 2.09/0.99                [status(thm)],
% 2.09/0.99                [c_1767,c_17]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1083,plain,
% 2.09/0.99      ( r1_tarski(X0,X1) = iProver_top
% 2.09/0.99      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1854,plain,
% 2.09/0.99      ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
% 2.09/0.99      inference(superposition,[status(thm)],[c_1849,c_1083]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_7,plain,
% 2.09/0.99      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 2.09/0.99      | ~ v1_relat_1(X0)
% 2.09/0.99      | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
% 2.09/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1080,plain,
% 2.09/0.99      ( k5_relat_1(X0,k6_partfun1(X1)) = X0
% 2.09/0.99      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 2.09/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.09/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1858,plain,
% 2.09/0.99      ( k5_relat_1(sK2,k6_partfun1(sK1)) = sK2
% 2.09/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.09/0.99      inference(superposition,[status(thm)],[c_1854,c_1080]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_1897,plain,
% 2.09/0.99      ( k5_relat_1(sK2,k6_partfun1(sK1)) = sK2 ),
% 2.09/0.99      inference(global_propositional_subsumption,
% 2.09/0.99                [status(thm)],
% 2.09/0.99                [c_1858,c_17,c_1193,c_1426,c_1551]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(c_4575,plain,
% 2.09/0.99      ( r2_relset_1(sK0,sK1,sK2,sK2) != iProver_top ),
% 2.09/0.99      inference(light_normalisation,[status(thm)],[c_4574,c_1897]) ).
% 2.09/0.99  
% 2.09/0.99  cnf(contradiction,plain,
% 2.09/0.99      ( $false ),
% 2.09/0.99      inference(minisat,[status(thm)],[c_4575,c_1237,c_17]) ).
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.09/0.99  
% 2.09/0.99  ------                               Statistics
% 2.09/0.99  
% 2.09/0.99  ------ General
% 2.09/0.99  
% 2.09/0.99  abstr_ref_over_cycles:                  0
% 2.09/0.99  abstr_ref_under_cycles:                 0
% 2.09/0.99  gc_basic_clause_elim:                   0
% 2.09/0.99  forced_gc_time:                         0
% 2.09/0.99  parsing_time:                           0.01
% 2.09/0.99  unif_index_cands_time:                  0.
% 2.09/0.99  unif_index_add_time:                    0.
% 2.09/0.99  orderings_time:                         0.
% 2.09/0.99  out_proof_time:                         0.008
% 2.09/0.99  total_time:                             0.169
% 2.09/0.99  num_of_symbols:                         47
% 2.09/0.99  num_of_terms:                           5388
% 2.09/0.99  
% 2.09/0.99  ------ Preprocessing
% 2.09/0.99  
% 2.09/0.99  num_of_splits:                          0
% 2.09/0.99  num_of_split_atoms:                     0
% 2.09/0.99  num_of_reused_defs:                     0
% 2.09/0.99  num_eq_ax_congr_red:                    20
% 2.09/0.99  num_of_sem_filtered_clauses:            1
% 2.09/0.99  num_of_subtypes:                        0
% 2.09/0.99  monotx_restored_types:                  0
% 2.09/0.99  sat_num_of_epr_types:                   0
% 2.09/0.99  sat_num_of_non_cyclic_types:            0
% 2.09/0.99  sat_guarded_non_collapsed_types:        0
% 2.09/0.99  num_pure_diseq_elim:                    0
% 2.09/0.99  simp_replaced_by:                       0
% 2.09/0.99  res_preprocessed:                       85
% 2.09/0.99  prep_upred:                             0
% 2.09/0.99  prep_unflattend:                        18
% 2.09/0.99  smt_new_axioms:                         0
% 2.09/0.99  pred_elim_cands:                        4
% 2.09/0.99  pred_elim:                              1
% 2.09/0.99  pred_elim_cl:                           2
% 2.09/0.99  pred_elim_cycles:                       3
% 2.09/0.99  merged_defs:                            8
% 2.09/0.99  merged_defs_ncl:                        0
% 2.09/0.99  bin_hyper_res:                          9
% 2.09/0.99  prep_cycles:                            4
% 2.09/0.99  pred_elim_time:                         0.004
% 2.09/0.99  splitting_time:                         0.
% 2.09/0.99  sem_filter_time:                        0.
% 2.09/0.99  monotx_time:                            0.001
% 2.09/0.99  subtype_inf_time:                       0.
% 2.09/0.99  
% 2.09/0.99  ------ Problem properties
% 2.09/0.99  
% 2.09/0.99  clauses:                                15
% 2.09/0.99  conjectures:                            2
% 2.09/0.99  epr:                                    1
% 2.09/0.99  horn:                                   15
% 2.09/0.99  ground:                                 2
% 2.09/0.99  unary:                                  3
% 2.09/0.99  binary:                                 6
% 2.09/0.99  lits:                                   34
% 2.09/0.99  lits_eq:                                5
% 2.09/0.99  fd_pure:                                0
% 2.09/0.99  fd_pseudo:                              0
% 2.09/0.99  fd_cond:                                0
% 2.09/0.99  fd_pseudo_cond:                         1
% 2.09/0.99  ac_symbols:                             0
% 2.09/0.99  
% 2.09/0.99  ------ Propositional Solver
% 2.09/0.99  
% 2.09/0.99  prop_solver_calls:                      30
% 2.09/0.99  prop_fast_solver_calls:                 617
% 2.09/0.99  smt_solver_calls:                       0
% 2.09/0.99  smt_fast_solver_calls:                  0
% 2.09/0.99  prop_num_of_clauses:                    1760
% 2.09/0.99  prop_preprocess_simplified:             4827
% 2.09/0.99  prop_fo_subsumed:                       7
% 2.09/0.99  prop_solver_time:                       0.
% 2.09/0.99  smt_solver_time:                        0.
% 2.09/0.99  smt_fast_solver_time:                   0.
% 2.09/0.99  prop_fast_solver_time:                  0.
% 2.09/0.99  prop_unsat_core_time:                   0.
% 2.09/0.99  
% 2.09/0.99  ------ QBF
% 2.09/0.99  
% 2.09/0.99  qbf_q_res:                              0
% 2.09/0.99  qbf_num_tautologies:                    0
% 2.09/0.99  qbf_prep_cycles:                        0
% 2.09/0.99  
% 2.09/0.99  ------ BMC1
% 2.09/0.99  
% 2.09/0.99  bmc1_current_bound:                     -1
% 2.09/0.99  bmc1_last_solved_bound:                 -1
% 2.09/0.99  bmc1_unsat_core_size:                   -1
% 2.09/0.99  bmc1_unsat_core_parents_size:           -1
% 2.09/0.99  bmc1_merge_next_fun:                    0
% 2.09/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.09/0.99  
% 2.09/0.99  ------ Instantiation
% 2.09/0.99  
% 2.09/0.99  inst_num_of_clauses:                    483
% 2.09/0.99  inst_num_in_passive:                    167
% 2.09/0.99  inst_num_in_active:                     294
% 2.09/0.99  inst_num_in_unprocessed:                22
% 2.09/0.99  inst_num_of_loops:                      310
% 2.09/0.99  inst_num_of_learning_restarts:          0
% 2.09/0.99  inst_num_moves_active_passive:          12
% 2.09/0.99  inst_lit_activity:                      0
% 2.09/0.99  inst_lit_activity_moves:                0
% 2.09/0.99  inst_num_tautologies:                   0
% 2.09/0.99  inst_num_prop_implied:                  0
% 2.09/0.99  inst_num_existing_simplified:           0
% 2.09/0.99  inst_num_eq_res_simplified:             0
% 2.09/0.99  inst_num_child_elim:                    0
% 2.09/0.99  inst_num_of_dismatching_blockings:      134
% 2.09/0.99  inst_num_of_non_proper_insts:           611
% 2.09/0.99  inst_num_of_duplicates:                 0
% 2.09/0.99  inst_inst_num_from_inst_to_res:         0
% 2.09/0.99  inst_dismatching_checking_time:         0.
% 2.09/0.99  
% 2.09/0.99  ------ Resolution
% 2.09/0.99  
% 2.09/0.99  res_num_of_clauses:                     0
% 2.09/0.99  res_num_in_passive:                     0
% 2.09/0.99  res_num_in_active:                      0
% 2.09/0.99  res_num_of_loops:                       89
% 2.09/0.99  res_forward_subset_subsumed:            41
% 2.09/0.99  res_backward_subset_subsumed:           2
% 2.09/0.99  res_forward_subsumed:                   0
% 2.09/0.99  res_backward_subsumed:                  0
% 2.09/0.99  res_forward_subsumption_resolution:     0
% 2.09/0.99  res_backward_subsumption_resolution:    0
% 2.09/0.99  res_clause_to_clause_subsumption:       231
% 2.09/0.99  res_orphan_elimination:                 0
% 2.09/0.99  res_tautology_del:                      80
% 2.09/0.99  res_num_eq_res_simplified:              0
% 2.09/0.99  res_num_sel_changes:                    0
% 2.09/0.99  res_moves_from_active_to_pass:          0
% 2.09/0.99  
% 2.09/0.99  ------ Superposition
% 2.09/0.99  
% 2.09/0.99  sup_time_total:                         0.
% 2.09/0.99  sup_time_generating:                    0.
% 2.09/0.99  sup_time_sim_full:                      0.
% 2.09/0.99  sup_time_sim_immed:                     0.
% 2.09/0.99  
% 2.09/0.99  sup_num_of_clauses:                     98
% 2.09/0.99  sup_num_in_active:                      59
% 2.09/0.99  sup_num_in_passive:                     39
% 2.09/0.99  sup_num_of_loops:                       61
% 2.09/0.99  sup_fw_superposition:                   76
% 2.09/0.99  sup_bw_superposition:                   34
% 2.09/0.99  sup_immediate_simplified:               19
% 2.09/0.99  sup_given_eliminated:                   0
% 2.09/0.99  comparisons_done:                       0
% 2.09/0.99  comparisons_avoided:                    0
% 2.09/0.99  
% 2.09/0.99  ------ Simplifications
% 2.09/0.99  
% 2.09/0.99  
% 2.09/0.99  sim_fw_subset_subsumed:                 3
% 2.09/0.99  sim_bw_subset_subsumed:                 1
% 2.09/0.99  sim_fw_subsumed:                        1
% 2.09/0.99  sim_bw_subsumed:                        0
% 2.09/0.99  sim_fw_subsumption_res:                 2
% 2.09/0.99  sim_bw_subsumption_res:                 0
% 2.09/0.99  sim_tautology_del:                      1
% 2.09/0.99  sim_eq_tautology_del:                   3
% 2.09/0.99  sim_eq_res_simp:                        0
% 2.09/0.99  sim_fw_demodulated:                     10
% 2.09/0.99  sim_bw_demodulated:                     3
% 2.09/0.99  sim_light_normalised:                   5
% 2.09/0.99  sim_joinable_taut:                      0
% 2.09/0.99  sim_joinable_simp:                      0
% 2.09/0.99  sim_ac_normalised:                      0
% 2.09/0.99  sim_smt_subsumption:                    0
% 2.09/0.99  
%------------------------------------------------------------------------------
