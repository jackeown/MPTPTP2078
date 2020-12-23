%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:24 EST 2020

% Result     : Theorem 0.51s
% Output     : CNFRefutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 198 expanded)
%              Number of clauses        :   65 (  89 expanded)
%              Number of leaves         :   14 (  37 expanded)
%              Depth                    :   15
%              Number of atoms          :  280 ( 494 expanded)
%              Number of equality atoms :   70 (  94 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
          & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        | ~ r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
          | ~ r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
        | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
      | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f28])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f21])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f44,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
    | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_partfun1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f34,f42])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_partfun1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f35,f42])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_523,plain,
    ( ~ r2_relset_1(X0_47,X1_47,X0_44,X1_44)
    | r2_relset_1(X0_47,X1_47,X2_44,X3_44)
    | X2_44 != X0_44
    | X3_44 != X1_44 ),
    theory(equality)).

cnf(c_892,plain,
    ( r2_relset_1(sK0,sK1,X0_44,X1_44)
    | ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | X0_44 != sK2
    | X1_44 != sK2 ),
    inference(instantiation,[status(thm)],[c_523])).

cnf(c_1422,plain,
    ( r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_partfun1(sK1)),X0_44)
    | ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | X0_44 != sK2
    | k5_relat_1(sK2,k6_partfun1(sK1)) != sK2 ),
    inference(instantiation,[status(thm)],[c_892])).

cnf(c_1424,plain,
    ( r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_partfun1(sK1)),sK2)
    | ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | k5_relat_1(sK2,k6_partfun1(sK1)) != sK2
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1422])).

cnf(c_11,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_509,plain,
    ( m1_subset_1(k6_partfun1(X0_47),k1_zfmisc_1(k2_zfmisc_1(X0_47,X0_47))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_738,plain,
    ( m1_subset_1(k6_partfun1(X0_47),k1_zfmisc_1(k2_zfmisc_1(X0_47,X0_47))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_509])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_507,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_740,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_507])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_511,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47)))
    | k4_relset_1(X2_47,X3_47,X0_47,X1_47,X1_44,X0_44) = k5_relat_1(X1_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_736,plain,
    ( k4_relset_1(X0_47,X1_47,X2_47,X3_47,X0_44,X1_44) = k5_relat_1(X0_44,X1_44)
    | m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | m1_subset_1(X1_44,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_511])).

cnf(c_1094,plain,
    ( k4_relset_1(X0_47,X1_47,sK0,sK1,X0_44,sK2) = k5_relat_1(X0_44,sK2)
    | m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
    inference(superposition,[status(thm)],[c_740,c_736])).

cnf(c_1276,plain,
    ( k4_relset_1(X0_47,X0_47,sK0,sK1,k6_partfun1(X0_47),sK2) = k5_relat_1(k6_partfun1(X0_47),sK2) ),
    inference(superposition,[status(thm)],[c_738,c_1094])).

cnf(c_12,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
    | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_508,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
    | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_739,plain,
    ( r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) != iProver_top
    | r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_508])).

cnf(c_1404,plain,
    ( r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) != iProver_top
    | r2_relset_1(sK0,sK1,k5_relat_1(k6_partfun1(sK0),sK2),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1276,c_739])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_165,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_8,c_1])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_169,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_165,c_6])).

cnf(c_170,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_169])).

cnf(c_506,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | r1_tarski(k1_relat_1(X0_44),X0_47) ),
    inference(subtyping,[status(esa)],[c_170])).

cnf(c_741,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | r1_tarski(k1_relat_1(X0_44),X0_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_506])).

cnf(c_1006,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_740,c_741])).

cnf(c_4,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_514,plain,
    ( ~ r1_tarski(k1_relat_1(X0_44),X0_47)
    | ~ v1_relat_1(X0_44)
    | k5_relat_1(k6_partfun1(X0_47),X0_44) = X0_44 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_733,plain,
    ( k5_relat_1(k6_partfun1(X0_47),X0_44) = X0_44
    | r1_tarski(k1_relat_1(X0_44),X0_47) != iProver_top
    | v1_relat_1(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_514])).

cnf(c_1042,plain,
    ( k5_relat_1(k6_partfun1(sK0),sK2) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1006,c_733])).

cnf(c_533,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k6_partfun1(sK0),sK2) = sK2 ),
    inference(instantiation,[status(thm)],[c_514])).

cnf(c_512,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | v1_relat_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_810,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_512])).

cnf(c_826,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(instantiation,[status(thm)],[c_506])).

cnf(c_1400,plain,
    ( k5_relat_1(k6_partfun1(sK0),sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1042,c_13,c_533,c_810,c_826])).

cnf(c_1405,plain,
    ( r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) != iProver_top
    | r2_relset_1(sK0,sK1,sK2,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1404,c_1400])).

cnf(c_1406,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
    | ~ r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1405])).

cnf(c_1185,plain,
    ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_509])).

cnf(c_862,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | ~ m1_subset_1(k6_partfun1(X2_47),k1_zfmisc_1(k2_zfmisc_1(X2_47,X2_47)))
    | k4_relset_1(X0_47,X1_47,X2_47,X2_47,X0_44,k6_partfun1(X2_47)) = k5_relat_1(X0_44,k6_partfun1(X2_47)) ),
    inference(instantiation,[status(thm)],[c_511])).

cnf(c_1023,plain,
    ( ~ m1_subset_1(k6_partfun1(X0_47),k1_zfmisc_1(k2_zfmisc_1(X0_47,X0_47)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k4_relset_1(sK0,sK1,X0_47,X0_47,sK2,k6_partfun1(X0_47)) = k5_relat_1(sK2,k6_partfun1(X0_47)) ),
    inference(instantiation,[status(thm)],[c_862])).

cnf(c_1172,plain,
    ( ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)) = k5_relat_1(sK2,k6_partfun1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1023])).

cnf(c_954,plain,
    ( ~ r2_relset_1(sK0,sK1,X0_44,X1_44)
    | r2_relset_1(sK0,sK1,X2_44,X3_44)
    | X2_44 != X0_44
    | X3_44 != X1_44 ),
    inference(instantiation,[status(thm)],[c_523])).

cnf(c_1067,plain,
    ( ~ r2_relset_1(sK0,sK1,X0_44,X1_44)
    | r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
    | k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)) != X0_44
    | sK2 != X1_44 ),
    inference(instantiation,[status(thm)],[c_954])).

cnf(c_1171,plain,
    ( r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
    | ~ r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_partfun1(sK1)),X0_44)
    | k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)) != k5_relat_1(sK2,k6_partfun1(sK1))
    | sK2 != X0_44 ),
    inference(instantiation,[status(thm)],[c_1067])).

cnf(c_1174,plain,
    ( r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
    | ~ r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_partfun1(sK1)),sK2)
    | k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)) != k5_relat_1(sK2,k6_partfun1(sK1))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1171])).

cnf(c_5,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_513,plain,
    ( ~ r1_tarski(k2_relat_1(X0_44),X0_47)
    | ~ v1_relat_1(X0_44)
    | k5_relat_1(X0_44,k6_partfun1(X0_47)) = X0_44 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_934,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k6_partfun1(sK1)) = sK2 ),
    inference(instantiation,[status(thm)],[c_513])).

cnf(c_10,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_510,plain,
    ( r2_relset_1(X0_47,X1_47,X0_44,X0_44)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_842,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_510])).

cnf(c_844,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_842])).

cnf(c_3,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_187,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_7])).

cnf(c_188,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_187])).

cnf(c_192,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_188,c_6])).

cnf(c_193,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_192])).

cnf(c_505,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | r1_tarski(k2_relat_1(X0_44),X1_47) ),
    inference(subtyping,[status(esa)],[c_193])).

cnf(c_818,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_505])).

cnf(c_516,plain,
    ( X0_44 = X0_44 ),
    theory(equality)).

cnf(c_530,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_516])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1424,c_1406,c_1185,c_1172,c_1174,c_934,c_844,c_818,c_810,c_530,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:56:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.51/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.51/1.03  
% 0.51/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.51/1.03  
% 0.51/1.03  ------  iProver source info
% 0.51/1.03  
% 0.51/1.03  git: date: 2020-06-30 10:37:57 +0100
% 0.51/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.51/1.03  git: non_committed_changes: false
% 0.51/1.03  git: last_make_outside_of_git: false
% 0.51/1.03  
% 0.51/1.03  ------ 
% 0.51/1.03  
% 0.51/1.03  ------ Input Options
% 0.51/1.03  
% 0.51/1.03  --out_options                           all
% 0.51/1.03  --tptp_safe_out                         true
% 0.51/1.03  --problem_path                          ""
% 0.51/1.03  --include_path                          ""
% 0.51/1.03  --clausifier                            res/vclausify_rel
% 0.51/1.03  --clausifier_options                    --mode clausify
% 0.51/1.03  --stdin                                 false
% 0.51/1.03  --stats_out                             all
% 0.51/1.03  
% 0.51/1.03  ------ General Options
% 0.51/1.03  
% 0.51/1.03  --fof                                   false
% 0.51/1.03  --time_out_real                         305.
% 0.51/1.03  --time_out_virtual                      -1.
% 0.51/1.03  --symbol_type_check                     false
% 0.51/1.03  --clausify_out                          false
% 0.51/1.03  --sig_cnt_out                           false
% 0.51/1.03  --trig_cnt_out                          false
% 0.51/1.03  --trig_cnt_out_tolerance                1.
% 0.51/1.03  --trig_cnt_out_sk_spl                   false
% 0.51/1.03  --abstr_cl_out                          false
% 0.51/1.03  
% 0.51/1.03  ------ Global Options
% 0.51/1.03  
% 0.51/1.03  --schedule                              default
% 0.51/1.03  --add_important_lit                     false
% 0.51/1.03  --prop_solver_per_cl                    1000
% 0.51/1.03  --min_unsat_core                        false
% 0.51/1.03  --soft_assumptions                      false
% 0.51/1.03  --soft_lemma_size                       3
% 0.51/1.03  --prop_impl_unit_size                   0
% 0.51/1.03  --prop_impl_unit                        []
% 0.51/1.03  --share_sel_clauses                     true
% 0.51/1.03  --reset_solvers                         false
% 0.51/1.03  --bc_imp_inh                            [conj_cone]
% 0.51/1.03  --conj_cone_tolerance                   3.
% 0.51/1.03  --extra_neg_conj                        none
% 0.51/1.03  --large_theory_mode                     true
% 0.51/1.03  --prolific_symb_bound                   200
% 0.51/1.03  --lt_threshold                          2000
% 0.51/1.03  --clause_weak_htbl                      true
% 0.51/1.03  --gc_record_bc_elim                     false
% 0.51/1.03  
% 0.51/1.03  ------ Preprocessing Options
% 0.51/1.03  
% 0.51/1.03  --preprocessing_flag                    true
% 0.51/1.03  --time_out_prep_mult                    0.1
% 0.51/1.03  --splitting_mode                        input
% 0.51/1.03  --splitting_grd                         true
% 0.51/1.03  --splitting_cvd                         false
% 0.51/1.03  --splitting_cvd_svl                     false
% 0.51/1.03  --splitting_nvd                         32
% 0.51/1.03  --sub_typing                            true
% 0.51/1.03  --prep_gs_sim                           true
% 0.51/1.03  --prep_unflatten                        true
% 0.51/1.03  --prep_res_sim                          true
% 0.51/1.03  --prep_upred                            true
% 0.51/1.03  --prep_sem_filter                       exhaustive
% 0.51/1.03  --prep_sem_filter_out                   false
% 0.51/1.03  --pred_elim                             true
% 0.51/1.03  --res_sim_input                         true
% 0.51/1.03  --eq_ax_congr_red                       true
% 0.51/1.03  --pure_diseq_elim                       true
% 0.51/1.03  --brand_transform                       false
% 0.51/1.03  --non_eq_to_eq                          false
% 0.51/1.03  --prep_def_merge                        true
% 0.51/1.03  --prep_def_merge_prop_impl              false
% 0.51/1.03  --prep_def_merge_mbd                    true
% 0.51/1.03  --prep_def_merge_tr_red                 false
% 0.51/1.03  --prep_def_merge_tr_cl                  false
% 0.51/1.03  --smt_preprocessing                     true
% 0.51/1.03  --smt_ac_axioms                         fast
% 0.51/1.03  --preprocessed_out                      false
% 0.51/1.03  --preprocessed_stats                    false
% 0.51/1.03  
% 0.51/1.03  ------ Abstraction refinement Options
% 0.51/1.03  
% 0.51/1.03  --abstr_ref                             []
% 0.51/1.03  --abstr_ref_prep                        false
% 0.51/1.03  --abstr_ref_until_sat                   false
% 0.51/1.03  --abstr_ref_sig_restrict                funpre
% 0.51/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 0.51/1.03  --abstr_ref_under                       []
% 0.51/1.03  
% 0.51/1.03  ------ SAT Options
% 0.51/1.03  
% 0.51/1.03  --sat_mode                              false
% 0.51/1.03  --sat_fm_restart_options                ""
% 0.51/1.03  --sat_gr_def                            false
% 0.51/1.03  --sat_epr_types                         true
% 0.51/1.03  --sat_non_cyclic_types                  false
% 0.51/1.03  --sat_finite_models                     false
% 0.51/1.03  --sat_fm_lemmas                         false
% 0.51/1.03  --sat_fm_prep                           false
% 0.51/1.03  --sat_fm_uc_incr                        true
% 0.51/1.03  --sat_out_model                         small
% 0.51/1.03  --sat_out_clauses                       false
% 0.51/1.03  
% 0.51/1.03  ------ QBF Options
% 0.51/1.03  
% 0.51/1.03  --qbf_mode                              false
% 0.51/1.03  --qbf_elim_univ                         false
% 0.51/1.03  --qbf_dom_inst                          none
% 0.51/1.03  --qbf_dom_pre_inst                      false
% 0.51/1.03  --qbf_sk_in                             false
% 0.51/1.03  --qbf_pred_elim                         true
% 0.51/1.03  --qbf_split                             512
% 0.51/1.03  
% 0.51/1.03  ------ BMC1 Options
% 0.51/1.03  
% 0.51/1.03  --bmc1_incremental                      false
% 0.51/1.03  --bmc1_axioms                           reachable_all
% 0.51/1.03  --bmc1_min_bound                        0
% 0.51/1.03  --bmc1_max_bound                        -1
% 0.51/1.03  --bmc1_max_bound_default                -1
% 0.51/1.03  --bmc1_symbol_reachability              true
% 0.51/1.03  --bmc1_property_lemmas                  false
% 0.51/1.03  --bmc1_k_induction                      false
% 0.51/1.03  --bmc1_non_equiv_states                 false
% 0.51/1.03  --bmc1_deadlock                         false
% 0.51/1.03  --bmc1_ucm                              false
% 0.51/1.03  --bmc1_add_unsat_core                   none
% 0.51/1.03  --bmc1_unsat_core_children              false
% 0.51/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 0.51/1.03  --bmc1_out_stat                         full
% 0.51/1.03  --bmc1_ground_init                      false
% 0.51/1.03  --bmc1_pre_inst_next_state              false
% 0.51/1.03  --bmc1_pre_inst_state                   false
% 0.51/1.03  --bmc1_pre_inst_reach_state             false
% 0.51/1.03  --bmc1_out_unsat_core                   false
% 0.51/1.03  --bmc1_aig_witness_out                  false
% 0.51/1.03  --bmc1_verbose                          false
% 0.51/1.03  --bmc1_dump_clauses_tptp                false
% 0.51/1.03  --bmc1_dump_unsat_core_tptp             false
% 0.51/1.03  --bmc1_dump_file                        -
% 0.51/1.03  --bmc1_ucm_expand_uc_limit              128
% 0.51/1.03  --bmc1_ucm_n_expand_iterations          6
% 0.51/1.03  --bmc1_ucm_extend_mode                  1
% 0.51/1.03  --bmc1_ucm_init_mode                    2
% 0.51/1.03  --bmc1_ucm_cone_mode                    none
% 0.51/1.03  --bmc1_ucm_reduced_relation_type        0
% 0.51/1.03  --bmc1_ucm_relax_model                  4
% 0.51/1.03  --bmc1_ucm_full_tr_after_sat            true
% 0.51/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 0.51/1.03  --bmc1_ucm_layered_model                none
% 0.51/1.03  --bmc1_ucm_max_lemma_size               10
% 0.51/1.03  
% 0.51/1.03  ------ AIG Options
% 0.51/1.03  
% 0.51/1.03  --aig_mode                              false
% 0.51/1.03  
% 0.51/1.03  ------ Instantiation Options
% 0.51/1.03  
% 0.51/1.03  --instantiation_flag                    true
% 0.51/1.03  --inst_sos_flag                         false
% 0.51/1.03  --inst_sos_phase                        true
% 0.51/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.51/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.51/1.03  --inst_lit_sel_side                     num_symb
% 0.51/1.03  --inst_solver_per_active                1400
% 0.51/1.03  --inst_solver_calls_frac                1.
% 0.51/1.03  --inst_passive_queue_type               priority_queues
% 0.51/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.51/1.03  --inst_passive_queues_freq              [25;2]
% 0.51/1.03  --inst_dismatching                      true
% 0.51/1.03  --inst_eager_unprocessed_to_passive     true
% 0.51/1.03  --inst_prop_sim_given                   true
% 0.51/1.03  --inst_prop_sim_new                     false
% 0.51/1.03  --inst_subs_new                         false
% 0.51/1.03  --inst_eq_res_simp                      false
% 0.51/1.03  --inst_subs_given                       false
% 0.51/1.03  --inst_orphan_elimination               true
% 0.51/1.03  --inst_learning_loop_flag               true
% 0.51/1.03  --inst_learning_start                   3000
% 0.51/1.03  --inst_learning_factor                  2
% 0.51/1.03  --inst_start_prop_sim_after_learn       3
% 0.51/1.03  --inst_sel_renew                        solver
% 0.51/1.03  --inst_lit_activity_flag                true
% 0.51/1.03  --inst_restr_to_given                   false
% 0.51/1.03  --inst_activity_threshold               500
% 0.51/1.03  --inst_out_proof                        true
% 0.51/1.03  
% 0.51/1.03  ------ Resolution Options
% 0.51/1.03  
% 0.51/1.03  --resolution_flag                       true
% 0.51/1.03  --res_lit_sel                           adaptive
% 0.51/1.03  --res_lit_sel_side                      none
% 0.51/1.03  --res_ordering                          kbo
% 0.51/1.03  --res_to_prop_solver                    active
% 0.51/1.03  --res_prop_simpl_new                    false
% 0.51/1.03  --res_prop_simpl_given                  true
% 0.51/1.03  --res_passive_queue_type                priority_queues
% 0.51/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.51/1.03  --res_passive_queues_freq               [15;5]
% 0.51/1.03  --res_forward_subs                      full
% 0.51/1.03  --res_backward_subs                     full
% 0.51/1.03  --res_forward_subs_resolution           true
% 0.51/1.03  --res_backward_subs_resolution          true
% 0.51/1.03  --res_orphan_elimination                true
% 0.51/1.03  --res_time_limit                        2.
% 0.51/1.03  --res_out_proof                         true
% 0.51/1.03  
% 0.51/1.03  ------ Superposition Options
% 0.51/1.03  
% 0.51/1.03  --superposition_flag                    true
% 0.51/1.03  --sup_passive_queue_type                priority_queues
% 0.51/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.51/1.03  --sup_passive_queues_freq               [8;1;4]
% 0.51/1.03  --demod_completeness_check              fast
% 0.51/1.03  --demod_use_ground                      true
% 0.51/1.03  --sup_to_prop_solver                    passive
% 0.51/1.03  --sup_prop_simpl_new                    true
% 0.51/1.03  --sup_prop_simpl_given                  true
% 0.51/1.03  --sup_fun_splitting                     false
% 0.51/1.03  --sup_smt_interval                      50000
% 0.51/1.03  
% 0.51/1.03  ------ Superposition Simplification Setup
% 0.51/1.03  
% 0.51/1.03  --sup_indices_passive                   []
% 0.51/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.51/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.51/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.51/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 0.51/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.51/1.03  --sup_full_bw                           [BwDemod]
% 0.51/1.03  --sup_immed_triv                        [TrivRules]
% 0.51/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.51/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.51/1.03  --sup_immed_bw_main                     []
% 0.51/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.51/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 0.51/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.51/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.51/1.03  
% 0.51/1.03  ------ Combination Options
% 0.51/1.03  
% 0.51/1.03  --comb_res_mult                         3
% 0.51/1.03  --comb_sup_mult                         2
% 0.51/1.03  --comb_inst_mult                        10
% 0.51/1.03  
% 0.51/1.03  ------ Debug Options
% 0.51/1.03  
% 0.51/1.03  --dbg_backtrace                         false
% 0.51/1.03  --dbg_dump_prop_clauses                 false
% 0.51/1.03  --dbg_dump_prop_clauses_file            -
% 0.51/1.03  --dbg_out_stat                          false
% 0.51/1.03  ------ Parsing...
% 0.51/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.51/1.03  
% 0.51/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 0.51/1.03  
% 0.51/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.51/1.03  
% 0.51/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.51/1.03  ------ Proving...
% 0.51/1.03  ------ Problem Properties 
% 0.51/1.03  
% 0.51/1.03  
% 0.51/1.03  clauses                                 10
% 0.51/1.03  conjectures                             2
% 0.51/1.03  EPR                                     0
% 0.51/1.03  Horn                                    10
% 0.51/1.03  unary                                   2
% 0.51/1.03  binary                                  4
% 0.51/1.03  lits                                    22
% 0.51/1.03  lits eq                                 3
% 0.51/1.03  fd_pure                                 0
% 0.51/1.03  fd_pseudo                               0
% 0.51/1.03  fd_cond                                 0
% 0.51/1.03  fd_pseudo_cond                          0
% 0.51/1.03  AC symbols                              0
% 0.51/1.03  
% 0.51/1.03  ------ Schedule dynamic 5 is on 
% 0.51/1.03  
% 0.51/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.51/1.03  
% 0.51/1.03  
% 0.51/1.03  ------ 
% 0.51/1.03  Current options:
% 0.51/1.03  ------ 
% 0.51/1.03  
% 0.51/1.03  ------ Input Options
% 0.51/1.03  
% 0.51/1.03  --out_options                           all
% 0.51/1.03  --tptp_safe_out                         true
% 0.51/1.03  --problem_path                          ""
% 0.51/1.03  --include_path                          ""
% 0.51/1.03  --clausifier                            res/vclausify_rel
% 0.51/1.03  --clausifier_options                    --mode clausify
% 0.51/1.03  --stdin                                 false
% 0.51/1.03  --stats_out                             all
% 0.51/1.03  
% 0.51/1.03  ------ General Options
% 0.51/1.03  
% 0.51/1.03  --fof                                   false
% 0.51/1.03  --time_out_real                         305.
% 0.51/1.03  --time_out_virtual                      -1.
% 0.51/1.03  --symbol_type_check                     false
% 0.51/1.03  --clausify_out                          false
% 0.51/1.03  --sig_cnt_out                           false
% 0.51/1.03  --trig_cnt_out                          false
% 0.51/1.03  --trig_cnt_out_tolerance                1.
% 0.51/1.03  --trig_cnt_out_sk_spl                   false
% 0.51/1.03  --abstr_cl_out                          false
% 0.51/1.03  
% 0.51/1.03  ------ Global Options
% 0.51/1.03  
% 0.51/1.03  --schedule                              default
% 0.51/1.03  --add_important_lit                     false
% 0.51/1.03  --prop_solver_per_cl                    1000
% 0.51/1.03  --min_unsat_core                        false
% 0.51/1.03  --soft_assumptions                      false
% 0.51/1.03  --soft_lemma_size                       3
% 0.51/1.03  --prop_impl_unit_size                   0
% 0.51/1.03  --prop_impl_unit                        []
% 0.51/1.03  --share_sel_clauses                     true
% 0.51/1.03  --reset_solvers                         false
% 0.51/1.03  --bc_imp_inh                            [conj_cone]
% 0.51/1.03  --conj_cone_tolerance                   3.
% 0.51/1.03  --extra_neg_conj                        none
% 0.51/1.03  --large_theory_mode                     true
% 0.51/1.03  --prolific_symb_bound                   200
% 0.51/1.03  --lt_threshold                          2000
% 0.51/1.03  --clause_weak_htbl                      true
% 0.51/1.03  --gc_record_bc_elim                     false
% 0.51/1.03  
% 0.51/1.03  ------ Preprocessing Options
% 0.51/1.03  
% 0.51/1.03  --preprocessing_flag                    true
% 0.51/1.03  --time_out_prep_mult                    0.1
% 0.51/1.03  --splitting_mode                        input
% 0.51/1.03  --splitting_grd                         true
% 0.51/1.03  --splitting_cvd                         false
% 0.51/1.03  --splitting_cvd_svl                     false
% 0.51/1.03  --splitting_nvd                         32
% 0.51/1.03  --sub_typing                            true
% 0.51/1.03  --prep_gs_sim                           true
% 0.51/1.03  --prep_unflatten                        true
% 0.51/1.03  --prep_res_sim                          true
% 0.51/1.03  --prep_upred                            true
% 0.51/1.03  --prep_sem_filter                       exhaustive
% 0.51/1.03  --prep_sem_filter_out                   false
% 0.51/1.03  --pred_elim                             true
% 0.51/1.03  --res_sim_input                         true
% 0.51/1.03  --eq_ax_congr_red                       true
% 0.51/1.03  --pure_diseq_elim                       true
% 0.51/1.03  --brand_transform                       false
% 0.51/1.03  --non_eq_to_eq                          false
% 0.51/1.03  --prep_def_merge                        true
% 0.51/1.03  --prep_def_merge_prop_impl              false
% 0.51/1.03  --prep_def_merge_mbd                    true
% 0.51/1.03  --prep_def_merge_tr_red                 false
% 0.51/1.03  --prep_def_merge_tr_cl                  false
% 0.51/1.03  --smt_preprocessing                     true
% 0.51/1.03  --smt_ac_axioms                         fast
% 0.51/1.03  --preprocessed_out                      false
% 0.51/1.03  --preprocessed_stats                    false
% 0.51/1.03  
% 0.51/1.03  ------ Abstraction refinement Options
% 0.51/1.03  
% 0.51/1.03  --abstr_ref                             []
% 0.51/1.03  --abstr_ref_prep                        false
% 0.51/1.03  --abstr_ref_until_sat                   false
% 0.51/1.03  --abstr_ref_sig_restrict                funpre
% 0.51/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 0.51/1.03  --abstr_ref_under                       []
% 0.51/1.03  
% 0.51/1.03  ------ SAT Options
% 0.51/1.03  
% 0.51/1.03  --sat_mode                              false
% 0.51/1.03  --sat_fm_restart_options                ""
% 0.51/1.03  --sat_gr_def                            false
% 0.51/1.03  --sat_epr_types                         true
% 0.51/1.03  --sat_non_cyclic_types                  false
% 0.51/1.03  --sat_finite_models                     false
% 0.51/1.03  --sat_fm_lemmas                         false
% 0.51/1.03  --sat_fm_prep                           false
% 0.51/1.03  --sat_fm_uc_incr                        true
% 0.51/1.03  --sat_out_model                         small
% 0.51/1.03  --sat_out_clauses                       false
% 0.51/1.03  
% 0.51/1.03  ------ QBF Options
% 0.51/1.03  
% 0.51/1.03  --qbf_mode                              false
% 0.51/1.03  --qbf_elim_univ                         false
% 0.51/1.03  --qbf_dom_inst                          none
% 0.51/1.03  --qbf_dom_pre_inst                      false
% 0.51/1.03  --qbf_sk_in                             false
% 0.51/1.03  --qbf_pred_elim                         true
% 0.51/1.03  --qbf_split                             512
% 0.51/1.03  
% 0.51/1.03  ------ BMC1 Options
% 0.51/1.03  
% 0.51/1.03  --bmc1_incremental                      false
% 0.51/1.03  --bmc1_axioms                           reachable_all
% 0.51/1.03  --bmc1_min_bound                        0
% 0.51/1.03  --bmc1_max_bound                        -1
% 0.51/1.03  --bmc1_max_bound_default                -1
% 0.51/1.03  --bmc1_symbol_reachability              true
% 0.51/1.03  --bmc1_property_lemmas                  false
% 0.51/1.03  --bmc1_k_induction                      false
% 0.51/1.03  --bmc1_non_equiv_states                 false
% 0.51/1.03  --bmc1_deadlock                         false
% 0.51/1.03  --bmc1_ucm                              false
% 0.51/1.03  --bmc1_add_unsat_core                   none
% 0.51/1.03  --bmc1_unsat_core_children              false
% 0.51/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 0.51/1.03  --bmc1_out_stat                         full
% 0.51/1.03  --bmc1_ground_init                      false
% 0.51/1.03  --bmc1_pre_inst_next_state              false
% 0.51/1.03  --bmc1_pre_inst_state                   false
% 0.51/1.03  --bmc1_pre_inst_reach_state             false
% 0.51/1.03  --bmc1_out_unsat_core                   false
% 0.51/1.03  --bmc1_aig_witness_out                  false
% 0.51/1.03  --bmc1_verbose                          false
% 0.51/1.03  --bmc1_dump_clauses_tptp                false
% 0.51/1.03  --bmc1_dump_unsat_core_tptp             false
% 0.51/1.03  --bmc1_dump_file                        -
% 0.51/1.03  --bmc1_ucm_expand_uc_limit              128
% 0.51/1.03  --bmc1_ucm_n_expand_iterations          6
% 0.51/1.03  --bmc1_ucm_extend_mode                  1
% 0.51/1.03  --bmc1_ucm_init_mode                    2
% 0.51/1.03  --bmc1_ucm_cone_mode                    none
% 0.51/1.03  --bmc1_ucm_reduced_relation_type        0
% 0.51/1.03  --bmc1_ucm_relax_model                  4
% 0.51/1.03  --bmc1_ucm_full_tr_after_sat            true
% 0.51/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 0.51/1.03  --bmc1_ucm_layered_model                none
% 0.51/1.03  --bmc1_ucm_max_lemma_size               10
% 0.51/1.03  
% 0.51/1.03  ------ AIG Options
% 0.51/1.03  
% 0.51/1.03  --aig_mode                              false
% 0.51/1.03  
% 0.51/1.03  ------ Instantiation Options
% 0.51/1.03  
% 0.51/1.03  --instantiation_flag                    true
% 0.51/1.03  --inst_sos_flag                         false
% 0.51/1.03  --inst_sos_phase                        true
% 0.51/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.51/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.51/1.03  --inst_lit_sel_side                     none
% 0.51/1.03  --inst_solver_per_active                1400
% 0.51/1.03  --inst_solver_calls_frac                1.
% 0.51/1.03  --inst_passive_queue_type               priority_queues
% 0.51/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.51/1.03  --inst_passive_queues_freq              [25;2]
% 0.51/1.03  --inst_dismatching                      true
% 0.51/1.03  --inst_eager_unprocessed_to_passive     true
% 0.51/1.03  --inst_prop_sim_given                   true
% 0.51/1.03  --inst_prop_sim_new                     false
% 0.51/1.03  --inst_subs_new                         false
% 0.51/1.03  --inst_eq_res_simp                      false
% 0.51/1.03  --inst_subs_given                       false
% 0.51/1.03  --inst_orphan_elimination               true
% 0.51/1.03  --inst_learning_loop_flag               true
% 0.51/1.03  --inst_learning_start                   3000
% 0.51/1.03  --inst_learning_factor                  2
% 0.51/1.03  --inst_start_prop_sim_after_learn       3
% 0.51/1.03  --inst_sel_renew                        solver
% 0.51/1.03  --inst_lit_activity_flag                true
% 0.51/1.03  --inst_restr_to_given                   false
% 0.51/1.03  --inst_activity_threshold               500
% 0.51/1.03  --inst_out_proof                        true
% 0.51/1.03  
% 0.51/1.03  ------ Resolution Options
% 0.51/1.03  
% 0.51/1.03  --resolution_flag                       false
% 0.51/1.03  --res_lit_sel                           adaptive
% 0.51/1.03  --res_lit_sel_side                      none
% 0.51/1.03  --res_ordering                          kbo
% 0.51/1.03  --res_to_prop_solver                    active
% 0.51/1.03  --res_prop_simpl_new                    false
% 0.51/1.03  --res_prop_simpl_given                  true
% 0.51/1.03  --res_passive_queue_type                priority_queues
% 0.51/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.51/1.03  --res_passive_queues_freq               [15;5]
% 0.51/1.03  --res_forward_subs                      full
% 0.51/1.03  --res_backward_subs                     full
% 0.51/1.03  --res_forward_subs_resolution           true
% 0.51/1.03  --res_backward_subs_resolution          true
% 0.51/1.03  --res_orphan_elimination                true
% 0.51/1.03  --res_time_limit                        2.
% 0.51/1.03  --res_out_proof                         true
% 0.51/1.03  
% 0.51/1.03  ------ Superposition Options
% 0.51/1.03  
% 0.51/1.03  --superposition_flag                    true
% 0.51/1.03  --sup_passive_queue_type                priority_queues
% 0.51/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.51/1.03  --sup_passive_queues_freq               [8;1;4]
% 0.51/1.03  --demod_completeness_check              fast
% 0.51/1.03  --demod_use_ground                      true
% 0.51/1.03  --sup_to_prop_solver                    passive
% 0.51/1.03  --sup_prop_simpl_new                    true
% 0.51/1.03  --sup_prop_simpl_given                  true
% 0.51/1.03  --sup_fun_splitting                     false
% 0.51/1.03  --sup_smt_interval                      50000
% 0.51/1.03  
% 0.51/1.03  ------ Superposition Simplification Setup
% 0.51/1.03  
% 0.51/1.03  --sup_indices_passive                   []
% 0.51/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.51/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.51/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.51/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 0.51/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.51/1.03  --sup_full_bw                           [BwDemod]
% 0.51/1.03  --sup_immed_triv                        [TrivRules]
% 0.51/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.51/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.51/1.03  --sup_immed_bw_main                     []
% 0.51/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.51/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 0.51/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.51/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.51/1.03  
% 0.51/1.03  ------ Combination Options
% 0.51/1.03  
% 0.51/1.03  --comb_res_mult                         3
% 0.51/1.03  --comb_sup_mult                         2
% 0.51/1.03  --comb_inst_mult                        10
% 0.51/1.03  
% 0.51/1.03  ------ Debug Options
% 0.51/1.03  
% 0.51/1.03  --dbg_backtrace                         false
% 0.51/1.03  --dbg_dump_prop_clauses                 false
% 0.51/1.03  --dbg_dump_prop_clauses_file            -
% 0.51/1.03  --dbg_out_stat                          false
% 0.51/1.03  
% 0.51/1.03  
% 0.51/1.03  
% 0.51/1.03  
% 0.51/1.03  ------ Proving...
% 0.51/1.03  
% 0.51/1.03  
% 0.51/1.03  % SZS status Theorem for theBenchmark.p
% 0.51/1.03  
% 0.51/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 0.51/1.03  
% 0.51/1.03  fof(f9,axiom,(
% 0.51/1.03    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.51/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.51/1.03  
% 0.51/1.03  fof(f41,plain,(
% 0.51/1.03    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.51/1.03    inference(cnf_transformation,[],[f9])).
% 0.51/1.03  
% 0.51/1.03  fof(f10,axiom,(
% 0.51/1.03    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.51/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.51/1.03  
% 0.51/1.03  fof(f42,plain,(
% 0.51/1.03    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.51/1.03    inference(cnf_transformation,[],[f10])).
% 0.51/1.03  
% 0.51/1.03  fof(f47,plain,(
% 0.51/1.03    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.51/1.03    inference(definition_unfolding,[],[f41,f42])).
% 0.51/1.03  
% 0.51/1.03  fof(f11,conjecture,(
% 0.51/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)))),
% 0.51/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.51/1.03  
% 0.51/1.03  fof(f12,negated_conjecture,(
% 0.51/1.03    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)))),
% 0.51/1.03    inference(negated_conjecture,[],[f11])).
% 0.51/1.03  
% 0.51/1.03  fof(f25,plain,(
% 0.51/1.03    ? [X0,X1,X2] : ((~r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) | ~r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.51/1.03    inference(ennf_transformation,[],[f12])).
% 0.51/1.03  
% 0.51/1.03  fof(f28,plain,(
% 0.51/1.03    ? [X0,X1,X2] : ((~r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) | ~r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.51/1.03    introduced(choice_axiom,[])).
% 0.51/1.03  
% 0.51/1.03  fof(f29,plain,(
% 0.51/1.03    (~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.51/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f28])).
% 0.51/1.03  
% 0.51/1.03  fof(f43,plain,(
% 0.51/1.03    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.51/1.03    inference(cnf_transformation,[],[f29])).
% 0.51/1.03  
% 0.51/1.03  fof(f7,axiom,(
% 0.51/1.03    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5))),
% 0.51/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.51/1.03  
% 0.51/1.03  fof(f21,plain,(
% 0.51/1.03    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.51/1.03    inference(ennf_transformation,[],[f7])).
% 0.51/1.03  
% 0.51/1.03  fof(f22,plain,(
% 0.51/1.03    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.51/1.03    inference(flattening,[],[f21])).
% 0.51/1.03  
% 0.51/1.03  fof(f39,plain,(
% 0.51/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.51/1.03    inference(cnf_transformation,[],[f22])).
% 0.51/1.03  
% 0.51/1.03  fof(f44,plain,(
% 0.51/1.03    ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)),
% 0.51/1.03    inference(cnf_transformation,[],[f29])).
% 0.51/1.03  
% 0.51/1.03  fof(f6,axiom,(
% 0.51/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.51/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.51/1.03  
% 0.51/1.03  fof(f20,plain,(
% 0.51/1.03    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.51/1.03    inference(ennf_transformation,[],[f6])).
% 0.51/1.03  
% 0.51/1.03  fof(f37,plain,(
% 0.51/1.03    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.51/1.03    inference(cnf_transformation,[],[f20])).
% 0.51/1.03  
% 0.51/1.03  fof(f1,axiom,(
% 0.51/1.03    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.51/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.51/1.03  
% 0.51/1.03  fof(f13,plain,(
% 0.51/1.03    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.51/1.03    inference(ennf_transformation,[],[f1])).
% 0.51/1.03  
% 0.51/1.03  fof(f26,plain,(
% 0.51/1.03    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.51/1.03    inference(nnf_transformation,[],[f13])).
% 0.51/1.03  
% 0.51/1.03  fof(f30,plain,(
% 0.51/1.03    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.51/1.03    inference(cnf_transformation,[],[f26])).
% 0.51/1.03  
% 0.51/1.03  fof(f5,axiom,(
% 0.51/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.51/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.51/1.03  
% 0.51/1.03  fof(f19,plain,(
% 0.51/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.51/1.03    inference(ennf_transformation,[],[f5])).
% 0.51/1.03  
% 0.51/1.03  fof(f36,plain,(
% 0.51/1.03    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.51/1.03    inference(cnf_transformation,[],[f19])).
% 0.51/1.03  
% 0.51/1.03  fof(f3,axiom,(
% 0.51/1.03    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.51/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.51/1.03  
% 0.51/1.03  fof(f15,plain,(
% 0.51/1.03    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.51/1.03    inference(ennf_transformation,[],[f3])).
% 0.51/1.03  
% 0.51/1.03  fof(f16,plain,(
% 0.51/1.03    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.51/1.03    inference(flattening,[],[f15])).
% 0.51/1.03  
% 0.51/1.03  fof(f34,plain,(
% 0.51/1.03    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.51/1.03    inference(cnf_transformation,[],[f16])).
% 0.51/1.03  
% 0.51/1.03  fof(f45,plain,(
% 0.51/1.03    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.51/1.03    inference(definition_unfolding,[],[f34,f42])).
% 0.51/1.03  
% 0.51/1.03  fof(f4,axiom,(
% 0.51/1.03    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.51/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.51/1.03  
% 0.51/1.03  fof(f17,plain,(
% 0.51/1.03    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.51/1.03    inference(ennf_transformation,[],[f4])).
% 0.51/1.03  
% 0.51/1.03  fof(f18,plain,(
% 0.51/1.03    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.51/1.03    inference(flattening,[],[f17])).
% 0.51/1.03  
% 0.51/1.03  fof(f35,plain,(
% 0.51/1.03    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.51/1.03    inference(cnf_transformation,[],[f18])).
% 0.51/1.03  
% 0.51/1.03  fof(f46,plain,(
% 0.51/1.03    ( ! [X0,X1] : (k5_relat_1(X1,k6_partfun1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.51/1.03    inference(definition_unfolding,[],[f35,f42])).
% 0.51/1.03  
% 0.51/1.03  fof(f8,axiom,(
% 0.51/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.51/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.51/1.03  
% 0.51/1.03  fof(f23,plain,(
% 0.51/1.03    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.51/1.03    inference(ennf_transformation,[],[f8])).
% 0.51/1.03  
% 0.51/1.03  fof(f24,plain,(
% 0.51/1.03    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.51/1.03    inference(flattening,[],[f23])).
% 0.51/1.03  
% 0.51/1.03  fof(f40,plain,(
% 0.51/1.03    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.51/1.03    inference(cnf_transformation,[],[f24])).
% 0.51/1.03  
% 0.51/1.03  fof(f2,axiom,(
% 0.51/1.03    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.51/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.51/1.03  
% 0.51/1.03  fof(f14,plain,(
% 0.51/1.03    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.51/1.03    inference(ennf_transformation,[],[f2])).
% 0.51/1.03  
% 0.51/1.03  fof(f27,plain,(
% 0.51/1.03    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.51/1.03    inference(nnf_transformation,[],[f14])).
% 0.51/1.03  
% 0.51/1.03  fof(f32,plain,(
% 0.51/1.03    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.51/1.03    inference(cnf_transformation,[],[f27])).
% 0.51/1.03  
% 0.51/1.03  fof(f38,plain,(
% 0.51/1.03    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.51/1.03    inference(cnf_transformation,[],[f20])).
% 0.51/1.03  
% 0.51/1.03  cnf(c_523,plain,
% 0.51/1.03      ( ~ r2_relset_1(X0_47,X1_47,X0_44,X1_44)
% 0.51/1.03      | r2_relset_1(X0_47,X1_47,X2_44,X3_44)
% 0.51/1.03      | X2_44 != X0_44
% 0.51/1.03      | X3_44 != X1_44 ),
% 0.51/1.03      theory(equality) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_892,plain,
% 0.51/1.03      ( r2_relset_1(sK0,sK1,X0_44,X1_44)
% 0.51/1.03      | ~ r2_relset_1(sK0,sK1,sK2,sK2)
% 0.51/1.03      | X0_44 != sK2
% 0.51/1.03      | X1_44 != sK2 ),
% 0.51/1.03      inference(instantiation,[status(thm)],[c_523]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_1422,plain,
% 0.51/1.03      ( r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_partfun1(sK1)),X0_44)
% 0.51/1.03      | ~ r2_relset_1(sK0,sK1,sK2,sK2)
% 0.51/1.03      | X0_44 != sK2
% 0.51/1.03      | k5_relat_1(sK2,k6_partfun1(sK1)) != sK2 ),
% 0.51/1.03      inference(instantiation,[status(thm)],[c_892]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_1424,plain,
% 0.51/1.03      ( r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_partfun1(sK1)),sK2)
% 0.51/1.03      | ~ r2_relset_1(sK0,sK1,sK2,sK2)
% 0.51/1.03      | k5_relat_1(sK2,k6_partfun1(sK1)) != sK2
% 0.51/1.03      | sK2 != sK2 ),
% 0.51/1.03      inference(instantiation,[status(thm)],[c_1422]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_11,plain,
% 0.51/1.03      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 0.51/1.03      inference(cnf_transformation,[],[f47]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_509,plain,
% 0.51/1.03      ( m1_subset_1(k6_partfun1(X0_47),k1_zfmisc_1(k2_zfmisc_1(X0_47,X0_47))) ),
% 0.51/1.03      inference(subtyping,[status(esa)],[c_11]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_738,plain,
% 0.51/1.03      ( m1_subset_1(k6_partfun1(X0_47),k1_zfmisc_1(k2_zfmisc_1(X0_47,X0_47))) = iProver_top ),
% 0.51/1.03      inference(predicate_to_equality,[status(thm)],[c_509]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_13,negated_conjecture,
% 0.51/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 0.51/1.03      inference(cnf_transformation,[],[f43]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_507,negated_conjecture,
% 0.51/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 0.51/1.03      inference(subtyping,[status(esa)],[c_13]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_740,plain,
% 0.51/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 0.51/1.03      inference(predicate_to_equality,[status(thm)],[c_507]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_9,plain,
% 0.51/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.51/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 0.51/1.03      | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 0.51/1.03      inference(cnf_transformation,[],[f39]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_511,plain,
% 0.51/1.03      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 0.51/1.03      | ~ m1_subset_1(X1_44,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47)))
% 0.51/1.03      | k4_relset_1(X2_47,X3_47,X0_47,X1_47,X1_44,X0_44) = k5_relat_1(X1_44,X0_44) ),
% 0.51/1.03      inference(subtyping,[status(esa)],[c_9]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_736,plain,
% 0.51/1.03      ( k4_relset_1(X0_47,X1_47,X2_47,X3_47,X0_44,X1_44) = k5_relat_1(X0_44,X1_44)
% 0.51/1.03      | m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
% 0.51/1.03      | m1_subset_1(X1_44,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47))) != iProver_top ),
% 0.51/1.03      inference(predicate_to_equality,[status(thm)],[c_511]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_1094,plain,
% 0.51/1.03      ( k4_relset_1(X0_47,X1_47,sK0,sK1,X0_44,sK2) = k5_relat_1(X0_44,sK2)
% 0.51/1.03      | m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
% 0.51/1.03      inference(superposition,[status(thm)],[c_740,c_736]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_1276,plain,
% 0.51/1.03      ( k4_relset_1(X0_47,X0_47,sK0,sK1,k6_partfun1(X0_47),sK2) = k5_relat_1(k6_partfun1(X0_47),sK2) ),
% 0.51/1.03      inference(superposition,[status(thm)],[c_738,c_1094]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_12,negated_conjecture,
% 0.51/1.03      ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
% 0.51/1.03      | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) ),
% 0.51/1.03      inference(cnf_transformation,[],[f44]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_508,negated_conjecture,
% 0.51/1.03      ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
% 0.51/1.03      | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) ),
% 0.51/1.03      inference(subtyping,[status(esa)],[c_12]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_739,plain,
% 0.51/1.03      ( r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) != iProver_top
% 0.51/1.03      | r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) != iProver_top ),
% 0.51/1.03      inference(predicate_to_equality,[status(thm)],[c_508]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_1404,plain,
% 0.51/1.03      ( r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) != iProver_top
% 0.51/1.03      | r2_relset_1(sK0,sK1,k5_relat_1(k6_partfun1(sK0),sK2),sK2) != iProver_top ),
% 0.51/1.03      inference(demodulation,[status(thm)],[c_1276,c_739]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_8,plain,
% 0.51/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.51/1.03      | v4_relat_1(X0,X1) ),
% 0.51/1.03      inference(cnf_transformation,[],[f37]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_1,plain,
% 0.51/1.03      ( r1_tarski(k1_relat_1(X0),X1)
% 0.51/1.03      | ~ v4_relat_1(X0,X1)
% 0.51/1.03      | ~ v1_relat_1(X0) ),
% 0.51/1.03      inference(cnf_transformation,[],[f30]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_165,plain,
% 0.51/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.51/1.03      | r1_tarski(k1_relat_1(X0),X1)
% 0.51/1.03      | ~ v1_relat_1(X0) ),
% 0.51/1.03      inference(resolution,[status(thm)],[c_8,c_1]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_6,plain,
% 0.51/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.51/1.03      | v1_relat_1(X0) ),
% 0.51/1.03      inference(cnf_transformation,[],[f36]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_169,plain,
% 0.51/1.03      ( r1_tarski(k1_relat_1(X0),X1)
% 0.51/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 0.51/1.03      inference(global_propositional_subsumption,
% 0.51/1.03                [status(thm)],
% 0.51/1.03                [c_165,c_6]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_170,plain,
% 0.51/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.51/1.03      | r1_tarski(k1_relat_1(X0),X1) ),
% 0.51/1.03      inference(renaming,[status(thm)],[c_169]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_506,plain,
% 0.51/1.03      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 0.51/1.03      | r1_tarski(k1_relat_1(X0_44),X0_47) ),
% 0.51/1.03      inference(subtyping,[status(esa)],[c_170]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_741,plain,
% 0.51/1.03      ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
% 0.51/1.03      | r1_tarski(k1_relat_1(X0_44),X0_47) = iProver_top ),
% 0.51/1.03      inference(predicate_to_equality,[status(thm)],[c_506]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_1006,plain,
% 0.51/1.03      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 0.51/1.03      inference(superposition,[status(thm)],[c_740,c_741]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_4,plain,
% 0.51/1.03      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 0.51/1.03      | ~ v1_relat_1(X0)
% 0.51/1.03      | k5_relat_1(k6_partfun1(X1),X0) = X0 ),
% 0.51/1.03      inference(cnf_transformation,[],[f45]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_514,plain,
% 0.51/1.03      ( ~ r1_tarski(k1_relat_1(X0_44),X0_47)
% 0.51/1.03      | ~ v1_relat_1(X0_44)
% 0.51/1.03      | k5_relat_1(k6_partfun1(X0_47),X0_44) = X0_44 ),
% 0.51/1.03      inference(subtyping,[status(esa)],[c_4]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_733,plain,
% 0.51/1.03      ( k5_relat_1(k6_partfun1(X0_47),X0_44) = X0_44
% 0.51/1.03      | r1_tarski(k1_relat_1(X0_44),X0_47) != iProver_top
% 0.51/1.03      | v1_relat_1(X0_44) != iProver_top ),
% 0.51/1.03      inference(predicate_to_equality,[status(thm)],[c_514]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_1042,plain,
% 0.51/1.03      ( k5_relat_1(k6_partfun1(sK0),sK2) = sK2
% 0.51/1.03      | v1_relat_1(sK2) != iProver_top ),
% 0.51/1.03      inference(superposition,[status(thm)],[c_1006,c_733]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_533,plain,
% 0.51/1.03      ( ~ r1_tarski(k1_relat_1(sK2),sK0)
% 0.51/1.03      | ~ v1_relat_1(sK2)
% 0.51/1.03      | k5_relat_1(k6_partfun1(sK0),sK2) = sK2 ),
% 0.51/1.03      inference(instantiation,[status(thm)],[c_514]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_512,plain,
% 0.51/1.03      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 0.51/1.03      | v1_relat_1(X0_44) ),
% 0.51/1.03      inference(subtyping,[status(esa)],[c_6]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_810,plain,
% 0.51/1.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 0.51/1.03      | v1_relat_1(sK2) ),
% 0.51/1.03      inference(instantiation,[status(thm)],[c_512]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_826,plain,
% 0.51/1.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 0.51/1.03      | r1_tarski(k1_relat_1(sK2),sK0) ),
% 0.51/1.03      inference(instantiation,[status(thm)],[c_506]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_1400,plain,
% 0.51/1.03      ( k5_relat_1(k6_partfun1(sK0),sK2) = sK2 ),
% 0.51/1.03      inference(global_propositional_subsumption,
% 0.51/1.03                [status(thm)],
% 0.51/1.03                [c_1042,c_13,c_533,c_810,c_826]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_1405,plain,
% 0.51/1.03      ( r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) != iProver_top
% 0.51/1.03      | r2_relset_1(sK0,sK1,sK2,sK2) != iProver_top ),
% 0.51/1.03      inference(light_normalisation,[status(thm)],[c_1404,c_1400]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_1406,plain,
% 0.51/1.03      ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
% 0.51/1.03      | ~ r2_relset_1(sK0,sK1,sK2,sK2) ),
% 0.51/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_1405]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_1185,plain,
% 0.51/1.03      ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 0.51/1.03      inference(instantiation,[status(thm)],[c_509]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_862,plain,
% 0.51/1.03      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 0.51/1.03      | ~ m1_subset_1(k6_partfun1(X2_47),k1_zfmisc_1(k2_zfmisc_1(X2_47,X2_47)))
% 0.51/1.03      | k4_relset_1(X0_47,X1_47,X2_47,X2_47,X0_44,k6_partfun1(X2_47)) = k5_relat_1(X0_44,k6_partfun1(X2_47)) ),
% 0.51/1.03      inference(instantiation,[status(thm)],[c_511]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_1023,plain,
% 0.51/1.03      ( ~ m1_subset_1(k6_partfun1(X0_47),k1_zfmisc_1(k2_zfmisc_1(X0_47,X0_47)))
% 0.51/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 0.51/1.03      | k4_relset_1(sK0,sK1,X0_47,X0_47,sK2,k6_partfun1(X0_47)) = k5_relat_1(sK2,k6_partfun1(X0_47)) ),
% 0.51/1.03      inference(instantiation,[status(thm)],[c_862]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_1172,plain,
% 0.51/1.03      ( ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 0.51/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 0.51/1.03      | k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)) = k5_relat_1(sK2,k6_partfun1(sK1)) ),
% 0.51/1.03      inference(instantiation,[status(thm)],[c_1023]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_954,plain,
% 0.51/1.03      ( ~ r2_relset_1(sK0,sK1,X0_44,X1_44)
% 0.51/1.03      | r2_relset_1(sK0,sK1,X2_44,X3_44)
% 0.51/1.03      | X2_44 != X0_44
% 0.51/1.03      | X3_44 != X1_44 ),
% 0.51/1.03      inference(instantiation,[status(thm)],[c_523]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_1067,plain,
% 0.51/1.03      ( ~ r2_relset_1(sK0,sK1,X0_44,X1_44)
% 0.51/1.03      | r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
% 0.51/1.03      | k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)) != X0_44
% 0.51/1.03      | sK2 != X1_44 ),
% 0.51/1.03      inference(instantiation,[status(thm)],[c_954]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_1171,plain,
% 0.51/1.03      ( r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
% 0.51/1.03      | ~ r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_partfun1(sK1)),X0_44)
% 0.51/1.03      | k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)) != k5_relat_1(sK2,k6_partfun1(sK1))
% 0.51/1.03      | sK2 != X0_44 ),
% 0.51/1.03      inference(instantiation,[status(thm)],[c_1067]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_1174,plain,
% 0.51/1.03      ( r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
% 0.51/1.03      | ~ r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_partfun1(sK1)),sK2)
% 0.51/1.03      | k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)) != k5_relat_1(sK2,k6_partfun1(sK1))
% 0.51/1.03      | sK2 != sK2 ),
% 0.51/1.03      inference(instantiation,[status(thm)],[c_1171]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_5,plain,
% 0.51/1.03      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 0.51/1.03      | ~ v1_relat_1(X0)
% 0.51/1.03      | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
% 0.51/1.03      inference(cnf_transformation,[],[f46]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_513,plain,
% 0.51/1.03      ( ~ r1_tarski(k2_relat_1(X0_44),X0_47)
% 0.51/1.03      | ~ v1_relat_1(X0_44)
% 0.51/1.03      | k5_relat_1(X0_44,k6_partfun1(X0_47)) = X0_44 ),
% 0.51/1.03      inference(subtyping,[status(esa)],[c_5]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_934,plain,
% 0.51/1.03      ( ~ r1_tarski(k2_relat_1(sK2),sK1)
% 0.51/1.03      | ~ v1_relat_1(sK2)
% 0.51/1.03      | k5_relat_1(sK2,k6_partfun1(sK1)) = sK2 ),
% 0.51/1.03      inference(instantiation,[status(thm)],[c_513]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_10,plain,
% 0.51/1.03      ( r2_relset_1(X0,X1,X2,X2)
% 0.51/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 0.51/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 0.51/1.03      inference(cnf_transformation,[],[f40]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_510,plain,
% 0.51/1.03      ( r2_relset_1(X0_47,X1_47,X0_44,X0_44)
% 0.51/1.03      | ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 0.51/1.03      | ~ m1_subset_1(X1_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) ),
% 0.51/1.03      inference(subtyping,[status(esa)],[c_10]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_842,plain,
% 0.51/1.03      ( r2_relset_1(sK0,sK1,sK2,sK2)
% 0.51/1.03      | ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 0.51/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 0.51/1.03      inference(instantiation,[status(thm)],[c_510]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_844,plain,
% 0.51/1.03      ( r2_relset_1(sK0,sK1,sK2,sK2)
% 0.51/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 0.51/1.03      inference(instantiation,[status(thm)],[c_842]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_3,plain,
% 0.51/1.03      ( ~ v5_relat_1(X0,X1)
% 0.51/1.03      | r1_tarski(k2_relat_1(X0),X1)
% 0.51/1.03      | ~ v1_relat_1(X0) ),
% 0.51/1.03      inference(cnf_transformation,[],[f32]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_7,plain,
% 0.51/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.51/1.03      | v5_relat_1(X0,X2) ),
% 0.51/1.03      inference(cnf_transformation,[],[f38]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_187,plain,
% 0.51/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.51/1.03      | r1_tarski(k2_relat_1(X3),X4)
% 0.51/1.03      | ~ v1_relat_1(X3)
% 0.51/1.03      | X0 != X3
% 0.51/1.03      | X2 != X4 ),
% 0.51/1.03      inference(resolution_lifted,[status(thm)],[c_3,c_7]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_188,plain,
% 0.51/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.51/1.03      | r1_tarski(k2_relat_1(X0),X2)
% 0.51/1.03      | ~ v1_relat_1(X0) ),
% 0.51/1.03      inference(unflattening,[status(thm)],[c_187]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_192,plain,
% 0.51/1.03      ( r1_tarski(k2_relat_1(X0),X2)
% 0.51/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 0.51/1.03      inference(global_propositional_subsumption,
% 0.51/1.03                [status(thm)],
% 0.51/1.03                [c_188,c_6]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_193,plain,
% 0.51/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.51/1.03      | r1_tarski(k2_relat_1(X0),X2) ),
% 0.51/1.03      inference(renaming,[status(thm)],[c_192]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_505,plain,
% 0.51/1.03      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 0.51/1.03      | r1_tarski(k2_relat_1(X0_44),X1_47) ),
% 0.51/1.03      inference(subtyping,[status(esa)],[c_193]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_818,plain,
% 0.51/1.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 0.51/1.03      | r1_tarski(k2_relat_1(sK2),sK1) ),
% 0.51/1.03      inference(instantiation,[status(thm)],[c_505]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_516,plain,( X0_44 = X0_44 ),theory(equality) ).
% 0.51/1.03  
% 0.51/1.03  cnf(c_530,plain,
% 0.51/1.03      ( sK2 = sK2 ),
% 0.51/1.03      inference(instantiation,[status(thm)],[c_516]) ).
% 0.51/1.03  
% 0.51/1.03  cnf(contradiction,plain,
% 0.51/1.03      ( $false ),
% 0.51/1.03      inference(minisat,
% 0.51/1.03                [status(thm)],
% 0.51/1.03                [c_1424,c_1406,c_1185,c_1172,c_1174,c_934,c_844,c_818,
% 0.51/1.03                 c_810,c_530,c_13]) ).
% 0.51/1.03  
% 0.51/1.03  
% 0.51/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 0.51/1.03  
% 0.51/1.03  ------                               Statistics
% 0.51/1.03  
% 0.51/1.03  ------ General
% 0.51/1.03  
% 0.51/1.03  abstr_ref_over_cycles:                  0
% 0.51/1.03  abstr_ref_under_cycles:                 0
% 0.51/1.03  gc_basic_clause_elim:                   0
% 0.51/1.03  forced_gc_time:                         0
% 0.51/1.03  parsing_time:                           0.008
% 0.51/1.03  unif_index_cands_time:                  0.
% 0.51/1.03  unif_index_add_time:                    0.
% 0.51/1.03  orderings_time:                         0.
% 0.51/1.03  out_proof_time:                         0.011
% 0.51/1.03  total_time:                             0.081
% 0.51/1.03  num_of_symbols:                         52
% 0.51/1.03  num_of_terms:                           1481
% 0.51/1.03  
% 0.51/1.03  ------ Preprocessing
% 0.51/1.03  
% 0.51/1.03  num_of_splits:                          0
% 0.51/1.03  num_of_split_atoms:                     0
% 0.51/1.03  num_of_reused_defs:                     0
% 0.51/1.03  num_eq_ax_congr_red:                    27
% 0.51/1.03  num_of_sem_filtered_clauses:            1
% 0.51/1.03  num_of_subtypes:                        5
% 0.51/1.03  monotx_restored_types:                  1
% 0.51/1.03  sat_num_of_epr_types:                   0
% 0.51/1.03  sat_num_of_non_cyclic_types:            0
% 0.51/1.03  sat_guarded_non_collapsed_types:        0
% 0.51/1.03  num_pure_diseq_elim:                    0
% 0.51/1.03  simp_replaced_by:                       0
% 0.51/1.03  res_preprocessed:                       61
% 0.51/1.03  prep_upred:                             0
% 0.51/1.03  prep_unflattend:                        8
% 0.51/1.03  smt_new_axioms:                         0
% 0.51/1.03  pred_elim_cands:                        4
% 0.51/1.03  pred_elim:                              2
% 0.51/1.03  pred_elim_cl:                           4
% 0.51/1.03  pred_elim_cycles:                       6
% 0.51/1.03  merged_defs:                            0
% 0.51/1.03  merged_defs_ncl:                        0
% 0.51/1.03  bin_hyper_res:                          0
% 0.51/1.03  prep_cycles:                            4
% 0.51/1.03  pred_elim_time:                         0.004
% 0.51/1.03  splitting_time:                         0.
% 0.51/1.03  sem_filter_time:                        0.
% 0.51/1.03  monotx_time:                            0.
% 0.51/1.03  subtype_inf_time:                       0.001
% 0.51/1.03  
% 0.51/1.03  ------ Problem properties
% 0.51/1.03  
% 0.51/1.03  clauses:                                10
% 0.51/1.03  conjectures:                            2
% 0.51/1.03  epr:                                    0
% 0.51/1.03  horn:                                   10
% 0.51/1.03  ground:                                 2
% 0.51/1.03  unary:                                  2
% 0.51/1.03  binary:                                 4
% 0.51/1.03  lits:                                   22
% 0.51/1.03  lits_eq:                                3
% 0.51/1.03  fd_pure:                                0
% 0.51/1.03  fd_pseudo:                              0
% 0.51/1.03  fd_cond:                                0
% 0.51/1.03  fd_pseudo_cond:                         0
% 0.51/1.03  ac_symbols:                             0
% 0.51/1.03  
% 0.51/1.03  ------ Propositional Solver
% 0.51/1.03  
% 0.51/1.03  prop_solver_calls:                      27
% 0.51/1.03  prop_fast_solver_calls:                 376
% 0.51/1.03  smt_solver_calls:                       0
% 0.51/1.03  smt_fast_solver_calls:                  0
% 0.51/1.03  prop_num_of_clauses:                    491
% 0.51/1.03  prop_preprocess_simplified:             2157
% 0.51/1.03  prop_fo_subsumed:                       6
% 0.51/1.03  prop_solver_time:                       0.
% 0.51/1.03  smt_solver_time:                        0.
% 0.51/1.03  smt_fast_solver_time:                   0.
% 0.51/1.03  prop_fast_solver_time:                  0.
% 0.51/1.03  prop_unsat_core_time:                   0.
% 0.51/1.03  
% 0.51/1.03  ------ QBF
% 0.51/1.03  
% 0.51/1.03  qbf_q_res:                              0
% 0.51/1.03  qbf_num_tautologies:                    0
% 0.51/1.03  qbf_prep_cycles:                        0
% 0.51/1.03  
% 0.51/1.03  ------ BMC1
% 0.51/1.03  
% 0.51/1.03  bmc1_current_bound:                     -1
% 0.51/1.03  bmc1_last_solved_bound:                 -1
% 0.51/1.03  bmc1_unsat_core_size:                   -1
% 0.51/1.03  bmc1_unsat_core_parents_size:           -1
% 0.51/1.03  bmc1_merge_next_fun:                    0
% 0.51/1.03  bmc1_unsat_core_clauses_time:           0.
% 0.51/1.03  
% 0.51/1.03  ------ Instantiation
% 0.51/1.03  
% 0.51/1.03  inst_num_of_clauses:                    125
% 0.51/1.03  inst_num_in_passive:                    36
% 0.51/1.03  inst_num_in_active:                     86
% 0.51/1.03  inst_num_in_unprocessed:                2
% 0.51/1.03  inst_num_of_loops:                      95
% 0.51/1.03  inst_num_of_learning_restarts:          0
% 0.51/1.03  inst_num_moves_active_passive:          4
% 0.51/1.03  inst_lit_activity:                      0
% 0.51/1.03  inst_lit_activity_moves:                0
% 0.51/1.03  inst_num_tautologies:                   0
% 0.51/1.03  inst_num_prop_implied:                  0
% 0.51/1.03  inst_num_existing_simplified:           0
% 0.51/1.03  inst_num_eq_res_simplified:             0
% 0.51/1.03  inst_num_child_elim:                    0
% 0.51/1.03  inst_num_of_dismatching_blockings:      19
% 0.51/1.03  inst_num_of_non_proper_insts:           90
% 0.51/1.03  inst_num_of_duplicates:                 0
% 0.51/1.03  inst_inst_num_from_inst_to_res:         0
% 0.51/1.03  inst_dismatching_checking_time:         0.
% 0.51/1.03  
% 0.51/1.03  ------ Resolution
% 0.51/1.03  
% 0.51/1.03  res_num_of_clauses:                     0
% 0.51/1.03  res_num_in_passive:                     0
% 0.51/1.03  res_num_in_active:                      0
% 0.51/1.03  res_num_of_loops:                       65
% 0.51/1.03  res_forward_subset_subsumed:            1
% 0.51/1.03  res_backward_subset_subsumed:           0
% 0.51/1.03  res_forward_subsumed:                   0
% 0.51/1.03  res_backward_subsumed:                  0
% 0.51/1.03  res_forward_subsumption_resolution:     0
% 0.51/1.03  res_backward_subsumption_resolution:    0
% 0.51/1.03  res_clause_to_clause_subsumption:       54
% 0.51/1.03  res_orphan_elimination:                 0
% 0.51/1.03  res_tautology_del:                      10
% 0.51/1.03  res_num_eq_res_simplified:              0
% 0.51/1.03  res_num_sel_changes:                    0
% 0.51/1.03  res_moves_from_active_to_pass:          0
% 0.51/1.03  
% 0.51/1.03  ------ Superposition
% 0.51/1.03  
% 0.51/1.03  sup_time_total:                         0.
% 0.51/1.03  sup_time_generating:                    0.
% 0.51/1.03  sup_time_sim_full:                      0.
% 0.51/1.03  sup_time_sim_immed:                     0.
% 0.51/1.03  
% 0.51/1.03  sup_num_of_clauses:                     22
% 0.51/1.03  sup_num_in_active:                      17
% 0.51/1.03  sup_num_in_passive:                     5
% 0.51/1.03  sup_num_of_loops:                       18
% 0.51/1.03  sup_fw_superposition:                   11
% 0.51/1.03  sup_bw_superposition:                   1
% 0.51/1.03  sup_immediate_simplified:               1
% 0.51/1.03  sup_given_eliminated:                   0
% 0.51/1.03  comparisons_done:                       0
% 0.51/1.03  comparisons_avoided:                    0
% 0.51/1.03  
% 0.51/1.03  ------ Simplifications
% 0.51/1.03  
% 0.51/1.03  
% 0.51/1.03  sim_fw_subset_subsumed:                 0
% 0.51/1.03  sim_bw_subset_subsumed:                 0
% 0.51/1.03  sim_fw_subsumed:                        0
% 0.51/1.03  sim_bw_subsumed:                        0
% 0.51/1.03  sim_fw_subsumption_res:                 0
% 0.51/1.03  sim_bw_subsumption_res:                 0
% 0.51/1.03  sim_tautology_del:                      0
% 0.51/1.03  sim_eq_tautology_del:                   0
% 0.51/1.03  sim_eq_res_simp:                        0
% 0.51/1.03  sim_fw_demodulated:                     0
% 0.51/1.03  sim_bw_demodulated:                     1
% 0.51/1.03  sim_light_normalised:                   1
% 0.51/1.03  sim_joinable_taut:                      0
% 0.51/1.03  sim_joinable_simp:                      0
% 0.51/1.03  sim_ac_normalised:                      0
% 0.51/1.03  sim_smt_subsumption:                    0
% 0.51/1.03  
%------------------------------------------------------------------------------
