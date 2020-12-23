%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:55:20 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 158 expanded)
%              Number of clauses        :   51 (  62 expanded)
%              Number of leaves         :   12 (  30 expanded)
%              Depth                    :   15
%              Number of atoms          :  236 ( 477 expanded)
%              Number of equality atoms :  106 ( 162 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X1),X2)
       => ( k2_relset_1(X0,X1,X2) = X1
          & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(k6_relat_1(X1),X2)
         => ( k2_relset_1(X0,X1,X2) = X1
            & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f20])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_relset_1(X0,X1,X2) != X1
          | ~ r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
        & r1_tarski(k6_relat_1(X1),X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( k2_relset_1(sK0,sK1,sK2) != sK1
        | ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) )
      & r1_tarski(k6_relat_1(sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ( k2_relset_1(sK0,sK1,sK2) != sK1
      | ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) )
    & r1_tarski(k6_relat_1(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f25])).

fof(f42,plain,(
    r1_tarski(k6_relat_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f29,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f43,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    | ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(k6_relat_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_500,plain,
    ( r1_tarski(k6_relat_1(sK1),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_8,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_503,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1406,plain,
    ( r1_tarski(X0,k2_relat_1(X1)) = iProver_top
    | r1_tarski(k6_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_503])).

cnf(c_5,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_40,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1763,plain,
    ( v1_relat_1(X1) != iProver_top
    | r1_tarski(k6_relat_1(X0),X1) != iProver_top
    | r1_tarski(X0,k2_relat_1(X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1406,c_40])).

cnf(c_1764,plain,
    ( r1_tarski(X0,k2_relat_1(X1)) = iProver_top
    | r1_tarski(k6_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_1763])).

cnf(c_1773,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_500,c_1764])).

cnf(c_9,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_502,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1261,plain,
    ( r1_tarski(X0,k1_relat_1(X1)) = iProver_top
    | r1_tarski(k6_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_502])).

cnf(c_1445,plain,
    ( v1_relat_1(X1) != iProver_top
    | r1_tarski(k6_relat_1(X0),X1) != iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1261,c_40])).

cnf(c_1446,plain,
    ( r1_tarski(X0,k1_relat_1(X1)) = iProver_top
    | r1_tarski(k6_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_1445])).

cnf(c_1455,plain,
    ( r1_tarski(sK1,k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_500,c_1446])).

cnf(c_4,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_193,plain,
    ( v5_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_16])).

cnf(c_194,plain,
    ( v5_relat_1(sK2,X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_193])).

cnf(c_228,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | X2 != X1
    | k1_zfmisc_1(k2_zfmisc_1(X3,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_194])).

cnf(c_229,plain,
    ( r1_tarski(k2_relat_1(sK2),X0)
    | ~ v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_228])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_205,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_16])).

cnf(c_206,plain,
    ( v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_205])).

cnf(c_239,plain,
    ( r1_tarski(k2_relat_1(sK2),X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_229,c_206])).

cnf(c_498,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | r1_tarski(k2_relat_1(sK2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_239])).

cnf(c_888,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_498])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_506,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1152,plain,
    ( k2_relat_1(sK2) = sK1
    | r1_tarski(sK1,k2_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_888,c_506])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_175,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_16])).

cnf(c_176,plain,
    ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_175])).

cnf(c_620,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_176])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))
    | k2_relset_1(sK0,sK1,sK2) != sK1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_501,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    | r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_697,plain,
    ( k2_relat_1(sK2) != sK1
    | r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_620,c_501])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_184,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_16])).

cnf(c_185,plain,
    ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_184])).

cnf(c_623,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_185])).

cnf(c_786,plain,
    ( k2_relat_1(sK2) != sK1
    | r1_tarski(sK1,k1_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_697,c_623])).

cnf(c_587,plain,
    ( v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_206])).

cnf(c_588,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_587])).

cnf(c_318,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_584,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_318])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1773,c_1455,c_1152,c_786,c_588,c_584])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:53:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.61/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.01  
% 1.61/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.61/1.01  
% 1.61/1.01  ------  iProver source info
% 1.61/1.01  
% 1.61/1.01  git: date: 2020-06-30 10:37:57 +0100
% 1.61/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.61/1.01  git: non_committed_changes: false
% 1.61/1.01  git: last_make_outside_of_git: false
% 1.61/1.01  
% 1.61/1.01  ------ 
% 1.61/1.01  
% 1.61/1.01  ------ Input Options
% 1.61/1.01  
% 1.61/1.01  --out_options                           all
% 1.61/1.01  --tptp_safe_out                         true
% 1.61/1.01  --problem_path                          ""
% 1.61/1.01  --include_path                          ""
% 1.61/1.01  --clausifier                            res/vclausify_rel
% 1.61/1.01  --clausifier_options                    --mode clausify
% 1.61/1.01  --stdin                                 false
% 1.61/1.01  --stats_out                             all
% 1.61/1.01  
% 1.61/1.01  ------ General Options
% 1.61/1.01  
% 1.61/1.01  --fof                                   false
% 1.61/1.01  --time_out_real                         305.
% 1.61/1.01  --time_out_virtual                      -1.
% 1.61/1.01  --symbol_type_check                     false
% 1.61/1.01  --clausify_out                          false
% 1.61/1.01  --sig_cnt_out                           false
% 1.61/1.01  --trig_cnt_out                          false
% 1.61/1.01  --trig_cnt_out_tolerance                1.
% 1.61/1.01  --trig_cnt_out_sk_spl                   false
% 1.61/1.01  --abstr_cl_out                          false
% 1.61/1.01  
% 1.61/1.01  ------ Global Options
% 1.61/1.01  
% 1.61/1.01  --schedule                              default
% 1.61/1.01  --add_important_lit                     false
% 1.61/1.01  --prop_solver_per_cl                    1000
% 1.61/1.01  --min_unsat_core                        false
% 1.61/1.01  --soft_assumptions                      false
% 1.61/1.01  --soft_lemma_size                       3
% 1.61/1.01  --prop_impl_unit_size                   0
% 1.61/1.01  --prop_impl_unit                        []
% 1.61/1.01  --share_sel_clauses                     true
% 1.61/1.01  --reset_solvers                         false
% 1.61/1.01  --bc_imp_inh                            [conj_cone]
% 1.61/1.01  --conj_cone_tolerance                   3.
% 1.61/1.01  --extra_neg_conj                        none
% 1.61/1.01  --large_theory_mode                     true
% 1.61/1.01  --prolific_symb_bound                   200
% 1.61/1.01  --lt_threshold                          2000
% 1.61/1.01  --clause_weak_htbl                      true
% 1.61/1.01  --gc_record_bc_elim                     false
% 1.61/1.01  
% 1.61/1.01  ------ Preprocessing Options
% 1.61/1.01  
% 1.61/1.01  --preprocessing_flag                    true
% 1.61/1.01  --time_out_prep_mult                    0.1
% 1.61/1.01  --splitting_mode                        input
% 1.61/1.01  --splitting_grd                         true
% 1.61/1.01  --splitting_cvd                         false
% 1.61/1.01  --splitting_cvd_svl                     false
% 1.61/1.01  --splitting_nvd                         32
% 1.61/1.01  --sub_typing                            true
% 1.61/1.01  --prep_gs_sim                           true
% 1.61/1.01  --prep_unflatten                        true
% 1.61/1.01  --prep_res_sim                          true
% 1.61/1.01  --prep_upred                            true
% 1.61/1.01  --prep_sem_filter                       exhaustive
% 1.61/1.01  --prep_sem_filter_out                   false
% 1.61/1.01  --pred_elim                             true
% 1.61/1.01  --res_sim_input                         true
% 1.61/1.01  --eq_ax_congr_red                       true
% 1.61/1.01  --pure_diseq_elim                       true
% 1.61/1.01  --brand_transform                       false
% 1.61/1.01  --non_eq_to_eq                          false
% 1.61/1.01  --prep_def_merge                        true
% 1.61/1.01  --prep_def_merge_prop_impl              false
% 1.61/1.01  --prep_def_merge_mbd                    true
% 1.61/1.01  --prep_def_merge_tr_red                 false
% 1.61/1.01  --prep_def_merge_tr_cl                  false
% 1.61/1.01  --smt_preprocessing                     true
% 1.61/1.01  --smt_ac_axioms                         fast
% 1.61/1.01  --preprocessed_out                      false
% 1.61/1.01  --preprocessed_stats                    false
% 1.61/1.01  
% 1.61/1.01  ------ Abstraction refinement Options
% 1.61/1.01  
% 1.61/1.01  --abstr_ref                             []
% 1.61/1.01  --abstr_ref_prep                        false
% 1.61/1.01  --abstr_ref_until_sat                   false
% 1.61/1.01  --abstr_ref_sig_restrict                funpre
% 1.61/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.61/1.01  --abstr_ref_under                       []
% 1.61/1.01  
% 1.61/1.01  ------ SAT Options
% 1.61/1.01  
% 1.61/1.01  --sat_mode                              false
% 1.61/1.01  --sat_fm_restart_options                ""
% 1.61/1.01  --sat_gr_def                            false
% 1.61/1.01  --sat_epr_types                         true
% 1.61/1.01  --sat_non_cyclic_types                  false
% 1.61/1.01  --sat_finite_models                     false
% 1.61/1.01  --sat_fm_lemmas                         false
% 1.61/1.01  --sat_fm_prep                           false
% 1.61/1.01  --sat_fm_uc_incr                        true
% 1.61/1.01  --sat_out_model                         small
% 1.61/1.01  --sat_out_clauses                       false
% 1.61/1.01  
% 1.61/1.01  ------ QBF Options
% 1.61/1.01  
% 1.61/1.01  --qbf_mode                              false
% 1.61/1.01  --qbf_elim_univ                         false
% 1.61/1.01  --qbf_dom_inst                          none
% 1.61/1.01  --qbf_dom_pre_inst                      false
% 1.61/1.01  --qbf_sk_in                             false
% 1.61/1.01  --qbf_pred_elim                         true
% 1.61/1.01  --qbf_split                             512
% 1.61/1.01  
% 1.61/1.01  ------ BMC1 Options
% 1.61/1.01  
% 1.61/1.01  --bmc1_incremental                      false
% 1.61/1.01  --bmc1_axioms                           reachable_all
% 1.61/1.01  --bmc1_min_bound                        0
% 1.61/1.01  --bmc1_max_bound                        -1
% 1.61/1.01  --bmc1_max_bound_default                -1
% 1.61/1.01  --bmc1_symbol_reachability              true
% 1.61/1.01  --bmc1_property_lemmas                  false
% 1.61/1.01  --bmc1_k_induction                      false
% 1.61/1.01  --bmc1_non_equiv_states                 false
% 1.61/1.01  --bmc1_deadlock                         false
% 1.61/1.01  --bmc1_ucm                              false
% 1.61/1.01  --bmc1_add_unsat_core                   none
% 1.61/1.01  --bmc1_unsat_core_children              false
% 1.61/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.61/1.01  --bmc1_out_stat                         full
% 1.61/1.01  --bmc1_ground_init                      false
% 1.61/1.01  --bmc1_pre_inst_next_state              false
% 1.61/1.01  --bmc1_pre_inst_state                   false
% 1.61/1.01  --bmc1_pre_inst_reach_state             false
% 1.61/1.01  --bmc1_out_unsat_core                   false
% 1.61/1.01  --bmc1_aig_witness_out                  false
% 1.61/1.01  --bmc1_verbose                          false
% 1.61/1.01  --bmc1_dump_clauses_tptp                false
% 1.61/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.61/1.01  --bmc1_dump_file                        -
% 1.61/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.61/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.61/1.01  --bmc1_ucm_extend_mode                  1
% 1.61/1.01  --bmc1_ucm_init_mode                    2
% 1.61/1.01  --bmc1_ucm_cone_mode                    none
% 1.61/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.61/1.01  --bmc1_ucm_relax_model                  4
% 1.61/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.61/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.61/1.01  --bmc1_ucm_layered_model                none
% 1.61/1.01  --bmc1_ucm_max_lemma_size               10
% 1.61/1.01  
% 1.61/1.01  ------ AIG Options
% 1.61/1.01  
% 1.61/1.01  --aig_mode                              false
% 1.61/1.01  
% 1.61/1.01  ------ Instantiation Options
% 1.61/1.01  
% 1.61/1.01  --instantiation_flag                    true
% 1.61/1.01  --inst_sos_flag                         false
% 1.61/1.01  --inst_sos_phase                        true
% 1.61/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.61/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.61/1.01  --inst_lit_sel_side                     num_symb
% 1.61/1.01  --inst_solver_per_active                1400
% 1.61/1.01  --inst_solver_calls_frac                1.
% 1.61/1.01  --inst_passive_queue_type               priority_queues
% 1.61/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.61/1.01  --inst_passive_queues_freq              [25;2]
% 1.61/1.01  --inst_dismatching                      true
% 1.61/1.01  --inst_eager_unprocessed_to_passive     true
% 1.61/1.01  --inst_prop_sim_given                   true
% 1.61/1.01  --inst_prop_sim_new                     false
% 1.61/1.01  --inst_subs_new                         false
% 1.61/1.01  --inst_eq_res_simp                      false
% 1.61/1.01  --inst_subs_given                       false
% 1.61/1.01  --inst_orphan_elimination               true
% 1.61/1.01  --inst_learning_loop_flag               true
% 1.61/1.01  --inst_learning_start                   3000
% 1.61/1.01  --inst_learning_factor                  2
% 1.61/1.01  --inst_start_prop_sim_after_learn       3
% 1.61/1.01  --inst_sel_renew                        solver
% 1.61/1.01  --inst_lit_activity_flag                true
% 1.61/1.01  --inst_restr_to_given                   false
% 1.61/1.01  --inst_activity_threshold               500
% 1.61/1.01  --inst_out_proof                        true
% 1.61/1.01  
% 1.61/1.01  ------ Resolution Options
% 1.61/1.01  
% 1.61/1.01  --resolution_flag                       true
% 1.61/1.01  --res_lit_sel                           adaptive
% 1.61/1.01  --res_lit_sel_side                      none
% 1.61/1.01  --res_ordering                          kbo
% 1.61/1.01  --res_to_prop_solver                    active
% 1.61/1.01  --res_prop_simpl_new                    false
% 1.61/1.01  --res_prop_simpl_given                  true
% 1.61/1.01  --res_passive_queue_type                priority_queues
% 1.61/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.61/1.01  --res_passive_queues_freq               [15;5]
% 1.61/1.01  --res_forward_subs                      full
% 1.61/1.01  --res_backward_subs                     full
% 1.61/1.01  --res_forward_subs_resolution           true
% 1.61/1.01  --res_backward_subs_resolution          true
% 1.61/1.01  --res_orphan_elimination                true
% 1.61/1.01  --res_time_limit                        2.
% 1.61/1.01  --res_out_proof                         true
% 1.61/1.01  
% 1.61/1.01  ------ Superposition Options
% 1.61/1.01  
% 1.61/1.01  --superposition_flag                    true
% 1.61/1.01  --sup_passive_queue_type                priority_queues
% 1.61/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.61/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.61/1.01  --demod_completeness_check              fast
% 1.61/1.01  --demod_use_ground                      true
% 1.61/1.01  --sup_to_prop_solver                    passive
% 1.61/1.01  --sup_prop_simpl_new                    true
% 1.61/1.01  --sup_prop_simpl_given                  true
% 1.61/1.01  --sup_fun_splitting                     false
% 1.61/1.01  --sup_smt_interval                      50000
% 1.61/1.01  
% 1.61/1.01  ------ Superposition Simplification Setup
% 1.61/1.01  
% 1.61/1.01  --sup_indices_passive                   []
% 1.61/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.61/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.61/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.61/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.61/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.61/1.01  --sup_full_bw                           [BwDemod]
% 1.61/1.01  --sup_immed_triv                        [TrivRules]
% 1.61/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.61/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.61/1.01  --sup_immed_bw_main                     []
% 1.61/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.61/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.61/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.61/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.61/1.01  
% 1.61/1.01  ------ Combination Options
% 1.61/1.01  
% 1.61/1.01  --comb_res_mult                         3
% 1.61/1.01  --comb_sup_mult                         2
% 1.61/1.01  --comb_inst_mult                        10
% 1.61/1.01  
% 1.61/1.01  ------ Debug Options
% 1.61/1.01  
% 1.61/1.01  --dbg_backtrace                         false
% 1.61/1.01  --dbg_dump_prop_clauses                 false
% 1.61/1.01  --dbg_dump_prop_clauses_file            -
% 1.61/1.01  --dbg_out_stat                          false
% 1.61/1.01  ------ Parsing...
% 1.61/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.61/1.01  
% 1.61/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.61/1.01  
% 1.61/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.61/1.01  
% 1.61/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.61/1.01  ------ Proving...
% 1.61/1.01  ------ Problem Properties 
% 1.61/1.01  
% 1.61/1.01  
% 1.61/1.01  clauses                                 13
% 1.61/1.01  conjectures                             2
% 1.61/1.01  EPR                                     2
% 1.61/1.01  Horn                                    13
% 1.61/1.01  unary                                   5
% 1.61/1.01  binary                                  5
% 1.61/1.01  lits                                    26
% 1.61/1.01  lits eq                                 10
% 1.61/1.01  fd_pure                                 0
% 1.61/1.01  fd_pseudo                               0
% 1.61/1.01  fd_cond                                 0
% 1.61/1.01  fd_pseudo_cond                          1
% 1.61/1.01  AC symbols                              0
% 1.61/1.01  
% 1.61/1.01  ------ Schedule dynamic 5 is on 
% 1.61/1.01  
% 1.61/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.61/1.01  
% 1.61/1.01  
% 1.61/1.01  ------ 
% 1.61/1.01  Current options:
% 1.61/1.01  ------ 
% 1.61/1.01  
% 1.61/1.01  ------ Input Options
% 1.61/1.01  
% 1.61/1.01  --out_options                           all
% 1.61/1.01  --tptp_safe_out                         true
% 1.61/1.01  --problem_path                          ""
% 1.61/1.01  --include_path                          ""
% 1.61/1.01  --clausifier                            res/vclausify_rel
% 1.61/1.01  --clausifier_options                    --mode clausify
% 1.61/1.01  --stdin                                 false
% 1.61/1.01  --stats_out                             all
% 1.61/1.01  
% 1.61/1.01  ------ General Options
% 1.61/1.01  
% 1.61/1.01  --fof                                   false
% 1.61/1.01  --time_out_real                         305.
% 1.61/1.01  --time_out_virtual                      -1.
% 1.61/1.01  --symbol_type_check                     false
% 1.61/1.01  --clausify_out                          false
% 1.61/1.01  --sig_cnt_out                           false
% 1.61/1.01  --trig_cnt_out                          false
% 1.61/1.01  --trig_cnt_out_tolerance                1.
% 1.61/1.01  --trig_cnt_out_sk_spl                   false
% 1.61/1.01  --abstr_cl_out                          false
% 1.61/1.01  
% 1.61/1.01  ------ Global Options
% 1.61/1.01  
% 1.61/1.01  --schedule                              default
% 1.61/1.01  --add_important_lit                     false
% 1.61/1.01  --prop_solver_per_cl                    1000
% 1.61/1.01  --min_unsat_core                        false
% 1.61/1.01  --soft_assumptions                      false
% 1.61/1.01  --soft_lemma_size                       3
% 1.61/1.01  --prop_impl_unit_size                   0
% 1.61/1.01  --prop_impl_unit                        []
% 1.61/1.01  --share_sel_clauses                     true
% 1.61/1.01  --reset_solvers                         false
% 1.61/1.01  --bc_imp_inh                            [conj_cone]
% 1.61/1.01  --conj_cone_tolerance                   3.
% 1.61/1.01  --extra_neg_conj                        none
% 1.61/1.01  --large_theory_mode                     true
% 1.61/1.01  --prolific_symb_bound                   200
% 1.61/1.01  --lt_threshold                          2000
% 1.61/1.01  --clause_weak_htbl                      true
% 1.61/1.01  --gc_record_bc_elim                     false
% 1.61/1.01  
% 1.61/1.01  ------ Preprocessing Options
% 1.61/1.01  
% 1.61/1.01  --preprocessing_flag                    true
% 1.61/1.01  --time_out_prep_mult                    0.1
% 1.61/1.01  --splitting_mode                        input
% 1.61/1.01  --splitting_grd                         true
% 1.61/1.01  --splitting_cvd                         false
% 1.61/1.01  --splitting_cvd_svl                     false
% 1.61/1.01  --splitting_nvd                         32
% 1.61/1.01  --sub_typing                            true
% 1.61/1.01  --prep_gs_sim                           true
% 1.61/1.01  --prep_unflatten                        true
% 1.61/1.01  --prep_res_sim                          true
% 1.61/1.01  --prep_upred                            true
% 1.61/1.01  --prep_sem_filter                       exhaustive
% 1.61/1.01  --prep_sem_filter_out                   false
% 1.61/1.01  --pred_elim                             true
% 1.61/1.01  --res_sim_input                         true
% 1.61/1.01  --eq_ax_congr_red                       true
% 1.61/1.01  --pure_diseq_elim                       true
% 1.61/1.01  --brand_transform                       false
% 1.61/1.01  --non_eq_to_eq                          false
% 1.61/1.01  --prep_def_merge                        true
% 1.61/1.01  --prep_def_merge_prop_impl              false
% 1.61/1.01  --prep_def_merge_mbd                    true
% 1.61/1.01  --prep_def_merge_tr_red                 false
% 1.61/1.01  --prep_def_merge_tr_cl                  false
% 1.61/1.01  --smt_preprocessing                     true
% 1.61/1.01  --smt_ac_axioms                         fast
% 1.61/1.01  --preprocessed_out                      false
% 1.61/1.01  --preprocessed_stats                    false
% 1.61/1.01  
% 1.61/1.01  ------ Abstraction refinement Options
% 1.61/1.01  
% 1.61/1.01  --abstr_ref                             []
% 1.61/1.01  --abstr_ref_prep                        false
% 1.61/1.01  --abstr_ref_until_sat                   false
% 1.61/1.01  --abstr_ref_sig_restrict                funpre
% 1.61/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.61/1.01  --abstr_ref_under                       []
% 1.61/1.01  
% 1.61/1.01  ------ SAT Options
% 1.61/1.01  
% 1.61/1.01  --sat_mode                              false
% 1.61/1.01  --sat_fm_restart_options                ""
% 1.61/1.01  --sat_gr_def                            false
% 1.61/1.01  --sat_epr_types                         true
% 1.61/1.01  --sat_non_cyclic_types                  false
% 1.61/1.01  --sat_finite_models                     false
% 1.61/1.01  --sat_fm_lemmas                         false
% 1.61/1.01  --sat_fm_prep                           false
% 1.61/1.01  --sat_fm_uc_incr                        true
% 1.61/1.01  --sat_out_model                         small
% 1.61/1.01  --sat_out_clauses                       false
% 1.61/1.01  
% 1.61/1.01  ------ QBF Options
% 1.61/1.01  
% 1.61/1.01  --qbf_mode                              false
% 1.61/1.01  --qbf_elim_univ                         false
% 1.61/1.01  --qbf_dom_inst                          none
% 1.61/1.01  --qbf_dom_pre_inst                      false
% 1.61/1.01  --qbf_sk_in                             false
% 1.61/1.01  --qbf_pred_elim                         true
% 1.61/1.01  --qbf_split                             512
% 1.61/1.01  
% 1.61/1.01  ------ BMC1 Options
% 1.61/1.01  
% 1.61/1.01  --bmc1_incremental                      false
% 1.61/1.01  --bmc1_axioms                           reachable_all
% 1.61/1.01  --bmc1_min_bound                        0
% 1.61/1.01  --bmc1_max_bound                        -1
% 1.61/1.01  --bmc1_max_bound_default                -1
% 1.61/1.01  --bmc1_symbol_reachability              true
% 1.61/1.01  --bmc1_property_lemmas                  false
% 1.61/1.01  --bmc1_k_induction                      false
% 1.61/1.01  --bmc1_non_equiv_states                 false
% 1.61/1.01  --bmc1_deadlock                         false
% 1.61/1.01  --bmc1_ucm                              false
% 1.61/1.01  --bmc1_add_unsat_core                   none
% 1.61/1.01  --bmc1_unsat_core_children              false
% 1.61/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.61/1.01  --bmc1_out_stat                         full
% 1.61/1.01  --bmc1_ground_init                      false
% 1.61/1.01  --bmc1_pre_inst_next_state              false
% 1.61/1.01  --bmc1_pre_inst_state                   false
% 1.61/1.01  --bmc1_pre_inst_reach_state             false
% 1.61/1.01  --bmc1_out_unsat_core                   false
% 1.61/1.01  --bmc1_aig_witness_out                  false
% 1.61/1.01  --bmc1_verbose                          false
% 1.61/1.01  --bmc1_dump_clauses_tptp                false
% 1.61/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.61/1.01  --bmc1_dump_file                        -
% 1.61/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.61/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.61/1.01  --bmc1_ucm_extend_mode                  1
% 1.61/1.01  --bmc1_ucm_init_mode                    2
% 1.61/1.01  --bmc1_ucm_cone_mode                    none
% 1.61/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.61/1.01  --bmc1_ucm_relax_model                  4
% 1.61/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.61/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.61/1.01  --bmc1_ucm_layered_model                none
% 1.61/1.01  --bmc1_ucm_max_lemma_size               10
% 1.61/1.01  
% 1.61/1.01  ------ AIG Options
% 1.61/1.01  
% 1.61/1.01  --aig_mode                              false
% 1.61/1.01  
% 1.61/1.01  ------ Instantiation Options
% 1.61/1.01  
% 1.61/1.01  --instantiation_flag                    true
% 1.61/1.01  --inst_sos_flag                         false
% 1.61/1.01  --inst_sos_phase                        true
% 1.61/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.61/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.61/1.01  --inst_lit_sel_side                     none
% 1.61/1.01  --inst_solver_per_active                1400
% 1.61/1.01  --inst_solver_calls_frac                1.
% 1.61/1.01  --inst_passive_queue_type               priority_queues
% 1.61/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.61/1.01  --inst_passive_queues_freq              [25;2]
% 1.61/1.01  --inst_dismatching                      true
% 1.61/1.01  --inst_eager_unprocessed_to_passive     true
% 1.61/1.01  --inst_prop_sim_given                   true
% 1.61/1.01  --inst_prop_sim_new                     false
% 1.61/1.01  --inst_subs_new                         false
% 1.61/1.01  --inst_eq_res_simp                      false
% 1.61/1.01  --inst_subs_given                       false
% 1.61/1.01  --inst_orphan_elimination               true
% 1.61/1.01  --inst_learning_loop_flag               true
% 1.61/1.01  --inst_learning_start                   3000
% 1.61/1.01  --inst_learning_factor                  2
% 1.61/1.01  --inst_start_prop_sim_after_learn       3
% 1.61/1.01  --inst_sel_renew                        solver
% 1.61/1.01  --inst_lit_activity_flag                true
% 1.61/1.01  --inst_restr_to_given                   false
% 1.61/1.01  --inst_activity_threshold               500
% 1.61/1.01  --inst_out_proof                        true
% 1.61/1.01  
% 1.61/1.01  ------ Resolution Options
% 1.61/1.01  
% 1.61/1.01  --resolution_flag                       false
% 1.61/1.01  --res_lit_sel                           adaptive
% 1.61/1.01  --res_lit_sel_side                      none
% 1.61/1.01  --res_ordering                          kbo
% 1.61/1.01  --res_to_prop_solver                    active
% 1.61/1.01  --res_prop_simpl_new                    false
% 1.61/1.01  --res_prop_simpl_given                  true
% 1.61/1.01  --res_passive_queue_type                priority_queues
% 1.61/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.61/1.01  --res_passive_queues_freq               [15;5]
% 1.61/1.01  --res_forward_subs                      full
% 1.61/1.01  --res_backward_subs                     full
% 1.61/1.01  --res_forward_subs_resolution           true
% 1.61/1.01  --res_backward_subs_resolution          true
% 1.61/1.01  --res_orphan_elimination                true
% 1.61/1.01  --res_time_limit                        2.
% 1.61/1.01  --res_out_proof                         true
% 1.61/1.01  
% 1.61/1.01  ------ Superposition Options
% 1.61/1.01  
% 1.61/1.01  --superposition_flag                    true
% 1.61/1.01  --sup_passive_queue_type                priority_queues
% 1.61/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.61/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.61/1.01  --demod_completeness_check              fast
% 1.61/1.01  --demod_use_ground                      true
% 1.61/1.01  --sup_to_prop_solver                    passive
% 1.61/1.01  --sup_prop_simpl_new                    true
% 1.61/1.01  --sup_prop_simpl_given                  true
% 1.61/1.01  --sup_fun_splitting                     false
% 1.61/1.01  --sup_smt_interval                      50000
% 1.61/1.01  
% 1.61/1.01  ------ Superposition Simplification Setup
% 1.61/1.01  
% 1.61/1.01  --sup_indices_passive                   []
% 1.61/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.61/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.61/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.61/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.61/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.61/1.01  --sup_full_bw                           [BwDemod]
% 1.61/1.01  --sup_immed_triv                        [TrivRules]
% 1.61/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.61/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.61/1.01  --sup_immed_bw_main                     []
% 1.61/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.61/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.61/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.61/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.61/1.01  
% 1.61/1.01  ------ Combination Options
% 1.61/1.01  
% 1.61/1.01  --comb_res_mult                         3
% 1.61/1.01  --comb_sup_mult                         2
% 1.61/1.01  --comb_inst_mult                        10
% 1.61/1.01  
% 1.61/1.01  ------ Debug Options
% 1.61/1.01  
% 1.61/1.01  --dbg_backtrace                         false
% 1.61/1.01  --dbg_dump_prop_clauses                 false
% 1.61/1.01  --dbg_dump_prop_clauses_file            -
% 1.61/1.01  --dbg_out_stat                          false
% 1.61/1.01  
% 1.61/1.01  
% 1.61/1.01  
% 1.61/1.01  
% 1.61/1.01  ------ Proving...
% 1.61/1.01  
% 1.61/1.01  
% 1.61/1.01  % SZS status Theorem for theBenchmark.p
% 1.61/1.01  
% 1.61/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 1.61/1.01  
% 1.61/1.01  fof(f10,conjecture,(
% 1.61/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 1.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.61/1.01  
% 1.61/1.01  fof(f11,negated_conjecture,(
% 1.61/1.01    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 1.61/1.01    inference(negated_conjecture,[],[f10])).
% 1.61/1.01  
% 1.61/1.01  fof(f20,plain,(
% 1.61/1.01    ? [X0,X1,X2] : (((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.61/1.01    inference(ennf_transformation,[],[f11])).
% 1.61/1.01  
% 1.61/1.01  fof(f21,plain,(
% 1.61/1.01    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.61/1.01    inference(flattening,[],[f20])).
% 1.61/1.01  
% 1.61/1.01  fof(f25,plain,(
% 1.61/1.01    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ~r1_tarski(X1,k1_relset_1(X0,X1,X2))) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((k2_relset_1(sK0,sK1,sK2) != sK1 | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))) & r1_tarski(k6_relat_1(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 1.61/1.01    introduced(choice_axiom,[])).
% 1.61/1.01  
% 1.61/1.01  fof(f26,plain,(
% 1.61/1.01    (k2_relset_1(sK0,sK1,sK2) != sK1 | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))) & r1_tarski(k6_relat_1(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.61/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f25])).
% 1.61/1.01  
% 1.61/1.01  fof(f42,plain,(
% 1.61/1.01    r1_tarski(k6_relat_1(sK1),sK2)),
% 1.61/1.01    inference(cnf_transformation,[],[f26])).
% 1.61/1.01  
% 1.61/1.01  fof(f5,axiom,(
% 1.61/1.01    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.61/1.01  
% 1.61/1.01  fof(f36,plain,(
% 1.61/1.01    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.61/1.01    inference(cnf_transformation,[],[f5])).
% 1.61/1.01  
% 1.61/1.01  fof(f4,axiom,(
% 1.61/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.61/1.01  
% 1.61/1.01  fof(f14,plain,(
% 1.61/1.01    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.61/1.01    inference(ennf_transformation,[],[f4])).
% 1.61/1.01  
% 1.61/1.01  fof(f15,plain,(
% 1.61/1.01    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.61/1.01    inference(flattening,[],[f14])).
% 1.61/1.01  
% 1.61/1.01  fof(f34,plain,(
% 1.61/1.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.61/1.01    inference(cnf_transformation,[],[f15])).
% 1.61/1.01  
% 1.61/1.01  fof(f3,axiom,(
% 1.61/1.01    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.61/1.01  
% 1.61/1.01  fof(f32,plain,(
% 1.61/1.01    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.61/1.01    inference(cnf_transformation,[],[f3])).
% 1.61/1.01  
% 1.61/1.01  fof(f35,plain,(
% 1.61/1.01    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.61/1.01    inference(cnf_transformation,[],[f5])).
% 1.61/1.01  
% 1.61/1.01  fof(f33,plain,(
% 1.61/1.01    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.61/1.01    inference(cnf_transformation,[],[f15])).
% 1.61/1.01  
% 1.61/1.01  fof(f2,axiom,(
% 1.61/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.61/1.01  
% 1.61/1.01  fof(f13,plain,(
% 1.61/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.61/1.01    inference(ennf_transformation,[],[f2])).
% 1.61/1.01  
% 1.61/1.01  fof(f24,plain,(
% 1.61/1.01    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.61/1.01    inference(nnf_transformation,[],[f13])).
% 1.61/1.01  
% 1.61/1.01  fof(f30,plain,(
% 1.61/1.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.61/1.01    inference(cnf_transformation,[],[f24])).
% 1.61/1.01  
% 1.61/1.01  fof(f7,axiom,(
% 1.61/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.61/1.01  
% 1.61/1.01  fof(f12,plain,(
% 1.61/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.61/1.01    inference(pure_predicate_removal,[],[f7])).
% 1.61/1.01  
% 1.61/1.01  fof(f17,plain,(
% 1.61/1.01    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.61/1.01    inference(ennf_transformation,[],[f12])).
% 1.61/1.01  
% 1.61/1.01  fof(f38,plain,(
% 1.61/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.61/1.01    inference(cnf_transformation,[],[f17])).
% 1.61/1.01  
% 1.61/1.01  fof(f41,plain,(
% 1.61/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.61/1.01    inference(cnf_transformation,[],[f26])).
% 1.61/1.01  
% 1.61/1.01  fof(f6,axiom,(
% 1.61/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.61/1.01  
% 1.61/1.01  fof(f16,plain,(
% 1.61/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.61/1.01    inference(ennf_transformation,[],[f6])).
% 1.61/1.01  
% 1.61/1.01  fof(f37,plain,(
% 1.61/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.61/1.01    inference(cnf_transformation,[],[f16])).
% 1.61/1.01  
% 1.61/1.01  fof(f1,axiom,(
% 1.61/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.61/1.01  
% 1.61/1.01  fof(f22,plain,(
% 1.61/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.61/1.01    inference(nnf_transformation,[],[f1])).
% 1.61/1.01  
% 1.61/1.01  fof(f23,plain,(
% 1.61/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.61/1.01    inference(flattening,[],[f22])).
% 1.61/1.01  
% 1.61/1.01  fof(f29,plain,(
% 1.61/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.61/1.01    inference(cnf_transformation,[],[f23])).
% 1.61/1.01  
% 1.61/1.01  fof(f9,axiom,(
% 1.61/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 1.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.61/1.01  
% 1.61/1.01  fof(f19,plain,(
% 1.61/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.61/1.01    inference(ennf_transformation,[],[f9])).
% 1.61/1.01  
% 1.61/1.01  fof(f40,plain,(
% 1.61/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.61/1.01    inference(cnf_transformation,[],[f19])).
% 1.61/1.01  
% 1.61/1.01  fof(f43,plain,(
% 1.61/1.01    k2_relset_1(sK0,sK1,sK2) != sK1 | ~r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))),
% 1.61/1.01    inference(cnf_transformation,[],[f26])).
% 1.61/1.01  
% 1.61/1.01  fof(f8,axiom,(
% 1.61/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.61/1.01  
% 1.61/1.01  fof(f18,plain,(
% 1.61/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.61/1.01    inference(ennf_transformation,[],[f8])).
% 1.61/1.01  
% 1.61/1.01  fof(f39,plain,(
% 1.61/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.61/1.01    inference(cnf_transformation,[],[f18])).
% 1.61/1.01  
% 1.61/1.01  cnf(c_15,negated_conjecture,
% 1.61/1.01      ( r1_tarski(k6_relat_1(sK1),sK2) ),
% 1.61/1.01      inference(cnf_transformation,[],[f42]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_500,plain,
% 1.61/1.01      ( r1_tarski(k6_relat_1(sK1),sK2) = iProver_top ),
% 1.61/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_8,plain,
% 1.61/1.01      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 1.61/1.01      inference(cnf_transformation,[],[f36]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_6,plain,
% 1.61/1.01      ( ~ r1_tarski(X0,X1)
% 1.61/1.01      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 1.61/1.01      | ~ v1_relat_1(X1)
% 1.61/1.01      | ~ v1_relat_1(X0) ),
% 1.61/1.01      inference(cnf_transformation,[],[f34]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_503,plain,
% 1.61/1.01      ( r1_tarski(X0,X1) != iProver_top
% 1.61/1.01      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 1.61/1.01      | v1_relat_1(X0) != iProver_top
% 1.61/1.01      | v1_relat_1(X1) != iProver_top ),
% 1.61/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_1406,plain,
% 1.61/1.01      ( r1_tarski(X0,k2_relat_1(X1)) = iProver_top
% 1.61/1.01      | r1_tarski(k6_relat_1(X0),X1) != iProver_top
% 1.61/1.01      | v1_relat_1(X1) != iProver_top
% 1.61/1.01      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 1.61/1.01      inference(superposition,[status(thm)],[c_8,c_503]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_5,plain,
% 1.61/1.01      ( v1_relat_1(k6_relat_1(X0)) ),
% 1.61/1.01      inference(cnf_transformation,[],[f32]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_40,plain,
% 1.61/1.01      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 1.61/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_1763,plain,
% 1.61/1.01      ( v1_relat_1(X1) != iProver_top
% 1.61/1.01      | r1_tarski(k6_relat_1(X0),X1) != iProver_top
% 1.61/1.01      | r1_tarski(X0,k2_relat_1(X1)) = iProver_top ),
% 1.61/1.01      inference(global_propositional_subsumption,
% 1.61/1.01                [status(thm)],
% 1.61/1.01                [c_1406,c_40]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_1764,plain,
% 1.61/1.01      ( r1_tarski(X0,k2_relat_1(X1)) = iProver_top
% 1.61/1.01      | r1_tarski(k6_relat_1(X0),X1) != iProver_top
% 1.61/1.01      | v1_relat_1(X1) != iProver_top ),
% 1.61/1.01      inference(renaming,[status(thm)],[c_1763]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_1773,plain,
% 1.61/1.01      ( r1_tarski(sK1,k2_relat_1(sK2)) = iProver_top
% 1.61/1.01      | v1_relat_1(sK2) != iProver_top ),
% 1.61/1.01      inference(superposition,[status(thm)],[c_500,c_1764]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_9,plain,
% 1.61/1.01      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 1.61/1.01      inference(cnf_transformation,[],[f35]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_7,plain,
% 1.61/1.01      ( ~ r1_tarski(X0,X1)
% 1.61/1.01      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 1.61/1.01      | ~ v1_relat_1(X1)
% 1.61/1.01      | ~ v1_relat_1(X0) ),
% 1.61/1.01      inference(cnf_transformation,[],[f33]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_502,plain,
% 1.61/1.01      ( r1_tarski(X0,X1) != iProver_top
% 1.61/1.01      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
% 1.61/1.01      | v1_relat_1(X0) != iProver_top
% 1.61/1.01      | v1_relat_1(X1) != iProver_top ),
% 1.61/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_1261,plain,
% 1.61/1.01      ( r1_tarski(X0,k1_relat_1(X1)) = iProver_top
% 1.61/1.01      | r1_tarski(k6_relat_1(X0),X1) != iProver_top
% 1.61/1.01      | v1_relat_1(X1) != iProver_top
% 1.61/1.01      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 1.61/1.01      inference(superposition,[status(thm)],[c_9,c_502]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_1445,plain,
% 1.61/1.01      ( v1_relat_1(X1) != iProver_top
% 1.61/1.01      | r1_tarski(k6_relat_1(X0),X1) != iProver_top
% 1.61/1.01      | r1_tarski(X0,k1_relat_1(X1)) = iProver_top ),
% 1.61/1.01      inference(global_propositional_subsumption,
% 1.61/1.01                [status(thm)],
% 1.61/1.01                [c_1261,c_40]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_1446,plain,
% 1.61/1.01      ( r1_tarski(X0,k1_relat_1(X1)) = iProver_top
% 1.61/1.01      | r1_tarski(k6_relat_1(X0),X1) != iProver_top
% 1.61/1.01      | v1_relat_1(X1) != iProver_top ),
% 1.61/1.01      inference(renaming,[status(thm)],[c_1445]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_1455,plain,
% 1.61/1.01      ( r1_tarski(sK1,k1_relat_1(sK2)) = iProver_top
% 1.61/1.01      | v1_relat_1(sK2) != iProver_top ),
% 1.61/1.01      inference(superposition,[status(thm)],[c_500,c_1446]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_4,plain,
% 1.61/1.01      ( ~ v5_relat_1(X0,X1)
% 1.61/1.01      | r1_tarski(k2_relat_1(X0),X1)
% 1.61/1.01      | ~ v1_relat_1(X0) ),
% 1.61/1.01      inference(cnf_transformation,[],[f30]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_11,plain,
% 1.61/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.61/1.01      | v5_relat_1(X0,X2) ),
% 1.61/1.01      inference(cnf_transformation,[],[f38]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_16,negated_conjecture,
% 1.61/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 1.61/1.01      inference(cnf_transformation,[],[f41]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_193,plain,
% 1.61/1.01      ( v5_relat_1(X0,X1)
% 1.61/1.01      | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.61/1.01      | sK2 != X0 ),
% 1.61/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_16]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_194,plain,
% 1.61/1.01      ( v5_relat_1(sK2,X0)
% 1.61/1.01      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 1.61/1.01      inference(unflattening,[status(thm)],[c_193]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_228,plain,
% 1.61/1.01      ( r1_tarski(k2_relat_1(X0),X1)
% 1.61/1.01      | ~ v1_relat_1(X0)
% 1.61/1.01      | X2 != X1
% 1.61/1.01      | k1_zfmisc_1(k2_zfmisc_1(X3,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.61/1.01      | sK2 != X0 ),
% 1.61/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_194]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_229,plain,
% 1.61/1.01      ( r1_tarski(k2_relat_1(sK2),X0)
% 1.61/1.01      | ~ v1_relat_1(sK2)
% 1.61/1.01      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 1.61/1.01      inference(unflattening,[status(thm)],[c_228]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_10,plain,
% 1.61/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.61/1.01      | v1_relat_1(X0) ),
% 1.61/1.01      inference(cnf_transformation,[],[f37]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_205,plain,
% 1.61/1.01      ( v1_relat_1(X0)
% 1.61/1.01      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.61/1.01      | sK2 != X0 ),
% 1.61/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_16]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_206,plain,
% 1.61/1.01      ( v1_relat_1(sK2)
% 1.61/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 1.61/1.01      inference(unflattening,[status(thm)],[c_205]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_239,plain,
% 1.61/1.01      ( r1_tarski(k2_relat_1(sK2),X0)
% 1.61/1.01      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 1.61/1.01      inference(forward_subsumption_resolution,
% 1.61/1.01                [status(thm)],
% 1.61/1.01                [c_229,c_206]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_498,plain,
% 1.61/1.01      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.61/1.01      | r1_tarski(k2_relat_1(sK2),X1) = iProver_top ),
% 1.61/1.01      inference(predicate_to_equality,[status(thm)],[c_239]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_888,plain,
% 1.61/1.01      ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
% 1.61/1.01      inference(equality_resolution,[status(thm)],[c_498]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_0,plain,
% 1.61/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 1.61/1.01      inference(cnf_transformation,[],[f29]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_506,plain,
% 1.61/1.01      ( X0 = X1
% 1.61/1.01      | r1_tarski(X0,X1) != iProver_top
% 1.61/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 1.61/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_1152,plain,
% 1.61/1.01      ( k2_relat_1(sK2) = sK1
% 1.61/1.01      | r1_tarski(sK1,k2_relat_1(sK2)) != iProver_top ),
% 1.61/1.01      inference(superposition,[status(thm)],[c_888,c_506]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_13,plain,
% 1.61/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.61/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 1.61/1.01      inference(cnf_transformation,[],[f40]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_175,plain,
% 1.61/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 1.61/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.61/1.01      | sK2 != X2 ),
% 1.61/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_16]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_176,plain,
% 1.61/1.01      ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
% 1.61/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 1.61/1.01      inference(unflattening,[status(thm)],[c_175]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_620,plain,
% 1.61/1.01      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 1.61/1.01      inference(equality_resolution,[status(thm)],[c_176]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_14,negated_conjecture,
% 1.61/1.01      ( ~ r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2))
% 1.61/1.01      | k2_relset_1(sK0,sK1,sK2) != sK1 ),
% 1.61/1.01      inference(cnf_transformation,[],[f43]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_501,plain,
% 1.61/1.01      ( k2_relset_1(sK0,sK1,sK2) != sK1
% 1.61/1.01      | r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) != iProver_top ),
% 1.61/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_697,plain,
% 1.61/1.01      ( k2_relat_1(sK2) != sK1
% 1.61/1.01      | r1_tarski(sK1,k1_relset_1(sK0,sK1,sK2)) != iProver_top ),
% 1.61/1.01      inference(demodulation,[status(thm)],[c_620,c_501]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_12,plain,
% 1.61/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.61/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.61/1.01      inference(cnf_transformation,[],[f39]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_184,plain,
% 1.61/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.61/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.61/1.01      | sK2 != X2 ),
% 1.61/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_16]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_185,plain,
% 1.61/1.01      ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
% 1.61/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 1.61/1.01      inference(unflattening,[status(thm)],[c_184]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_623,plain,
% 1.61/1.01      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 1.61/1.01      inference(equality_resolution,[status(thm)],[c_185]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_786,plain,
% 1.61/1.01      ( k2_relat_1(sK2) != sK1
% 1.61/1.01      | r1_tarski(sK1,k1_relat_1(sK2)) != iProver_top ),
% 1.61/1.01      inference(light_normalisation,[status(thm)],[c_697,c_623]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_587,plain,
% 1.61/1.01      ( v1_relat_1(sK2)
% 1.61/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 1.61/1.01      inference(instantiation,[status(thm)],[c_206]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_588,plain,
% 1.61/1.01      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.61/1.01      | v1_relat_1(sK2) = iProver_top ),
% 1.61/1.01      inference(predicate_to_equality,[status(thm)],[c_587]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_318,plain,( X0 = X0 ),theory(equality) ).
% 1.61/1.01  
% 1.61/1.01  cnf(c_584,plain,
% 1.61/1.01      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 1.61/1.01      inference(instantiation,[status(thm)],[c_318]) ).
% 1.61/1.01  
% 1.61/1.01  cnf(contradiction,plain,
% 1.61/1.01      ( $false ),
% 1.61/1.01      inference(minisat,
% 1.61/1.01                [status(thm)],
% 1.61/1.01                [c_1773,c_1455,c_1152,c_786,c_588,c_584]) ).
% 1.61/1.01  
% 1.61/1.01  
% 1.61/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.61/1.01  
% 1.61/1.01  ------                               Statistics
% 1.61/1.01  
% 1.61/1.01  ------ General
% 1.61/1.01  
% 1.61/1.01  abstr_ref_over_cycles:                  0
% 1.61/1.01  abstr_ref_under_cycles:                 0
% 1.61/1.01  gc_basic_clause_elim:                   0
% 1.61/1.01  forced_gc_time:                         0
% 1.61/1.01  parsing_time:                           0.011
% 1.61/1.01  unif_index_cands_time:                  0.
% 1.61/1.01  unif_index_add_time:                    0.
% 1.61/1.01  orderings_time:                         0.
% 1.61/1.01  out_proof_time:                         0.01
% 1.61/1.01  total_time:                             0.117
% 1.61/1.01  num_of_symbols:                         45
% 1.61/1.01  num_of_terms:                           1951
% 1.61/1.01  
% 1.61/1.01  ------ Preprocessing
% 1.61/1.01  
% 1.61/1.01  num_of_splits:                          0
% 1.61/1.01  num_of_split_atoms:                     0
% 1.61/1.01  num_of_reused_defs:                     0
% 1.61/1.01  num_eq_ax_congr_red:                    2
% 1.61/1.01  num_of_sem_filtered_clauses:            1
% 1.61/1.01  num_of_subtypes:                        0
% 1.61/1.01  monotx_restored_types:                  0
% 1.61/1.01  sat_num_of_epr_types:                   0
% 1.61/1.01  sat_num_of_non_cyclic_types:            0
% 1.61/1.01  sat_guarded_non_collapsed_types:        0
% 1.61/1.01  num_pure_diseq_elim:                    0
% 1.61/1.01  simp_replaced_by:                       0
% 1.61/1.01  res_preprocessed:                       78
% 1.61/1.01  prep_upred:                             0
% 1.61/1.01  prep_unflattend:                        6
% 1.61/1.01  smt_new_axioms:                         0
% 1.61/1.01  pred_elim_cands:                        2
% 1.61/1.01  pred_elim:                              2
% 1.61/1.01  pred_elim_cl:                           3
% 1.61/1.01  pred_elim_cycles:                       4
% 1.61/1.01  merged_defs:                            0
% 1.61/1.01  merged_defs_ncl:                        0
% 1.61/1.01  bin_hyper_res:                          0
% 1.61/1.01  prep_cycles:                            4
% 1.61/1.01  pred_elim_time:                         0.003
% 1.61/1.01  splitting_time:                         0.
% 1.61/1.01  sem_filter_time:                        0.
% 1.61/1.01  monotx_time:                            0.001
% 1.61/1.01  subtype_inf_time:                       0.
% 1.61/1.01  
% 1.61/1.01  ------ Problem properties
% 1.61/1.01  
% 1.61/1.01  clauses:                                13
% 1.61/1.01  conjectures:                            2
% 1.61/1.01  epr:                                    2
% 1.61/1.01  horn:                                   13
% 1.61/1.01  ground:                                 2
% 1.61/1.01  unary:                                  5
% 1.61/1.01  binary:                                 5
% 1.61/1.01  lits:                                   26
% 1.61/1.01  lits_eq:                                10
% 1.61/1.01  fd_pure:                                0
% 1.61/1.01  fd_pseudo:                              0
% 1.61/1.01  fd_cond:                                0
% 1.61/1.01  fd_pseudo_cond:                         1
% 1.61/1.01  ac_symbols:                             0
% 1.61/1.01  
% 1.61/1.01  ------ Propositional Solver
% 1.61/1.01  
% 1.61/1.01  prop_solver_calls:                      27
% 1.61/1.01  prop_fast_solver_calls:                 418
% 1.61/1.01  smt_solver_calls:                       0
% 1.61/1.01  smt_fast_solver_calls:                  0
% 1.61/1.01  prop_num_of_clauses:                    769
% 1.61/1.01  prop_preprocess_simplified:             2941
% 1.61/1.01  prop_fo_subsumed:                       4
% 1.61/1.01  prop_solver_time:                       0.
% 1.61/1.01  smt_solver_time:                        0.
% 1.61/1.01  smt_fast_solver_time:                   0.
% 1.61/1.01  prop_fast_solver_time:                  0.
% 1.61/1.01  prop_unsat_core_time:                   0.
% 1.61/1.01  
% 1.61/1.01  ------ QBF
% 1.61/1.01  
% 1.61/1.01  qbf_q_res:                              0
% 1.61/1.01  qbf_num_tautologies:                    0
% 1.61/1.01  qbf_prep_cycles:                        0
% 1.61/1.01  
% 1.61/1.01  ------ BMC1
% 1.61/1.01  
% 1.61/1.01  bmc1_current_bound:                     -1
% 1.61/1.01  bmc1_last_solved_bound:                 -1
% 1.61/1.01  bmc1_unsat_core_size:                   -1
% 1.61/1.01  bmc1_unsat_core_parents_size:           -1
% 1.61/1.01  bmc1_merge_next_fun:                    0
% 1.61/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.61/1.01  
% 1.61/1.01  ------ Instantiation
% 1.61/1.01  
% 1.61/1.01  inst_num_of_clauses:                    252
% 1.61/1.01  inst_num_in_passive:                    108
% 1.61/1.01  inst_num_in_active:                     114
% 1.61/1.01  inst_num_in_unprocessed:                30
% 1.61/1.01  inst_num_of_loops:                      120
% 1.61/1.01  inst_num_of_learning_restarts:          0
% 1.61/1.01  inst_num_moves_active_passive:          4
% 1.61/1.01  inst_lit_activity:                      0
% 1.61/1.01  inst_lit_activity_moves:                0
% 1.61/1.01  inst_num_tautologies:                   0
% 1.61/1.01  inst_num_prop_implied:                  0
% 1.61/1.01  inst_num_existing_simplified:           0
% 1.61/1.01  inst_num_eq_res_simplified:             0
% 1.61/1.01  inst_num_child_elim:                    0
% 1.61/1.01  inst_num_of_dismatching_blockings:      16
% 1.61/1.01  inst_num_of_non_proper_insts:           187
% 1.61/1.01  inst_num_of_duplicates:                 0
% 1.61/1.01  inst_inst_num_from_inst_to_res:         0
% 1.61/1.01  inst_dismatching_checking_time:         0.
% 1.61/1.01  
% 1.61/1.01  ------ Resolution
% 1.61/1.01  
% 1.61/1.01  res_num_of_clauses:                     0
% 1.61/1.01  res_num_in_passive:                     0
% 1.61/1.01  res_num_in_active:                      0
% 1.61/1.01  res_num_of_loops:                       82
% 1.61/1.01  res_forward_subset_subsumed:            25
% 1.61/1.01  res_backward_subset_subsumed:           0
% 1.61/1.01  res_forward_subsumed:                   0
% 1.61/1.01  res_backward_subsumed:                  0
% 1.61/1.01  res_forward_subsumption_resolution:     1
% 1.61/1.01  res_backward_subsumption_resolution:    0
% 1.61/1.01  res_clause_to_clause_subsumption:       88
% 1.61/1.01  res_orphan_elimination:                 0
% 1.61/1.01  res_tautology_del:                      21
% 1.61/1.01  res_num_eq_res_simplified:              0
% 1.61/1.01  res_num_sel_changes:                    0
% 1.61/1.01  res_moves_from_active_to_pass:          0
% 1.61/1.01  
% 1.61/1.01  ------ Superposition
% 1.61/1.01  
% 1.61/1.01  sup_time_total:                         0.
% 1.61/1.01  sup_time_generating:                    0.
% 1.61/1.01  sup_time_sim_full:                      0.
% 1.61/1.01  sup_time_sim_immed:                     0.
% 1.61/1.01  
% 1.61/1.01  sup_num_of_clauses:                     27
% 1.61/1.01  sup_num_in_active:                      22
% 1.61/1.01  sup_num_in_passive:                     5
% 1.61/1.01  sup_num_of_loops:                       22
% 1.61/1.01  sup_fw_superposition:                   12
% 1.61/1.01  sup_bw_superposition:                   3
% 1.61/1.01  sup_immediate_simplified:               3
% 1.61/1.01  sup_given_eliminated:                   0
% 1.61/1.01  comparisons_done:                       0
% 1.61/1.01  comparisons_avoided:                    0
% 1.61/1.01  
% 1.61/1.01  ------ Simplifications
% 1.61/1.01  
% 1.61/1.01  
% 1.61/1.01  sim_fw_subset_subsumed:                 0
% 1.61/1.01  sim_bw_subset_subsumed:                 0
% 1.61/1.01  sim_fw_subsumed:                        3
% 1.61/1.01  sim_bw_subsumed:                        0
% 1.61/1.01  sim_fw_subsumption_res:                 1
% 1.61/1.01  sim_bw_subsumption_res:                 0
% 1.61/1.01  sim_tautology_del:                      0
% 1.61/1.01  sim_eq_tautology_del:                   1
% 1.61/1.01  sim_eq_res_simp:                        0
% 1.61/1.01  sim_fw_demodulated:                     0
% 1.61/1.01  sim_bw_demodulated:                     1
% 1.61/1.01  sim_light_normalised:                   4
% 1.61/1.01  sim_joinable_taut:                      0
% 1.61/1.01  sim_joinable_simp:                      0
% 1.61/1.01  sim_ac_normalised:                      0
% 1.61/1.01  sim_smt_subsumption:                    0
% 1.61/1.01  
%------------------------------------------------------------------------------
