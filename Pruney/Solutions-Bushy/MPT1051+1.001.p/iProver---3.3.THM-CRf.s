%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1051+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:46 EST 2020

% Result     : Theorem 0.92s
% Output     : CNFRefutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 217 expanded)
%              Number of clauses        :   41 (  59 expanded)
%              Number of leaves         :    8 (  55 expanded)
%              Depth                    :   18
%              Number of atoms          :  266 (1222 expanded)
%              Number of equality atoms :  118 ( 406 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3)
              & ! [X4] : k1_tarski(X4) != X1 )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X3) )
           => ( ( k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3)
                & ! [X4] : k1_tarski(X4) != X1 )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3)
          & ! [X4] : k1_tarski(X4) != X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3)
          & ! [X4] : k1_tarski(X4) != X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3)
          & ! [X4] : k1_tarski(X4) != X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
     => ( ~ r2_relset_1(X0,X1,X2,sK4)
        & k5_partfun1(X0,X1,sK4) = k5_partfun1(X0,X1,X2)
        & ! [X4] : k1_tarski(X4) != X1
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3)
            & ! [X4] : k1_tarski(X4) != X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK1,sK2,sK3,X3)
          & k5_partfun1(sK1,sK2,sK3) = k5_partfun1(sK1,sK2,X3)
          & ! [X4] : k1_tarski(X4) != sK2
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ~ r2_relset_1(sK1,sK2,sK3,sK4)
    & k5_partfun1(sK1,sK2,sK3) = k5_partfun1(sK1,sK2,sK4)
    & ! [X4] : k1_tarski(X4) != sK2
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f13,f20,f19])).

fof(f30,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f14])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f22])).

fof(f34,plain,(
    k5_partfun1(sK1,sK2,sK3) = k5_partfun1(sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( ! [X4] : k1_tarski(X4) != X1
              & r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)) )
           => r1_relset_1(X0,X1,X3,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_relset_1(X0,X1,X3,X2)
          | ? [X4] : k1_tarski(X4) = X1
          | ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_relset_1(X0,X1,X3,X2)
          | ? [X4] : k1_tarski(X4) = X1
          | ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f17,plain,(
    ! [X1] :
      ( ? [X4] : k1_tarski(X4) = X1
     => k1_tarski(sK0(X1)) = X1 ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_relset_1(X0,X1,X3,X2)
          | k1_tarski(sK0(X1)) = X1
          | ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f17])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_relset_1(X0,X1,X3,X2)
      | k1_tarski(sK0(X1)) = X1
      | ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_relset_1(X0,X1,X2,X3)
      <=> r1_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_relset_1(X0,X1,X2,X3)
      <=> r1_tarski(X2,X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r1_relset_1(X0,X1,X2,X3)
          | ~ r1_tarski(X2,X3) )
        & ( r1_tarski(X2,X3)
          | ~ r1_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X2,X3)
      | ~ r1_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f31,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f32,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f21])).

fof(f33,plain,(
    ! [X4] : k1_tarski(X4) != sK2 ),
    inference(cnf_transformation,[],[f21])).

fof(f29,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f24,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f8])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f35,plain,(
    ~ r2_relset_1(sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_418,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_421,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_8,negated_conjecture,
    ( k5_partfun1(sK1,sK2,sK3) = k5_partfun1(sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_6,plain,
    ( r1_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(k5_partfun1(X0,X1,X3),k5_partfun1(X0,X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k1_tarski(sK0(X1)) = X1 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_4,plain,
    ( ~ r1_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | r1_tarski(X2,X3) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_151,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(X3,X0)
    | ~ r1_tarski(k5_partfun1(X1,X2,X0),k5_partfun1(X1,X2,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_tarski(sK0(X2)) = X2 ),
    inference(resolution,[status(thm)],[c_6,c_4])).

cnf(c_415,plain,
    ( k1_tarski(sK0(X0)) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r1_tarski(X3,X1) = iProver_top
    | r1_tarski(k5_partfun1(X2,X0,X1),k5_partfun1(X2,X0,X3)) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_151])).

cnf(c_728,plain,
    ( k1_tarski(sK0(sK2)) = sK2
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | r1_tarski(X0,sK4) = iProver_top
    | r1_tarski(k5_partfun1(sK1,sK2,sK3),k5_partfun1(sK1,sK2,X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_415])).

cnf(c_11,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_16,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_17,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_865,plain,
    ( v1_funct_1(X0) != iProver_top
    | r1_tarski(k5_partfun1(sK1,sK2,sK3),k5_partfun1(sK1,sK2,X0)) != iProver_top
    | r1_tarski(X0,sK4) = iProver_top
    | k1_tarski(sK0(sK2)) = sK2
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_728,c_16,c_17])).

cnf(c_866,plain,
    ( k1_tarski(sK0(sK2)) = sK2
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | r1_tarski(X0,sK4) = iProver_top
    | r1_tarski(k5_partfun1(sK1,sK2,sK3),k5_partfun1(sK1,sK2,X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_865])).

cnf(c_9,negated_conjecture,
    ( k1_tarski(X0) != sK2 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_876,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | r1_tarski(X0,sK4) = iProver_top
    | r1_tarski(k5_partfun1(sK1,sK2,sK3),k5_partfun1(sK1,sK2,X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_866,c_9])).

cnf(c_880,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | r1_tarski(sK3,sK4) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_421,c_876])).

cnf(c_13,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_14,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_15,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_982,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_880,c_14,c_15])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_422,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_987,plain,
    ( sK4 = sK3
    | r1_tarski(sK4,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_982,c_422])).

cnf(c_729,plain,
    ( k1_tarski(sK0(sK2)) = sK2
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | r1_tarski(k5_partfun1(sK1,sK2,X0),k5_partfun1(sK1,sK2,sK3)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_415])).

cnf(c_894,plain,
    ( v1_funct_1(X0) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | r1_tarski(k5_partfun1(sK1,sK2,X0),k5_partfun1(sK1,sK2,sK3)) != iProver_top
    | k1_tarski(sK0(sK2)) = sK2
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_729,c_16,c_17])).

cnf(c_895,plain,
    ( k1_tarski(sK0(sK2)) = sK2
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | r1_tarski(k5_partfun1(sK1,sK2,X0),k5_partfun1(sK1,sK2,sK3)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_894])).

cnf(c_905,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | r1_tarski(k5_partfun1(sK1,sK2,X0),k5_partfun1(sK1,sK2,sK3)) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_895,c_9])).

cnf(c_909,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | r1_tarski(sK4,sK3) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_421,c_905])).

cnf(c_1058,plain,
    ( sK4 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_987,c_14,c_15,c_909])).

cnf(c_5,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_7,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_130,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK4 != X0
    | sK3 != X0
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_7])).

cnf(c_131,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | sK3 != sK4 ),
    inference(unflattening,[status(thm)],[c_130])).

cnf(c_135,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | sK3 != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_131,c_10])).

cnf(c_416,plain,
    ( sK3 != sK4
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_135])).

cnf(c_1065,plain,
    ( sK3 != sK3
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1058,c_416])).

cnf(c_1069,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1065])).

cnf(c_1078,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_418,c_1069])).


%------------------------------------------------------------------------------
