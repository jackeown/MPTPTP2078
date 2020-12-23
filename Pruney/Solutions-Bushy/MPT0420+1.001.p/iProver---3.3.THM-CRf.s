%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0420+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:15 EST 2020

% Result     : Theorem 1.38s
% Output     : CNFRefutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 141 expanded)
%              Number of clauses        :   34 (  49 expanded)
%              Number of leaves         :    6 (  30 expanded)
%              Depth                    :   15
%              Number of atoms          :  157 ( 582 expanded)
%              Number of equality atoms :   49 (  62 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(k7_setfam_1(X0,X1),X2)
          <=> r1_tarski(X1,k7_setfam_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(k7_setfam_1(X0,X1),X2)
            <=> r1_tarski(X1,k7_setfam_1(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(k7_setfam_1(X0,X1),X2)
          <~> r1_tarski(X1,k7_setfam_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,k7_setfam_1(X0,X2))
            | ~ r1_tarski(k7_setfam_1(X0,X1),X2) )
          & ( r1_tarski(X1,k7_setfam_1(X0,X2))
            | r1_tarski(k7_setfam_1(X0,X1),X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,k7_setfam_1(X0,X2))
            | ~ r1_tarski(k7_setfam_1(X0,X1),X2) )
          & ( r1_tarski(X1,k7_setfam_1(X0,X2))
            | r1_tarski(k7_setfam_1(X0,X1),X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f11])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,k7_setfam_1(X0,X2))
            | ~ r1_tarski(k7_setfam_1(X0,X1),X2) )
          & ( r1_tarski(X1,k7_setfam_1(X0,X2))
            | r1_tarski(k7_setfam_1(X0,X1),X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
     => ( ( ~ r1_tarski(X1,k7_setfam_1(X0,sK2))
          | ~ r1_tarski(k7_setfam_1(X0,X1),sK2) )
        & ( r1_tarski(X1,k7_setfam_1(X0,sK2))
          | r1_tarski(k7_setfam_1(X0,X1),sK2) )
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(X1,k7_setfam_1(X0,X2))
              | ~ r1_tarski(k7_setfam_1(X0,X1),X2) )
            & ( r1_tarski(X1,k7_setfam_1(X0,X2))
              | r1_tarski(k7_setfam_1(X0,X1),X2) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(sK1,k7_setfam_1(sK0,X2))
            | ~ r1_tarski(k7_setfam_1(sK0,sK1),X2) )
          & ( r1_tarski(sK1,k7_setfam_1(sK0,X2))
            | r1_tarski(k7_setfam_1(sK0,sK1),X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ( ~ r1_tarski(sK1,k7_setfam_1(sK0,sK2))
      | ~ r1_tarski(k7_setfam_1(sK0,sK1),sK2) )
    & ( r1_tarski(sK1,k7_setfam_1(sK0,sK2))
      | r1_tarski(k7_setfam_1(sK0,sK1),sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14,f13])).

fof(f20,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f19,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ~ r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ~ r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f8])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f22,plain,
    ( ~ r1_tarski(sK1,k7_setfam_1(sK0,sK2))
    | ~ r1_tarski(k7_setfam_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f21,plain,
    ( r1_tarski(sK1,k7_setfam_1(sK0,sK2))
    | r1_tarski(k7_setfam_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_5,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_100,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_321,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_100])).

cnf(c_6,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_99,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_322,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_99])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k7_setfam_1(X1,k7_setfam_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_104,plain,
    ( ~ m1_subset_1(X0_35,k1_zfmisc_1(k1_zfmisc_1(X0_36)))
    | k7_setfam_1(X0_36,k7_setfam_1(X0_36,X0_35)) = X0_35 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_317,plain,
    ( k7_setfam_1(X0_36,k7_setfam_1(X0_36,X0_35)) = X0_35
    | m1_subset_1(X0_35,k1_zfmisc_1(k1_zfmisc_1(X0_36))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_104])).

cnf(c_480,plain,
    ( k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_322,c_317])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k7_setfam_1(X2,X0),k7_setfam_1(X2,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_103,plain,
    ( r1_tarski(X0_35,X1_35)
    | ~ r1_tarski(k7_setfam_1(X0_36,X0_35),k7_setfam_1(X0_36,X1_35))
    | ~ m1_subset_1(X0_35,k1_zfmisc_1(k1_zfmisc_1(X0_36)))
    | ~ m1_subset_1(X1_35,k1_zfmisc_1(k1_zfmisc_1(X0_36))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_318,plain,
    ( r1_tarski(X0_35,X1_35) = iProver_top
    | r1_tarski(k7_setfam_1(X0_36,X0_35),k7_setfam_1(X0_36,X1_35)) != iProver_top
    | m1_subset_1(X1_35,k1_zfmisc_1(k1_zfmisc_1(X0_36))) != iProver_top
    | m1_subset_1(X0_35,k1_zfmisc_1(k1_zfmisc_1(X0_36))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_103])).

cnf(c_631,plain,
    ( r1_tarski(k7_setfam_1(sK0,sK1),X0_35) = iProver_top
    | r1_tarski(sK1,k7_setfam_1(sK0,X0_35)) != iProver_top
    | m1_subset_1(X0_35,k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top
    | m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_480,c_318])).

cnf(c_7,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_105,plain,
    ( ~ m1_subset_1(X0_35,k1_zfmisc_1(k1_zfmisc_1(X0_36)))
    | m1_subset_1(k7_setfam_1(X0_36,X0_35),k1_zfmisc_1(k1_zfmisc_1(X0_36))) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_117,plain,
    ( m1_subset_1(X0_35,k1_zfmisc_1(k1_zfmisc_1(X0_36))) != iProver_top
    | m1_subset_1(k7_setfam_1(X0_36,X0_35),k1_zfmisc_1(k1_zfmisc_1(X0_36))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_105])).

cnf(c_119,plain,
    ( m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_117])).

cnf(c_1026,plain,
    ( m1_subset_1(X0_35,k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top
    | r1_tarski(sK1,k7_setfam_1(sK0,X0_35)) != iProver_top
    | r1_tarski(k7_setfam_1(sK0,sK1),X0_35) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_631,c_7,c_119])).

cnf(c_1027,plain,
    ( r1_tarski(k7_setfam_1(sK0,sK1),X0_35) = iProver_top
    | r1_tarski(sK1,k7_setfam_1(sK0,X0_35)) != iProver_top
    | m1_subset_1(X0_35,k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1026])).

cnf(c_1035,plain,
    ( r1_tarski(k7_setfam_1(sK0,sK1),sK2) = iProver_top
    | r1_tarski(sK1,k7_setfam_1(sK0,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_321,c_1027])).

cnf(c_808,plain,
    ( m1_subset_1(k7_setfam_1(X0_36,sK2),k1_zfmisc_1(k1_zfmisc_1(X0_36)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X0_36))) ),
    inference(instantiation,[status(thm)],[c_105])).

cnf(c_809,plain,
    ( m1_subset_1(k7_setfam_1(X0_36,sK2),k1_zfmisc_1(k1_zfmisc_1(X0_36))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X0_36))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_808])).

cnf(c_811,plain,
    ( m1_subset_1(k7_setfam_1(sK0,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_809])).

cnf(c_479,plain,
    ( k7_setfam_1(sK0,k7_setfam_1(sK0,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_321,c_317])).

cnf(c_634,plain,
    ( r1_tarski(X0_35,k7_setfam_1(sK0,sK2)) = iProver_top
    | r1_tarski(k7_setfam_1(sK0,X0_35),sK2) != iProver_top
    | m1_subset_1(X0_35,k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top
    | m1_subset_1(k7_setfam_1(sK0,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_479,c_318])).

cnf(c_677,plain,
    ( r1_tarski(k7_setfam_1(sK0,sK1),sK2) != iProver_top
    | r1_tarski(sK1,k7_setfam_1(sK0,sK2)) = iProver_top
    | m1_subset_1(k7_setfam_1(sK0,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_634])).

cnf(c_3,negated_conjecture,
    ( ~ r1_tarski(k7_setfam_1(sK0,sK1),sK2)
    | ~ r1_tarski(sK1,k7_setfam_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_10,plain,
    ( r1_tarski(k7_setfam_1(sK0,sK1),sK2) != iProver_top
    | r1_tarski(sK1,k7_setfam_1(sK0,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4,negated_conjecture,
    ( r1_tarski(k7_setfam_1(sK0,sK1),sK2)
    | r1_tarski(sK1,k7_setfam_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_9,plain,
    ( r1_tarski(k7_setfam_1(sK0,sK1),sK2) = iProver_top
    | r1_tarski(sK1,k7_setfam_1(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_8,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1035,c_811,c_677,c_10,c_9,c_8,c_7])).


%------------------------------------------------------------------------------
