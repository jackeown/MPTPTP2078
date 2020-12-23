%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1085+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:00 EST 2020

% Result     : Theorem 41.17s
% Output     : CNFRefutation 41.17s
% Verified   : 
% Statistics : Number of formulae       :   33 (  47 expanded)
%              Number of clauses        :   14 (  14 expanded)
%              Number of leaves         :    5 (  10 expanded)
%              Depth                    :   10
%              Number of atoms          :   72 ( 116 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1711,conjecture,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & r1_tarski(X0,X1) )
     => v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1712,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_finset_1(X1)
          & r1_tarski(X0,X1) )
       => v1_finset_1(X0) ) ),
    inference(negated_conjecture,[],[f1711])).

fof(f3628,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(X0)
      & v1_finset_1(X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1712])).

fof(f3629,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(X0)
      & v1_finset_1(X1)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f3628])).

fof(f5070,plain,
    ( ? [X0,X1] :
        ( ~ v1_finset_1(X0)
        & v1_finset_1(X1)
        & r1_tarski(X0,X1) )
   => ( ~ v1_finset_1(sK601)
      & v1_finset_1(sK602)
      & r1_tarski(sK601,sK602) ) ),
    introduced(choice_axiom,[])).

fof(f5071,plain,
    ( ~ v1_finset_1(sK601)
    & v1_finset_1(sK602)
    & r1_tarski(sK601,sK602) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK601,sK602])],[f3629,f5070])).

fof(f8362,plain,(
    r1_tarski(sK601,sK602) ),
    inference(cnf_transformation,[],[f5071])).

fof(f1708,axiom,(
    ! [X0] :
      ( v1_finset_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_finset_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3626,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_finset_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f1708])).

fof(f8358,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f3626])).

fof(f1559,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8020,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f1559])).

fof(f10016,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X1)
      | ~ m1_subset_1(X1,k9_setfam_1(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(definition_unfolding,[],[f8358,f8020])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4046,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f6042,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4046])).

fof(f8964,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k9_setfam_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f6042,f8020])).

fof(f8364,plain,(
    ~ v1_finset_1(sK601) ),
    inference(cnf_transformation,[],[f5071])).

fof(f8363,plain,(
    v1_finset_1(sK602) ),
    inference(cnf_transformation,[],[f5071])).

cnf(c_3266,negated_conjecture,
    ( r1_tarski(sK601,sK602) ),
    inference(cnf_transformation,[],[f8362])).

cnf(c_94465,plain,
    ( r1_tarski(sK601,sK602) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3266])).

cnf(c_3260,plain,
    ( ~ m1_subset_1(X0,k9_setfam_1(X1))
    | ~ v1_finset_1(X1)
    | v1_finset_1(X0) ),
    inference(cnf_transformation,[],[f10016])).

cnf(c_955,plain,
    ( m1_subset_1(X0,k9_setfam_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8964])).

cnf(c_20245,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k9_setfam_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_955])).

cnf(c_20246,plain,
    ( m1_subset_1(X0,k9_setfam_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_20245])).

cnf(c_24396,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_finset_1(X1)
    | v1_finset_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_3260,c_20246])).

cnf(c_94426,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_finset_1(X1) != iProver_top
    | v1_finset_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24396])).

cnf(c_124093,plain,
    ( v1_finset_1(sK602) != iProver_top
    | v1_finset_1(sK601) = iProver_top ),
    inference(superposition,[status(thm)],[c_94465,c_94426])).

cnf(c_3264,negated_conjecture,
    ( ~ v1_finset_1(sK601) ),
    inference(cnf_transformation,[],[f8364])).

cnf(c_3269,plain,
    ( v1_finset_1(sK601) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3264])).

cnf(c_3265,negated_conjecture,
    ( v1_finset_1(sK602) ),
    inference(cnf_transformation,[],[f8363])).

cnf(c_3268,plain,
    ( v1_finset_1(sK602) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3265])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_124093,c_3269,c_3268])).

%------------------------------------------------------------------------------
