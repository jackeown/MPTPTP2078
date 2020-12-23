%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0352+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:04 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 212 expanded)
%              Number of clauses        :   40 (  78 expanded)
%              Number of leaves         :    8 (  46 expanded)
%              Depth                    :   17
%              Number of atoms          :  142 ( 643 expanded)
%              Number of equality atoms :   46 ( 120 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f16])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ( ~ r1_tarski(k3_subset_1(X0,sK2),k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,sK2) )
        & ( r1_tarski(k3_subset_1(X0,sK2),k3_subset_1(X0,X1))
          | r1_tarski(X1,sK2) )
        & m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | r1_tarski(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | ~ r1_tarski(sK1,X2) )
          & ( r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | r1_tarski(sK1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | ~ r1_tarski(sK1,sK2) )
    & ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | r1_tarski(sK1,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f19,f18])).

fof(f31,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k6_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f21,f25])).

fof(f2,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X2,X1),k6_subset_1(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f25,f25])).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f32,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_8,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_355,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_610,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) = iProver_top
    | r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_355])).

cnf(c_9,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_354,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_611,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_354])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k6_subset_1(X1,X0) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_361,plain,
    ( ~ m1_subset_1(X0_39,k1_zfmisc_1(X1_39))
    | k6_subset_1(X1_39,X0_39) = k3_subset_1(X1_39,X0_39) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_605,plain,
    ( k6_subset_1(X0_39,X1_39) = k3_subset_1(X0_39,X1_39)
    | m1_subset_1(X1_39,k1_zfmisc_1(X0_39)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_361])).

cnf(c_861,plain,
    ( k6_subset_1(sK0,sK2) = k3_subset_1(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_611,c_605])).

cnf(c_1,plain,
    ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_360,plain,
    ( m1_subset_1(k6_subset_1(X0_39,X1_39),k1_zfmisc_1(X0_39)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_606,plain,
    ( m1_subset_1(k6_subset_1(X0_39,X1_39),k1_zfmisc_1(X0_39)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_360])).

cnf(c_1115,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_861,c_606])).

cnf(c_1335,plain,
    ( k6_subset_1(sK0,k3_subset_1(sK0,sK2)) = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_1115,c_605])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_359,plain,
    ( ~ m1_subset_1(X0_39,k1_zfmisc_1(X1_39))
    | k3_subset_1(X1_39,k3_subset_1(X1_39,X0_39)) = X0_39 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_607,plain,
    ( k3_subset_1(X0_39,k3_subset_1(X0_39,X1_39)) = X1_39
    | m1_subset_1(X1_39,k1_zfmisc_1(X0_39)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_359])).

cnf(c_962,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_611,c_607])).

cnf(c_1337,plain,
    ( k6_subset_1(sK0,k3_subset_1(sK0,sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_1335,c_962])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k6_subset_1(X2,X1),k6_subset_1(X2,X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_358,plain,
    ( ~ r1_tarski(X0_39,X1_39)
    | r1_tarski(k6_subset_1(X2_39,X1_39),k6_subset_1(X2_39,X0_39)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_608,plain,
    ( r1_tarski(X0_39,X1_39) != iProver_top
    | r1_tarski(k6_subset_1(X2_39,X1_39),k6_subset_1(X2_39,X0_39)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_358])).

cnf(c_1343,plain,
    ( r1_tarski(k6_subset_1(sK0,X0_39),sK2) = iProver_top
    | r1_tarski(k3_subset_1(sK0,sK2),X0_39) != iProver_top ),
    inference(superposition,[status(thm)],[c_1337,c_608])).

cnf(c_2342,plain,
    ( r1_tarski(k6_subset_1(sK0,k3_subset_1(sK0,sK1)),sK2) = iProver_top
    | r1_tarski(sK1,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_610,c_1343])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_353,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_612,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_353])).

cnf(c_862,plain,
    ( k6_subset_1(sK0,sK1) = k3_subset_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_612,c_605])).

cnf(c_1136,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_862,c_606])).

cnf(c_1464,plain,
    ( k6_subset_1(sK0,k3_subset_1(sK0,sK1)) = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_1136,c_605])).

cnf(c_963,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_612,c_607])).

cnf(c_1466,plain,
    ( k6_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1464,c_963])).

cnf(c_2355,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2342,c_1466])).

cnf(c_1113,plain,
    ( r1_tarski(X0_39,sK2) != iProver_top
    | r1_tarski(k3_subset_1(sK0,sK2),k6_subset_1(sK0,X0_39)) = iProver_top ),
    inference(superposition,[status(thm)],[c_861,c_608])).

cnf(c_1821,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) = iProver_top
    | r1_tarski(sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_862,c_1113])).

cnf(c_7,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_14,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) != iProver_top
    | r1_tarski(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2199,plain,
    ( r1_tarski(sK1,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1821,c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2355,c_2199])).


%------------------------------------------------------------------------------
