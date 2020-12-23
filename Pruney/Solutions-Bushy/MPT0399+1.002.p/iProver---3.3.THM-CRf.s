%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0399+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:13 EST 2020

% Result     : Theorem 0.85s
% Output     : CNFRefutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 124 expanded)
%              Number of clauses        :   33 (  55 expanded)
%              Number of leaves         :   10 (  26 expanded)
%              Depth                    :   13
%              Number of atoms          :  134 ( 247 expanded)
%              Number of equality atoms :   47 (  80 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] : m1_subset_1(sK1(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f3,f19])).

fof(f25,plain,(
    ! [X0] : m1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] : ~ r2_hidden(X3,X1)
            & r2_hidden(X2,X0) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] : r2_hidden(X3,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f17,plain,(
    ! [X1] :
      ( ? [X3] : r2_hidden(X3,X1)
     => r2_hidden(sK0(X1),X1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(sK0(X1),X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f17])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X1),X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,conjecture,(
    ! [X0] :
      ( r1_setfam_1(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( r1_setfam_1(X0,k1_xboole_0)
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f16,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & r1_setfam_1(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & r1_setfam_1(X0,k1_xboole_0) )
   => ( k1_xboole_0 != sK2
      & r1_setfam_1(sK2,k1_xboole_0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( k1_xboole_0 != sK2
    & r1_setfam_1(sK2,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f21])).

fof(f29,plain,(
    r1_setfam_1(sK2,k1_xboole_0) ),
    inference(cnf_transformation,[],[f22])).

fof(f30,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_2,plain,
    ( m1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_97,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | X1 != X2
    | sK1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_3])).

cnf(c_98,plain,
    ( r2_hidden(sK1(X0),X0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_97])).

cnf(c_366,plain,
    ( r2_hidden(sK1(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_98])).

cnf(c_1,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_369,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_368,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_437,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_369,c_368])).

cnf(c_0,plain,
    ( ~ r1_setfam_1(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(sK0(X1),X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_7,negated_conjecture,
    ( r1_setfam_1(sK2,k1_xboole_0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_82,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(X2),X2)
    | sK2 != X1
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_7])).

cnf(c_83,plain,
    ( ~ r2_hidden(X0,sK2)
    | r2_hidden(sK0(k1_xboole_0),k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_82])).

cnf(c_367,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(sK0(k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_83])).

cnf(c_508,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(sK0(o_0_0_xboole_0),o_0_0_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_437,c_367])).

cnf(c_627,plain,
    ( r2_hidden(sK0(o_0_0_xboole_0),o_0_0_xboole_0) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_366,c_508])).

cnf(c_6,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_402,plain,
    ( ~ v1_xboole_0(sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_403,plain,
    ( k1_xboole_0 = sK2
    | v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_402])).

cnf(c_690,plain,
    ( r2_hidden(sK0(o_0_0_xboole_0),o_0_0_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_627,c_6,c_403])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_109,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X2)
    | k1_zfmisc_1(X2) != X3
    | sK1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_4])).

cnf(c_110,plain,
    ( ~ r2_hidden(X0,sK1(k1_zfmisc_1(X1)))
    | ~ v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_109])).

cnf(c_365,plain,
    ( r2_hidden(X0,sK1(k1_zfmisc_1(X1))) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_110])).

cnf(c_628,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK1(k1_zfmisc_1(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_366,c_365])).

cnf(c_507,plain,
    ( o_0_0_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_437,c_368])).

cnf(c_698,plain,
    ( sK1(k1_zfmisc_1(X0)) = o_0_0_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_628,c_507])).

cnf(c_762,plain,
    ( sK1(k1_zfmisc_1(o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_369,c_698])).

cnf(c_775,plain,
    ( r2_hidden(X0,o_0_0_xboole_0) != iProver_top
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_762,c_365])).

cnf(c_21,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_848,plain,
    ( r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_775,c_21])).

cnf(c_856,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_690,c_848])).


%------------------------------------------------------------------------------
