%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0421+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:39 EST 2020

% Result     : Theorem 18.76s
% Output     : CNFRefutation 18.76s
% Verified   : 
% Statistics : Number of formulae       :   41 (  97 expanded)
%              Number of clauses        :   20 (  27 expanded)
%              Number of leaves         :    5 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :  119 ( 353 expanded)
%              Number of equality atoms :   59 ( 168 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1086,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f1087,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f1086])).

fof(f1447,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1087])).

fof(f2861,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f1447])).

fof(f607,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = k7_setfam_1(X0,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f608,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( k7_setfam_1(X0,X1) = k7_setfam_1(X0,X2)
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f607])).

fof(f1012,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k7_setfam_1(X0,X1) = k7_setfam_1(X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f608])).

fof(f1013,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k7_setfam_1(X0,X1) = k7_setfam_1(X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f1012])).

fof(f1377,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k7_setfam_1(X0,X1) = k7_setfam_1(X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
     => ( sK119 != X1
        & k7_setfam_1(X0,sK119) = k7_setfam_1(X0,X1)
        & m1_subset_1(sK119,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f1376,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X1 != X2
            & k7_setfam_1(X0,X1) = k7_setfam_1(X0,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( sK118 != X2
          & k7_setfam_1(sK117,sK118) = k7_setfam_1(sK117,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK117))) )
      & m1_subset_1(sK118,k1_zfmisc_1(k1_zfmisc_1(sK117))) ) ),
    introduced(choice_axiom,[])).

fof(f1378,plain,
    ( sK118 != sK119
    & k7_setfam_1(sK117,sK118) = k7_setfam_1(sK117,sK119)
    & m1_subset_1(sK119,k1_zfmisc_1(k1_zfmisc_1(sK117)))
    & m1_subset_1(sK118,k1_zfmisc_1(k1_zfmisc_1(sK117))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK117,sK118,sK119])],[f1013,f1377,f1376])).

fof(f2346,plain,(
    k7_setfam_1(sK117,sK118) = k7_setfam_1(sK117,sK119) ),
    inference(cnf_transformation,[],[f1378])).

fof(f605,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1009,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ~ r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f605])).

fof(f1010,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ~ r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f1009])).

fof(f2341,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f1010])).

fof(f2345,plain,(
    m1_subset_1(sK119,k1_zfmisc_1(k1_zfmisc_1(sK117))) ),
    inference(cnf_transformation,[],[f1378])).

fof(f1449,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1087])).

fof(f2347,plain,(
    sK118 != sK119 ),
    inference(cnf_transformation,[],[f1378])).

fof(f2344,plain,(
    m1_subset_1(sK118,k1_zfmisc_1(k1_zfmisc_1(sK117))) ),
    inference(cnf_transformation,[],[f1378])).

cnf(c_69,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2861])).

cnf(c_41230,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_69])).

cnf(c_950,negated_conjecture,
    ( k7_setfam_1(sK117,sK118) = k7_setfam_1(sK117,sK119) ),
    inference(cnf_transformation,[],[f2346])).

cnf(c_946,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | r1_tarski(X2,X0)
    | ~ r1_tarski(k7_setfam_1(X1,X2),k7_setfam_1(X1,X0)) ),
    inference(cnf_transformation,[],[f2341])).

cnf(c_40710,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r1_tarski(X2,X0) = iProver_top
    | r1_tarski(k7_setfam_1(X1,X2),k7_setfam_1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_946])).

cnf(c_51850,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK117))) != iProver_top
    | m1_subset_1(sK119,k1_zfmisc_1(k1_zfmisc_1(sK117))) != iProver_top
    | r1_tarski(X0,sK119) = iProver_top
    | r1_tarski(k7_setfam_1(sK117,X0),k7_setfam_1(sK117,sK118)) != iProver_top ),
    inference(superposition,[status(thm)],[c_950,c_40710])).

cnf(c_951,negated_conjecture,
    ( m1_subset_1(sK119,k1_zfmisc_1(k1_zfmisc_1(sK117))) ),
    inference(cnf_transformation,[],[f2345])).

cnf(c_961,plain,
    ( m1_subset_1(sK119,k1_zfmisc_1(k1_zfmisc_1(sK117))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_951])).

cnf(c_52560,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK117))) != iProver_top
    | r1_tarski(X0,sK119) = iProver_top
    | r1_tarski(k7_setfam_1(sK117,X0),k7_setfam_1(sK117,sK118)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_51850,c_961])).

cnf(c_66414,plain,
    ( m1_subset_1(sK118,k1_zfmisc_1(k1_zfmisc_1(sK117))) != iProver_top
    | r1_tarski(sK118,sK119) = iProver_top ),
    inference(superposition,[status(thm)],[c_41230,c_52560])).

cnf(c_51849,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK117))) != iProver_top
    | m1_subset_1(sK119,k1_zfmisc_1(k1_zfmisc_1(sK117))) != iProver_top
    | r1_tarski(k7_setfam_1(sK117,sK118),k7_setfam_1(sK117,X0)) != iProver_top
    | r1_tarski(sK119,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_950,c_40710])).

cnf(c_52470,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK117))) != iProver_top
    | r1_tarski(k7_setfam_1(sK117,sK118),k7_setfam_1(sK117,X0)) != iProver_top
    | r1_tarski(sK119,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_51849,c_961])).

cnf(c_66410,plain,
    ( m1_subset_1(sK118,k1_zfmisc_1(k1_zfmisc_1(sK117))) != iProver_top
    | r1_tarski(sK119,sK118) = iProver_top ),
    inference(superposition,[status(thm)],[c_41230,c_52470])).

cnf(c_67,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f1449])).

cnf(c_47899,plain,
    ( ~ r1_tarski(sK119,sK118)
    | ~ r1_tarski(sK118,sK119)
    | sK118 = sK119 ),
    inference(instantiation,[status(thm)],[c_67])).

cnf(c_47900,plain,
    ( sK118 = sK119
    | r1_tarski(sK119,sK118) != iProver_top
    | r1_tarski(sK118,sK119) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47899])).

cnf(c_949,negated_conjecture,
    ( sK118 != sK119 ),
    inference(cnf_transformation,[],[f2347])).

cnf(c_952,negated_conjecture,
    ( m1_subset_1(sK118,k1_zfmisc_1(k1_zfmisc_1(sK117))) ),
    inference(cnf_transformation,[],[f2344])).

cnf(c_960,plain,
    ( m1_subset_1(sK118,k1_zfmisc_1(k1_zfmisc_1(sK117))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_952])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_66414,c_66410,c_47900,c_949,c_960])).

%------------------------------------------------------------------------------
