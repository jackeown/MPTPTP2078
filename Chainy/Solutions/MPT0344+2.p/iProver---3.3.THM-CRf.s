%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0344+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:36 EST 2020

% Result     : Theorem 11.62s
% Output     : CNFRefutation 11.62s
% Verified   : 
% Statistics : Number of formulae       :   45 (  68 expanded)
%              Number of clauses        :   19 (  19 expanded)
%              Number of leaves         :    7 (  16 expanded)
%              Depth                    :   12
%              Number of atoms          :  126 ( 218 expanded)
%              Number of equality atoms :   42 (  62 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f463,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1607,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f463])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f938,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f2030,plain,(
    ! [X0] : m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f1607,f938])).

fof(f464,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f709,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f464])).

fof(f710,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f709])).

fof(f925,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK68(X0,X1,X2),X2)
        & r2_hidden(sK68(X0,X1,X2),X1)
        & m1_subset_1(sK68(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f926,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK68(X0,X1,X2),X2)
            & r2_hidden(sK68(X0,X1,X2),X1)
            & m1_subset_1(sK68(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK68])],[f710,f925])).

fof(f1609,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | r2_hidden(sK68(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f926])).

fof(f1608,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | m1_subset_1(sK68(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f926])).

fof(f461,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f462,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ~ ( ! [X2] :
                ( m1_subset_1(X2,X0)
               => ~ r2_hidden(X2,X1) )
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f461])).

fof(f707,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f462])).

fof(f708,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f707])).

fof(f923,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,X0) )
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ! [X2] :
          ( ~ r2_hidden(X2,sK67)
          | ~ m1_subset_1(X2,sK66) )
      & k1_xboole_0 != sK67
      & m1_subset_1(sK67,k1_zfmisc_1(sK66)) ) ),
    introduced(choice_axiom,[])).

fof(f924,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK67)
        | ~ m1_subset_1(X2,sK66) )
    & k1_xboole_0 != sK67
    & m1_subset_1(sK67,k1_zfmisc_1(sK66)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK66,sK67])],[f708,f923])).

fof(f1606,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK67)
      | ~ m1_subset_1(X2,sK66) ) ),
    inference(cnf_transformation,[],[f924])).

fof(f1604,plain,(
    m1_subset_1(sK67,k1_zfmisc_1(sK66)) ),
    inference(cnf_transformation,[],[f924])).

fof(f101,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f533,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f101])).

fof(f1077,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f533])).

fof(f1711,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ r1_tarski(X0,o_0_0_xboole_0) ) ),
    inference(definition_unfolding,[],[f1077,f938,f938])).

fof(f1605,plain,(
    k1_xboole_0 != sK67 ),
    inference(cnf_transformation,[],[f924])).

fof(f2029,plain,(
    o_0_0_xboole_0 != sK67 ),
    inference(definition_unfolding,[],[f1605,f938])).

cnf(c_663,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2030])).

cnf(c_15502,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_663])).

cnf(c_665,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_tarski(X0,X2)
    | r2_hidden(sK68(X1,X0,X2),X0) ),
    inference(cnf_transformation,[],[f1609])).

cnf(c_15491,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | r2_hidden(sK68(X1,X0,X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_665])).

cnf(c_666,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(sK68(X1,X0,X2),X1)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f1608])).

cnf(c_15490,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(sK68(X1,X0,X2),X1) = iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_666])).

cnf(c_660,negated_conjecture,
    ( ~ m1_subset_1(X0,sK66)
    | ~ r2_hidden(X0,sK67) ),
    inference(cnf_transformation,[],[f1606])).

cnf(c_15494,plain,
    ( m1_subset_1(X0,sK66) != iProver_top
    | r2_hidden(X0,sK67) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_660])).

cnf(c_26796,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK66)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(sK66)) != iProver_top
    | r1_tarski(X1,X0) = iProver_top
    | r2_hidden(sK68(sK66,X1,X0),sK67) != iProver_top ),
    inference(superposition,[status(thm)],[c_15490,c_15494])).

cnf(c_31040,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK66)) != iProver_top
    | m1_subset_1(sK67,k1_zfmisc_1(sK66)) != iProver_top
    | r1_tarski(sK67,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_15491,c_26796])).

cnf(c_662,negated_conjecture,
    ( m1_subset_1(sK67,k1_zfmisc_1(sK66)) ),
    inference(cnf_transformation,[],[f1604])).

cnf(c_670,plain,
    ( m1_subset_1(sK67,k1_zfmisc_1(sK66)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_662])).

cnf(c_32008,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK66)) != iProver_top
    | r1_tarski(sK67,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_31040,c_670])).

cnf(c_32016,plain,
    ( r1_tarski(sK67,o_0_0_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_15502,c_32008])).

cnf(c_146,plain,
    ( ~ r1_tarski(X0,o_0_0_xboole_0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f1711])).

cnf(c_19565,plain,
    ( ~ r1_tarski(sK67,o_0_0_xboole_0)
    | o_0_0_xboole_0 = sK67 ),
    inference(instantiation,[status(thm)],[c_146])).

cnf(c_19566,plain,
    ( o_0_0_xboole_0 = sK67
    | r1_tarski(sK67,o_0_0_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19565])).

cnf(c_661,negated_conjecture,
    ( o_0_0_xboole_0 != sK67 ),
    inference(cnf_transformation,[],[f2029])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_32016,c_19566,c_661])).

%------------------------------------------------------------------------------
