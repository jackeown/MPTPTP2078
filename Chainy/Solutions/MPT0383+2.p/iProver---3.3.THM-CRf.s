%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0383+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:37 EST 2020

% Result     : Theorem 19.86s
% Output     : CNFRefutation 19.86s
% Verified   : 
% Statistics : Number of formulae       :   49 (  92 expanded)
%              Number of clauses        :   27 (  33 expanded)
%              Number of leaves         :    6 (  20 expanded)
%              Depth                    :   11
%              Number of atoms          :  155 ( 361 expanded)
%              Number of equality atoms :   28 (  62 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f456,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f787,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f456])).

fof(f1105,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f787])).

fof(f1861,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1105])).

fof(f148,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f646,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f148])).

fof(f1381,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f646])).

fof(f537,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4] :
            ( m1_subset_1(X4,X0)
           => ! [X5] :
                ( m1_subset_1(X5,X1)
               => k4_tarski(X4,X5) != X3 ) )
        & r1_tarski(X2,k2_zfmisc_1(X0,X1))
        & r2_hidden(X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f538,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ! [X4] :
              ( m1_subset_1(X4,X0)
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => k4_tarski(X4,X5) != X3 ) )
          & r1_tarski(X2,k2_zfmisc_1(X0,X1))
          & r2_hidden(X3,X2) ) ),
    inference(negated_conjecture,[],[f537])).

fof(f880,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( k4_tarski(X4,X5) != X3
              | ~ m1_subset_1(X5,X1) )
          | ~ m1_subset_1(X4,X0) )
      & r1_tarski(X2,k2_zfmisc_1(X0,X1))
      & r2_hidden(X3,X2) ) ),
    inference(ennf_transformation,[],[f538])).

fof(f1177,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( ! [X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ m1_subset_1(X5,X1) )
            | ~ m1_subset_1(X4,X0) )
        & r1_tarski(X2,k2_zfmisc_1(X0,X1))
        & r2_hidden(X3,X2) )
   => ( ! [X4] :
          ( ! [X5] :
              ( k4_tarski(X4,X5) != sK90
              | ~ m1_subset_1(X5,sK88) )
          | ~ m1_subset_1(X4,sK87) )
      & r1_tarski(sK89,k2_zfmisc_1(sK87,sK88))
      & r2_hidden(sK90,sK89) ) ),
    introduced(choice_axiom,[])).

fof(f1178,plain,
    ( ! [X4] :
        ( ! [X5] :
            ( k4_tarski(X4,X5) != sK90
            | ~ m1_subset_1(X5,sK88) )
        | ~ m1_subset_1(X4,sK87) )
    & r1_tarski(sK89,k2_zfmisc_1(sK87,sK88))
    & r2_hidden(sK90,sK89) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK87,sK88,sK89,sK90])],[f880,f1177])).

fof(f2031,plain,(
    r2_hidden(sK90,sK89) ),
    inference(cnf_transformation,[],[f1178])).

fof(f2032,plain,(
    r1_tarski(sK89,k2_zfmisc_1(sK87,sK88)) ),
    inference(cnf_transformation,[],[f1178])).

fof(f322,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5] :
            ~ ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X3,X0)
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f686,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f322])).

fof(f1040,plain,(
    ! [X3,X2,X1] :
      ( ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
     => ( k4_tarski(sK53(X1,X2,X3),sK54(X1,X2,X3)) = X3
        & r2_hidden(sK54(X1,X2,X3),X2)
        & r2_hidden(sK53(X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f1041,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k4_tarski(sK53(X1,X2,X3),sK54(X1,X2,X3)) = X3
        & r2_hidden(sK54(X1,X2,X3),X2)
        & r2_hidden(sK53(X1,X2,X3),X1) )
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK53,sK54])],[f686,f1040])).

fof(f1633,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(sK53(X1,X2,X3),sK54(X1,X2,X3)) = X3
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f1041])).

fof(f2033,plain,(
    ! [X4,X5] :
      ( k4_tarski(X4,X5) != sK90
      | ~ m1_subset_1(X5,sK88)
      | ~ m1_subset_1(X4,sK87) ) ),
    inference(cnf_transformation,[],[f1178])).

fof(f1631,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK53(X1,X2,X3),X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f1041])).

fof(f1632,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK54(X1,X2,X3),X2)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f1041])).

cnf(c_665,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f1861])).

cnf(c_195,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f1381])).

cnf(c_3770,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_665,c_195])).

cnf(c_3771,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_3770])).

cnf(c_49321,plain,
    ( m1_subset_1(X0,sK87)
    | ~ r2_hidden(X0,sK87) ),
    inference(instantiation,[status(thm)],[c_3771])).

cnf(c_71471,plain,
    ( m1_subset_1(sK53(sK87,sK88,sK90),sK87)
    | ~ r2_hidden(sK53(sK87,sK88,sK90),sK87) ),
    inference(instantiation,[status(thm)],[c_49321])).

cnf(c_834,negated_conjecture,
    ( r2_hidden(sK90,sK89) ),
    inference(cnf_transformation,[],[f2031])).

cnf(c_36722,plain,
    ( r2_hidden(sK90,sK89) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_834])).

cnf(c_833,negated_conjecture,
    ( r1_tarski(sK89,k2_zfmisc_1(sK87,sK88)) ),
    inference(cnf_transformation,[],[f2032])).

cnf(c_36723,plain,
    ( r1_tarski(sK89,k2_zfmisc_1(sK87,sK88)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_833])).

cnf(c_434,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | ~ r2_hidden(X3,X0)
    | k4_tarski(sK53(X1,X2,X3),sK54(X1,X2,X3)) = X3 ),
    inference(cnf_transformation,[],[f1633])).

cnf(c_37013,plain,
    ( k4_tarski(sK53(X0,X1,X2),sK54(X0,X1,X2)) = X2
    | r1_tarski(X3,k2_zfmisc_1(X0,X1)) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_434])).

cnf(c_63389,plain,
    ( k4_tarski(sK53(sK87,sK88,X0),sK54(sK87,sK88,X0)) = X0
    | r2_hidden(X0,sK89) != iProver_top ),
    inference(superposition,[status(thm)],[c_36723,c_37013])).

cnf(c_64314,plain,
    ( k4_tarski(sK53(sK87,sK88,sK90),sK54(sK87,sK88,sK90)) = sK90 ),
    inference(superposition,[status(thm)],[c_36722,c_63389])).

cnf(c_832,negated_conjecture,
    ( ~ m1_subset_1(X0,sK87)
    | ~ m1_subset_1(X1,sK88)
    | k4_tarski(X0,X1) != sK90 ),
    inference(cnf_transformation,[],[f2033])).

cnf(c_36724,plain,
    ( k4_tarski(X0,X1) != sK90
    | m1_subset_1(X0,sK87) != iProver_top
    | m1_subset_1(X1,sK88) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_832])).

cnf(c_64674,plain,
    ( m1_subset_1(sK54(sK87,sK88,sK90),sK88) != iProver_top
    | m1_subset_1(sK53(sK87,sK88,sK90),sK87) != iProver_top ),
    inference(superposition,[status(thm)],[c_64314,c_36724])).

cnf(c_64726,plain,
    ( ~ m1_subset_1(sK54(sK87,sK88,sK90),sK88)
    | ~ m1_subset_1(sK53(sK87,sK88,sK90),sK87) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_64674])).

cnf(c_43050,plain,
    ( m1_subset_1(X0,sK88)
    | ~ r2_hidden(X0,sK88) ),
    inference(instantiation,[status(thm)],[c_3771])).

cnf(c_61212,plain,
    ( m1_subset_1(sK54(sK87,sK88,sK90),sK88)
    | ~ r2_hidden(sK54(sK87,sK88,sK90),sK88) ),
    inference(instantiation,[status(thm)],[c_43050])).

cnf(c_436,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | ~ r2_hidden(X3,X0)
    | r2_hidden(sK53(X1,X2,X3),X1) ),
    inference(cnf_transformation,[],[f1631])).

cnf(c_46826,plain,
    ( ~ r1_tarski(sK89,k2_zfmisc_1(X0,X1))
    | r2_hidden(sK53(X0,X1,sK90),X0)
    | ~ r2_hidden(sK90,sK89) ),
    inference(instantiation,[status(thm)],[c_436])).

cnf(c_51423,plain,
    ( ~ r1_tarski(sK89,k2_zfmisc_1(sK87,sK88))
    | r2_hidden(sK53(sK87,sK88,sK90),sK87)
    | ~ r2_hidden(sK90,sK89) ),
    inference(instantiation,[status(thm)],[c_46826])).

cnf(c_435,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | ~ r2_hidden(X3,X0)
    | r2_hidden(sK54(X1,X2,X3),X2) ),
    inference(cnf_transformation,[],[f1632])).

cnf(c_46766,plain,
    ( ~ r1_tarski(sK89,k2_zfmisc_1(X0,X1))
    | r2_hidden(sK54(X0,X1,sK90),X1)
    | ~ r2_hidden(sK90,sK89) ),
    inference(instantiation,[status(thm)],[c_435])).

cnf(c_51401,plain,
    ( ~ r1_tarski(sK89,k2_zfmisc_1(sK87,sK88))
    | r2_hidden(sK54(sK87,sK88,sK90),sK88)
    | ~ r2_hidden(sK90,sK89) ),
    inference(instantiation,[status(thm)],[c_46766])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_71471,c_64726,c_61212,c_51423,c_51401,c_833,c_834])).

%------------------------------------------------------------------------------
