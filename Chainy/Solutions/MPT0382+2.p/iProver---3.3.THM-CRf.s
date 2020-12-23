%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0382+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:37 EST 2020

% Result     : Theorem 15.31s
% Output     : CNFRefutation 15.31s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 145 expanded)
%              Number of clauses        :   30 (  43 expanded)
%              Number of leaves         :    5 (  34 expanded)
%              Depth                    :   13
%              Number of atoms          :  151 ( 536 expanded)
%              Number of equality atoms :   81 ( 249 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f942,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f943,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f942])).

fof(f1247,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f943])).

fof(f2502,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f1247])).

fof(f535,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( k3_subset_1(X0,X1) = k3_subset_1(X0,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f536,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( k3_subset_1(X0,X1) = k3_subset_1(X0,X2)
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f535])).

fof(f874,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k3_subset_1(X0,X1) = k3_subset_1(X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f536])).

fof(f875,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k3_subset_1(X0,X1) = k3_subset_1(X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f874])).

fof(f1173,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k3_subset_1(X0,X1) = k3_subset_1(X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( sK89 != X1
        & k3_subset_1(X0,sK89) = k3_subset_1(X0,X1)
        & m1_subset_1(sK89,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1172,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X1 != X2
            & k3_subset_1(X0,X1) = k3_subset_1(X0,X2)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( sK88 != X2
          & k3_subset_1(sK87,sK88) = k3_subset_1(sK87,X2)
          & m1_subset_1(X2,k1_zfmisc_1(sK87)) )
      & m1_subset_1(sK88,k1_zfmisc_1(sK87)) ) ),
    introduced(choice_axiom,[])).

fof(f1174,plain,
    ( sK88 != sK89
    & k3_subset_1(sK87,sK88) = k3_subset_1(sK87,sK89)
    & m1_subset_1(sK89,k1_zfmisc_1(sK87))
    & m1_subset_1(sK88,k1_zfmisc_1(sK87)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK87,sK88,sK89])],[f875,f1173,f1172])).

fof(f2026,plain,(
    m1_subset_1(sK89,k1_zfmisc_1(sK87)) ),
    inference(cnf_transformation,[],[f1174])).

fof(f2027,plain,(
    k3_subset_1(sK87,sK88) = k3_subset_1(sK87,sK89) ),
    inference(cnf_transformation,[],[f1174])).

fof(f516,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f840,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f516])).

fof(f1155,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(X1,X2)
              | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f840])).

fof(f1998,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k3_subset_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1155])).

fof(f1997,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_xboole_0(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1155])).

fof(f2025,plain,(
    m1_subset_1(sK88,k1_zfmisc_1(sK87)) ),
    inference(cnf_transformation,[],[f1174])).

fof(f1249,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f943])).

fof(f2028,plain,(
    sK88 != sK89 ),
    inference(cnf_transformation,[],[f1174])).

cnf(c_69,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2502])).

cnf(c_36535,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_69])).

cnf(c_832,negated_conjecture,
    ( m1_subset_1(sK89,k1_zfmisc_1(sK87)) ),
    inference(cnf_transformation,[],[f2026])).

cnf(c_36026,plain,
    ( m1_subset_1(sK89,k1_zfmisc_1(sK87)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_832])).

cnf(c_831,negated_conjecture,
    ( k3_subset_1(sK87,sK88) = k3_subset_1(sK87,sK89) ),
    inference(cnf_transformation,[],[f2027])).

cnf(c_802,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_xboole_0(X2,k3_subset_1(X1,X0))
    | ~ r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f1998])).

cnf(c_36053,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_xboole_0(X2,k3_subset_1(X1,X0)) = iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_802])).

cnf(c_42715,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK87)) != iProver_top
    | m1_subset_1(sK89,k1_zfmisc_1(sK87)) != iProver_top
    | r1_xboole_0(X0,k3_subset_1(sK87,sK88)) = iProver_top
    | r1_tarski(X0,sK89) != iProver_top ),
    inference(superposition,[status(thm)],[c_831,c_36053])).

cnf(c_841,plain,
    ( m1_subset_1(sK89,k1_zfmisc_1(sK87)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_832])).

cnf(c_43211,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK87)) != iProver_top
    | r1_xboole_0(X0,k3_subset_1(sK87,sK88)) = iProver_top
    | r1_tarski(X0,sK89) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_42715,c_841])).

cnf(c_803,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,k3_subset_1(X1,X0))
    | r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f1997])).

cnf(c_36052,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_xboole_0(X2,k3_subset_1(X1,X0)) != iProver_top
    | r1_tarski(X2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_803])).

cnf(c_43220,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK87)) != iProver_top
    | m1_subset_1(sK88,k1_zfmisc_1(sK87)) != iProver_top
    | r1_tarski(X0,sK89) != iProver_top
    | r1_tarski(X0,sK88) = iProver_top ),
    inference(superposition,[status(thm)],[c_43211,c_36052])).

cnf(c_833,negated_conjecture,
    ( m1_subset_1(sK88,k1_zfmisc_1(sK87)) ),
    inference(cnf_transformation,[],[f2025])).

cnf(c_840,plain,
    ( m1_subset_1(sK88,k1_zfmisc_1(sK87)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_833])).

cnf(c_43356,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK87)) != iProver_top
    | r1_tarski(X0,sK89) != iProver_top
    | r1_tarski(X0,sK88) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_43220,c_840])).

cnf(c_43365,plain,
    ( r1_tarski(sK89,sK89) != iProver_top
    | r1_tarski(sK89,sK88) = iProver_top ),
    inference(superposition,[status(thm)],[c_36026,c_43356])).

cnf(c_43885,plain,
    ( r1_tarski(sK89,sK88) = iProver_top ),
    inference(superposition,[status(thm)],[c_36535,c_43365])).

cnf(c_36025,plain,
    ( m1_subset_1(sK88,k1_zfmisc_1(sK87)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_833])).

cnf(c_42222,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK87)) != iProver_top
    | m1_subset_1(sK89,k1_zfmisc_1(sK87)) != iProver_top
    | r1_xboole_0(X0,k3_subset_1(sK87,sK88)) != iProver_top
    | r1_tarski(X0,sK89) = iProver_top ),
    inference(superposition,[status(thm)],[c_831,c_36052])).

cnf(c_42451,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK87)) != iProver_top
    | r1_xboole_0(X0,k3_subset_1(sK87,sK88)) != iProver_top
    | r1_tarski(X0,sK89) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_42222,c_841])).

cnf(c_42717,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK87)) != iProver_top
    | m1_subset_1(sK88,k1_zfmisc_1(sK87)) != iProver_top
    | r1_tarski(X0,sK89) = iProver_top
    | r1_tarski(X0,sK88) != iProver_top ),
    inference(superposition,[status(thm)],[c_36053,c_42451])).

cnf(c_43234,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK87)) != iProver_top
    | r1_tarski(X0,sK89) = iProver_top
    | r1_tarski(X0,sK88) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_42717,c_840])).

cnf(c_43244,plain,
    ( r1_tarski(sK88,sK89) = iProver_top
    | r1_tarski(sK88,sK88) != iProver_top ),
    inference(superposition,[status(thm)],[c_36025,c_43234])).

cnf(c_43884,plain,
    ( r1_tarski(sK88,sK89) = iProver_top ),
    inference(superposition,[status(thm)],[c_36535,c_43244])).

cnf(c_67,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f1249])).

cnf(c_42108,plain,
    ( ~ r1_tarski(sK89,sK88)
    | ~ r1_tarski(sK88,sK89)
    | sK88 = sK89 ),
    inference(instantiation,[status(thm)],[c_67])).

cnf(c_42109,plain,
    ( sK88 = sK89
    | r1_tarski(sK89,sK88) != iProver_top
    | r1_tarski(sK88,sK89) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42108])).

cnf(c_830,negated_conjecture,
    ( sK88 != sK89 ),
    inference(cnf_transformation,[],[f2028])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_43885,c_43884,c_42109,c_830])).

%------------------------------------------------------------------------------
