%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0856+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:54 EST 2020

% Result     : Theorem 27.92s
% Output     : CNFRefutation 27.92s
% Verified   : 
% Statistics : Number of formulae       :   32 (  47 expanded)
%              Number of clauses        :   14 (  16 expanded)
%              Number of leaves         :    5 (  10 expanded)
%              Depth                    :    9
%              Number of atoms          :   99 ( 144 expanded)
%              Number of equality atoms :   46 (  59 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2744,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f175])).

fof(f2745,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f2744])).

fof(f2746,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK39(X0,X1) != X0
          | ~ r2_hidden(sK39(X0,X1),X1) )
        & ( sK39(X0,X1) = X0
          | r2_hidden(sK39(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2747,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK39(X0,X1) != X0
            | ~ r2_hidden(sK39(X0,X1),X1) )
          & ( sK39(X0,X1) = X0
            | r2_hidden(sK39(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK39])],[f2745,f2746])).

fof(f3882,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2747])).

fof(f6669,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f3882])).

fof(f1294,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1295,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
       => ( r2_hidden(k2_mcart_1(X0),X2)
          & k1_mcart_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f1294])).

fof(f2628,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(k2_mcart_1(X0),X2)
        | k1_mcart_1(X0) != X1 )
      & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f1295])).

fof(f3635,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(k2_mcart_1(X0),X2)
          | k1_mcart_1(X0) != X1 )
        & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) )
   => ( ( ~ r2_hidden(k2_mcart_1(sK375),sK377)
        | k1_mcart_1(sK375) != sK376 )
      & r2_hidden(sK375,k2_zfmisc_1(k1_tarski(sK376),sK377)) ) ),
    introduced(choice_axiom,[])).

fof(f3636,plain,
    ( ( ~ r2_hidden(k2_mcart_1(sK375),sK377)
      | k1_mcart_1(sK375) != sK376 )
    & r2_hidden(sK375,k2_zfmisc_1(k1_tarski(sK376),sK377)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK375,sK376,sK377])],[f2628,f3635])).

fof(f5916,plain,(
    r2_hidden(sK375,k2_zfmisc_1(k1_tarski(sK376),sK377)) ),
    inference(cnf_transformation,[],[f3636])).

fof(f1292,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2625,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f1292])).

fof(f5914,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f2625])).

fof(f5913,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f2625])).

fof(f5917,plain,
    ( ~ r2_hidden(k2_mcart_1(sK375),sK377)
    | k1_mcart_1(sK375) != sK376 ),
    inference(cnf_transformation,[],[f3636])).

cnf(c_232,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f6669])).

cnf(c_111395,plain,
    ( ~ r2_hidden(k1_mcart_1(sK375),k1_tarski(sK376))
    | k1_mcart_1(sK375) = sK376 ),
    inference(instantiation,[status(thm)],[c_232])).

cnf(c_2251,negated_conjecture,
    ( r2_hidden(sK375,k2_zfmisc_1(k1_tarski(sK376),sK377)) ),
    inference(cnf_transformation,[],[f5916])).

cnf(c_105612,plain,
    ( r2_hidden(sK375,k2_zfmisc_1(k1_tarski(sK376),sK377)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2251])).

cnf(c_2247,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f5914])).

cnf(c_105616,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2247])).

cnf(c_111217,plain,
    ( r2_hidden(k2_mcart_1(sK375),sK377) = iProver_top ),
    inference(superposition,[status(thm)],[c_105612,c_105616])).

cnf(c_2248,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f5913])).

cnf(c_105615,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2248])).

cnf(c_111178,plain,
    ( r2_hidden(k1_mcart_1(sK375),k1_tarski(sK376)) = iProver_top ),
    inference(superposition,[status(thm)],[c_105612,c_105615])).

cnf(c_111180,plain,
    ( r2_hidden(k1_mcart_1(sK375),k1_tarski(sK376)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_111178])).

cnf(c_2250,negated_conjecture,
    ( ~ r2_hidden(k2_mcart_1(sK375),sK377)
    | k1_mcart_1(sK375) != sK376 ),
    inference(cnf_transformation,[],[f5917])).

cnf(c_2271,plain,
    ( k1_mcart_1(sK375) != sK376
    | r2_hidden(k2_mcart_1(sK375),sK377) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2250])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_111395,c_111217,c_111180,c_2271])).

%------------------------------------------------------------------------------
