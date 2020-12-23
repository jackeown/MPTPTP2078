%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0857+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:54 EST 2020

% Result     : Theorem 30.34s
% Output     : CNFRefutation 30.34s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2746,plain,(
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

fof(f2747,plain,(
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
    inference(rectify,[],[f2746])).

fof(f2748,plain,(
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

fof(f2749,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK39])],[f2747,f2748])).

fof(f3884,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2749])).

fof(f6673,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f3884])).

fof(f1295,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
     => ( k2_mcart_1(X0) = X2
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1296,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
       => ( k2_mcart_1(X0) = X2
          & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f1295])).

fof(f2630,plain,(
    ? [X0,X1,X2] :
      ( ( k2_mcart_1(X0) != X2
        | ~ r2_hidden(k1_mcart_1(X0),X1) )
      & r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) ) ),
    inference(ennf_transformation,[],[f1296])).

fof(f3637,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_mcart_1(X0) != X2
          | ~ r2_hidden(k1_mcart_1(X0),X1) )
        & r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) )
   => ( ( k2_mcart_1(sK375) != sK377
        | ~ r2_hidden(k1_mcart_1(sK375),sK376) )
      & r2_hidden(sK375,k2_zfmisc_1(sK376,k1_tarski(sK377))) ) ),
    introduced(choice_axiom,[])).

fof(f3638,plain,
    ( ( k2_mcart_1(sK375) != sK377
      | ~ r2_hidden(k1_mcart_1(sK375),sK376) )
    & r2_hidden(sK375,k2_zfmisc_1(sK376,k1_tarski(sK377))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK375,sK376,sK377])],[f2630,f3637])).

fof(f5920,plain,(
    r2_hidden(sK375,k2_zfmisc_1(sK376,k1_tarski(sK377))) ),
    inference(cnf_transformation,[],[f3638])).

fof(f1292,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2626,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f1292])).

fof(f5916,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f2626])).

fof(f5915,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f2626])).

fof(f5921,plain,
    ( k2_mcart_1(sK375) != sK377
    | ~ r2_hidden(k1_mcart_1(sK375),sK376) ),
    inference(cnf_transformation,[],[f3638])).

cnf(c_232,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f6673])).

cnf(c_100566,plain,
    ( ~ r2_hidden(k2_mcart_1(sK375),k1_tarski(sK377))
    | k2_mcart_1(sK375) = sK377 ),
    inference(instantiation,[status(thm)],[c_232])).

cnf(c_2253,negated_conjecture,
    ( r2_hidden(sK375,k2_zfmisc_1(sK376,k1_tarski(sK377))) ),
    inference(cnf_transformation,[],[f5920])).

cnf(c_64902,plain,
    ( r2_hidden(sK375,k2_zfmisc_1(sK376,k1_tarski(sK377))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2253])).

cnf(c_2247,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f5916])).

cnf(c_64908,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2247])).

cnf(c_84228,plain,
    ( r2_hidden(k2_mcart_1(sK375),k1_tarski(sK377)) = iProver_top ),
    inference(superposition,[status(thm)],[c_64902,c_64908])).

cnf(c_84237,plain,
    ( r2_hidden(k2_mcart_1(sK375),k1_tarski(sK377)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_84228])).

cnf(c_2248,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f5915])).

cnf(c_64907,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2248])).

cnf(c_83851,plain,
    ( r2_hidden(k1_mcart_1(sK375),sK376) = iProver_top ),
    inference(superposition,[status(thm)],[c_64902,c_64907])).

cnf(c_2252,negated_conjecture,
    ( ~ r2_hidden(k1_mcart_1(sK375),sK376)
    | k2_mcart_1(sK375) != sK377 ),
    inference(cnf_transformation,[],[f5921])).

cnf(c_2273,plain,
    ( k2_mcart_1(sK375) != sK377
    | r2_hidden(k1_mcart_1(sK375),sK376) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2252])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_100566,c_84237,c_83851,c_2273])).

%------------------------------------------------------------------------------
