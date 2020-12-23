%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0858+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:55 EST 2020

% Result     : Theorem 27.25s
% Output     : CNFRefutation 27.25s
% Verified   : 
% Statistics : Number of formulae       :   29 (  34 expanded)
%              Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    6 (   8 expanded)
%              Depth                    :    8
%              Number of atoms          :   99 ( 117 expanded)
%              Number of equality atoms :   50 (  62 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1295,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
     => ( k2_mcart_1(X0) = X2
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2631,plain,(
    ! [X0,X1,X2] :
      ( ( k2_mcart_1(X0) = X2
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) ) ),
    inference(ennf_transformation,[],[f1295])).

fof(f5923,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) = X2
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f2631])).

fof(f1292,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2627,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f1292])).

fof(f5917,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f2627])).

fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2748,plain,(
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

fof(f2749,plain,(
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
    inference(rectify,[],[f2748])).

fof(f2750,plain,(
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

fof(f2751,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK39])],[f2749,f2750])).

fof(f3886,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2751])).

fof(f6677,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f3886])).

fof(f1296,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)))
     => ( k2_mcart_1(X0) = X2
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1297,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)))
       => ( k2_mcart_1(X0) = X2
          & k1_mcart_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f1296])).

fof(f2632,plain,(
    ? [X0,X1,X2] :
      ( ( k2_mcart_1(X0) != X2
        | k1_mcart_1(X0) != X1 )
      & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))) ) ),
    inference(ennf_transformation,[],[f1297])).

fof(f3639,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_mcart_1(X0) != X2
          | k1_mcart_1(X0) != X1 )
        & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))) )
   => ( ( k2_mcart_1(sK375) != sK377
        | k1_mcart_1(sK375) != sK376 )
      & r2_hidden(sK375,k2_zfmisc_1(k1_tarski(sK376),k1_tarski(sK377))) ) ),
    introduced(choice_axiom,[])).

fof(f3640,plain,
    ( ( k2_mcart_1(sK375) != sK377
      | k1_mcart_1(sK375) != sK376 )
    & r2_hidden(sK375,k2_zfmisc_1(k1_tarski(sK376),k1_tarski(sK377))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK375,sK376,sK377])],[f2632,f3639])).

fof(f5925,plain,
    ( k2_mcart_1(sK375) != sK377
    | k1_mcart_1(sK375) != sK376 ),
    inference(cnf_transformation,[],[f3640])).

fof(f5924,plain,(
    r2_hidden(sK375,k2_zfmisc_1(k1_tarski(sK376),k1_tarski(sK377))) ),
    inference(cnf_transformation,[],[f3640])).

cnf(c_2252,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
    | k2_mcart_1(X0) = X2 ),
    inference(cnf_transformation,[],[f5923])).

cnf(c_89714,plain,
    ( ~ r2_hidden(sK375,k2_zfmisc_1(k1_tarski(sK376),k1_tarski(sK377)))
    | k2_mcart_1(sK375) = sK377 ),
    inference(instantiation,[status(thm)],[c_2252])).

cnf(c_2248,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f5917])).

cnf(c_89545,plain,
    ( r2_hidden(k1_mcart_1(sK375),k1_tarski(sK376))
    | ~ r2_hidden(sK375,k2_zfmisc_1(k1_tarski(sK376),k1_tarski(sK377))) ),
    inference(instantiation,[status(thm)],[c_2248])).

cnf(c_232,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f6677])).

cnf(c_84076,plain,
    ( ~ r2_hidden(k1_mcart_1(sK375),k1_tarski(sK376))
    | k1_mcart_1(sK375) = sK376 ),
    inference(instantiation,[status(thm)],[c_232])).

cnf(c_2254,negated_conjecture,
    ( k2_mcart_1(sK375) != sK377
    | k1_mcart_1(sK375) != sK376 ),
    inference(cnf_transformation,[],[f5925])).

cnf(c_2255,negated_conjecture,
    ( r2_hidden(sK375,k2_zfmisc_1(k1_tarski(sK376),k1_tarski(sK377))) ),
    inference(cnf_transformation,[],[f5924])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_89714,c_89545,c_84076,c_2254,c_2255])).

%------------------------------------------------------------------------------
