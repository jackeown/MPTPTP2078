%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0278+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:33 EST 2020

% Result     : Theorem 22.88s
% Output     : CNFRefutation 22.88s
% Verified   : 
% Statistics : Number of formulae       :   42 (  58 expanded)
%              Number of clauses        :   14 (  14 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :    8
%              Number of atoms          :  137 ( 218 expanded)
%              Number of equality atoms :    9 (  16 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f284,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f646,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f284])).

fof(f647,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f646])).

fof(f648,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK24(X0,X1),X0)
          | ~ r2_hidden(sK24(X0,X1),X1) )
        & ( r1_tarski(sK24(X0,X1),X0)
          | r2_hidden(sK24(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f649,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK24(X0,X1),X0)
            | ~ r2_hidden(sK24(X0,X1),X1) )
          & ( r1_tarski(sK24(X0,X1),X0)
            | r2_hidden(sK24(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK24])],[f647,f648])).

fof(f1071,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f649])).

fof(f1633,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f1071])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f424,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f425,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f424])).

fof(f821,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f425])).

fof(f1072,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f649])).

fof(f1632,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f1072])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f387,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f560,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f387])).

fof(f561,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f560])).

fof(f562,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f563,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f561,f562])).

fof(f711,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f563])).

fof(f712,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f563])).

fof(f375,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f376,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    inference(negated_conjecture,[],[f375])).

fof(f547,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f376])).

fof(f700,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k1_zfmisc_1(sK35),k1_zfmisc_1(sK36))
      & r1_tarski(sK35,sK36) ) ),
    introduced(choice_axiom,[])).

fof(f701,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK35),k1_zfmisc_1(sK36))
    & r1_tarski(sK35,sK36) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK35,sK36])],[f547,f700])).

fof(f1228,plain,(
    ~ r1_tarski(k1_zfmisc_1(sK35),k1_zfmisc_1(sK36)) ),
    inference(cnf_transformation,[],[f701])).

fof(f1227,plain,(
    r1_tarski(sK35,sK36) ),
    inference(cnf_transformation,[],[f701])).

cnf(c_360,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f1633])).

cnf(c_101610,plain,
    ( r1_tarski(sK5(k1_zfmisc_1(sK35),k1_zfmisc_1(sK36)),sK35)
    | ~ r2_hidden(sK5(k1_zfmisc_1(sK35),k1_zfmisc_1(sK36)),k1_zfmisc_1(sK35)) ),
    inference(instantiation,[status(thm)],[c_360])).

cnf(c_119,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f821])).

cnf(c_29407,plain,
    ( ~ r1_tarski(X0,sK36)
    | ~ r1_tarski(sK5(k1_zfmisc_1(sK35),k1_zfmisc_1(sK36)),X0)
    | r1_tarski(sK5(k1_zfmisc_1(sK35),k1_zfmisc_1(sK36)),sK36) ),
    inference(instantiation,[status(thm)],[c_119])).

cnf(c_80390,plain,
    ( r1_tarski(sK5(k1_zfmisc_1(sK35),k1_zfmisc_1(sK36)),sK36)
    | ~ r1_tarski(sK5(k1_zfmisc_1(sK35),k1_zfmisc_1(sK36)),sK35)
    | ~ r1_tarski(sK35,sK36) ),
    inference(instantiation,[status(thm)],[c_29407])).

cnf(c_359,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f1632])).

cnf(c_21301,plain,
    ( ~ r1_tarski(sK5(k1_zfmisc_1(sK35),k1_zfmisc_1(sK36)),sK36)
    | r2_hidden(sK5(k1_zfmisc_1(sK35),k1_zfmisc_1(sK36)),k1_zfmisc_1(sK36)) ),
    inference(instantiation,[status(thm)],[c_359])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK5(X0,X1),X0) ),
    inference(cnf_transformation,[],[f711])).

cnf(c_17973,plain,
    ( r1_tarski(k1_zfmisc_1(sK35),k1_zfmisc_1(sK36))
    | r2_hidden(sK5(k1_zfmisc_1(sK35),k1_zfmisc_1(sK36)),k1_zfmisc_1(sK35)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK5(X0,X1),X1) ),
    inference(cnf_transformation,[],[f712])).

cnf(c_17965,plain,
    ( r1_tarski(k1_zfmisc_1(sK35),k1_zfmisc_1(sK36))
    | ~ r2_hidden(sK5(k1_zfmisc_1(sK35),k1_zfmisc_1(sK36)),k1_zfmisc_1(sK36)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_513,negated_conjecture,
    ( ~ r1_tarski(k1_zfmisc_1(sK35),k1_zfmisc_1(sK36)) ),
    inference(cnf_transformation,[],[f1228])).

cnf(c_514,negated_conjecture,
    ( r1_tarski(sK35,sK36) ),
    inference(cnf_transformation,[],[f1227])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_101610,c_80390,c_21301,c_17973,c_17965,c_513,c_514])).

%------------------------------------------------------------------------------
