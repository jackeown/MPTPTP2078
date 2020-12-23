%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0307+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:34 EST 2020

% Result     : Theorem 33.71s
% Output     : CNFRefutation 33.71s
% Verified   : 
% Statistics : Number of formulae       :   31 (  45 expanded)
%              Number of clauses        :   14 (  14 expanded)
%              Number of leaves         :    4 (   9 expanded)
%              Depth                    :    8
%              Number of atoms          :   74 ( 122 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f326,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f550,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f326])).

fof(f1226,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f550])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f455,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f456,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f455])).

fof(f894,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f456])).

fof(f1225,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f550])).

fof(f327,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f328,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(negated_conjecture,[],[f327])).

fof(f551,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f328])).

fof(f552,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f551])).

fof(f742,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k2_zfmisc_1(sK44,sK46),k2_zfmisc_1(sK45,sK47))
      & r1_tarski(sK46,sK47)
      & r1_tarski(sK44,sK45) ) ),
    introduced(choice_axiom,[])).

fof(f743,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK44,sK46),k2_zfmisc_1(sK45,sK47))
    & r1_tarski(sK46,sK47)
    & r1_tarski(sK44,sK45) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK44,sK45,sK46,sK47])],[f552,f742])).

fof(f1229,plain,(
    ~ r1_tarski(k2_zfmisc_1(sK44,sK46),k2_zfmisc_1(sK45,sK47)) ),
    inference(cnf_transformation,[],[f743])).

fof(f1228,plain,(
    r1_tarski(sK46,sK47) ),
    inference(cnf_transformation,[],[f743])).

fof(f1227,plain,(
    r1_tarski(sK44,sK45) ),
    inference(cnf_transformation,[],[f743])).

cnf(c_438,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f1226])).

cnf(c_36086,plain,
    ( ~ r1_tarski(X0,sK47)
    | r1_tarski(k2_zfmisc_1(sK45,X0),k2_zfmisc_1(sK45,sK47)) ),
    inference(instantiation,[status(thm)],[c_438])).

cnf(c_95539,plain,
    ( r1_tarski(k2_zfmisc_1(sK45,sK46),k2_zfmisc_1(sK45,sK47))
    | ~ r1_tarski(sK46,sK47) ),
    inference(instantiation,[status(thm)],[c_36086])).

cnf(c_119,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f894])).

cnf(c_20171,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(sK45,sK47))
    | ~ r1_tarski(k2_zfmisc_1(sK44,sK46),X0)
    | r1_tarski(k2_zfmisc_1(sK44,sK46),k2_zfmisc_1(sK45,sK47)) ),
    inference(instantiation,[status(thm)],[c_119])).

cnf(c_36085,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK45,X0),k2_zfmisc_1(sK45,sK47))
    | ~ r1_tarski(k2_zfmisc_1(sK44,sK46),k2_zfmisc_1(sK45,X0))
    | r1_tarski(k2_zfmisc_1(sK44,sK46),k2_zfmisc_1(sK45,sK47)) ),
    inference(instantiation,[status(thm)],[c_20171])).

cnf(c_54799,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK45,sK46),k2_zfmisc_1(sK45,sK47))
    | r1_tarski(k2_zfmisc_1(sK44,sK46),k2_zfmisc_1(sK45,sK47))
    | ~ r1_tarski(k2_zfmisc_1(sK44,sK46),k2_zfmisc_1(sK45,sK46)) ),
    inference(instantiation,[status(thm)],[c_36085])).

cnf(c_439,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f1225])).

cnf(c_25084,plain,
    ( r1_tarski(k2_zfmisc_1(sK44,sK46),k2_zfmisc_1(X0,sK46))
    | ~ r1_tarski(sK44,X0) ),
    inference(instantiation,[status(thm)],[c_439])).

cnf(c_39650,plain,
    ( r1_tarski(k2_zfmisc_1(sK44,sK46),k2_zfmisc_1(sK45,sK46))
    | ~ r1_tarski(sK44,sK45) ),
    inference(instantiation,[status(thm)],[c_25084])).

cnf(c_440,negated_conjecture,
    ( ~ r1_tarski(k2_zfmisc_1(sK44,sK46),k2_zfmisc_1(sK45,sK47)) ),
    inference(cnf_transformation,[],[f1229])).

cnf(c_441,negated_conjecture,
    ( r1_tarski(sK46,sK47) ),
    inference(cnf_transformation,[],[f1228])).

cnf(c_442,negated_conjecture,
    ( r1_tarski(sK44,sK45) ),
    inference(cnf_transformation,[],[f1227])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_95539,c_54799,c_39650,c_440,c_441,c_442])).

%------------------------------------------------------------------------------
