%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0390+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:38 EST 2020

% Result     : Theorem 15.07s
% Output     : CNFRefutation 15.07s
% Verified   : 
% Statistics : Number of formulae       :   25 (  37 expanded)
%              Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :    7
%              Number of atoms          :   59 ( 101 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f615,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f616,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f615])).

fof(f1363,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f616])).

fof(f554,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f917,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f554])).

fof(f2122,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f917])).

fof(f560,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f561,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X0,X2)
          & r2_hidden(X0,X1) )
       => r1_tarski(k1_setfam_1(X1),X2) ) ),
    inference(negated_conjecture,[],[f560])).

fof(f926,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k1_setfam_1(X1),X2)
      & r1_tarski(X0,X2)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f561])).

fof(f927,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k1_setfam_1(X1),X2)
      & r1_tarski(X0,X2)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f926])).

fof(f1242,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k1_setfam_1(X1),X2)
        & r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
   => ( ~ r1_tarski(k1_setfam_1(sK98),sK99)
      & r1_tarski(sK97,sK99)
      & r2_hidden(sK97,sK98) ) ),
    introduced(choice_axiom,[])).

fof(f1243,plain,
    ( ~ r1_tarski(k1_setfam_1(sK98),sK99)
    & r1_tarski(sK97,sK99)
    & r2_hidden(sK97,sK98) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK97,sK98,sK99])],[f927,f1242])).

fof(f2131,plain,(
    ~ r1_tarski(k1_setfam_1(sK98),sK99) ),
    inference(cnf_transformation,[],[f1243])).

fof(f2130,plain,(
    r1_tarski(sK97,sK99) ),
    inference(cnf_transformation,[],[f1243])).

fof(f2129,plain,(
    r2_hidden(sK97,sK98) ),
    inference(cnf_transformation,[],[f1243])).

cnf(c_119,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f1363])).

cnf(c_44118,plain,
    ( ~ r1_tarski(X0,sK99)
    | ~ r1_tarski(k1_setfam_1(sK98),X0)
    | r1_tarski(k1_setfam_1(sK98),sK99) ),
    inference(instantiation,[status(thm)],[c_119])).

cnf(c_49995,plain,
    ( ~ r1_tarski(k1_setfam_1(sK98),sK97)
    | r1_tarski(k1_setfam_1(sK98),sK99)
    | ~ r1_tarski(sK97,sK99) ),
    inference(instantiation,[status(thm)],[c_44118])).

cnf(c_864,plain,
    ( r1_tarski(k1_setfam_1(X0),X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f2122])).

cnf(c_43696,plain,
    ( r1_tarski(k1_setfam_1(sK98),sK97)
    | ~ r2_hidden(sK97,sK98) ),
    inference(instantiation,[status(thm)],[c_864])).

cnf(c_871,negated_conjecture,
    ( ~ r1_tarski(k1_setfam_1(sK98),sK99) ),
    inference(cnf_transformation,[],[f2131])).

cnf(c_872,negated_conjecture,
    ( r1_tarski(sK97,sK99) ),
    inference(cnf_transformation,[],[f2130])).

cnf(c_873,negated_conjecture,
    ( r2_hidden(sK97,sK98) ),
    inference(cnf_transformation,[],[f2129])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_49995,c_43696,c_871,c_872,c_873])).

%------------------------------------------------------------------------------
