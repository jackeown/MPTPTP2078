%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0391+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:38 EST 2020

% Result     : Theorem 23.27s
% Output     : CNFRefutation 23.27s
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
fof(f129,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f644,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f129])).

fof(f645,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f644])).

fof(f1421,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f645])).

fof(f554,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f918,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f554])).

fof(f2125,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f918])).

fof(f561,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_xboole_0(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f562,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r2_hidden(X0,X1) )
       => r1_xboole_0(k1_setfam_1(X1),X2) ) ),
    inference(negated_conjecture,[],[f561])).

fof(f929,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k1_setfam_1(X1),X2)
      & r1_xboole_0(X0,X2)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f562])).

fof(f930,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k1_setfam_1(X1),X2)
      & r1_xboole_0(X0,X2)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f929])).

fof(f1245,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k1_setfam_1(X1),X2)
        & r1_xboole_0(X0,X2)
        & r2_hidden(X0,X1) )
   => ( ~ r1_xboole_0(k1_setfam_1(sK98),sK99)
      & r1_xboole_0(sK97,sK99)
      & r2_hidden(sK97,sK98) ) ),
    introduced(choice_axiom,[])).

fof(f1246,plain,
    ( ~ r1_xboole_0(k1_setfam_1(sK98),sK99)
    & r1_xboole_0(sK97,sK99)
    & r2_hidden(sK97,sK98) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK97,sK98,sK99])],[f930,f1245])).

fof(f2135,plain,(
    ~ r1_xboole_0(k1_setfam_1(sK98),sK99) ),
    inference(cnf_transformation,[],[f1246])).

fof(f2134,plain,(
    r1_xboole_0(sK97,sK99) ),
    inference(cnf_transformation,[],[f1246])).

fof(f2133,plain,(
    r2_hidden(sK97,sK98) ),
    inference(cnf_transformation,[],[f1246])).

cnf(c_173,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | ~ r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f1421])).

cnf(c_29225,plain,
    ( ~ r1_xboole_0(X0,sK99)
    | r1_xboole_0(k1_setfam_1(sK98),sK99)
    | ~ r1_tarski(k1_setfam_1(sK98),X0) ),
    inference(instantiation,[status(thm)],[c_173])).

cnf(c_36153,plain,
    ( r1_xboole_0(k1_setfam_1(sK98),sK99)
    | ~ r1_xboole_0(sK97,sK99)
    | ~ r1_tarski(k1_setfam_1(sK98),sK97) ),
    inference(instantiation,[status(thm)],[c_29225])).

cnf(c_864,plain,
    ( r1_tarski(k1_setfam_1(X0),X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f2125])).

cnf(c_28753,plain,
    ( r1_tarski(k1_setfam_1(sK98),sK97)
    | ~ r2_hidden(sK97,sK98) ),
    inference(instantiation,[status(thm)],[c_864])).

cnf(c_872,negated_conjecture,
    ( ~ r1_xboole_0(k1_setfam_1(sK98),sK99) ),
    inference(cnf_transformation,[],[f2135])).

cnf(c_873,negated_conjecture,
    ( r1_xboole_0(sK97,sK99) ),
    inference(cnf_transformation,[],[f2134])).

cnf(c_874,negated_conjecture,
    ( r2_hidden(sK97,sK98) ),
    inference(cnf_transformation,[],[f2133])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_36153,c_28753,c_872,c_873,c_874])).

%------------------------------------------------------------------------------
