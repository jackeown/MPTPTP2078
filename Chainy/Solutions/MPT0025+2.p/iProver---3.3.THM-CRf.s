%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0025+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:12 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   23 (  28 expanded)
%              Number of clauses        :   10 (  10 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    8
%              Number of atoms          :   46 (  58 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f47,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f232,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f47])).

fof(f51,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f96,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f51])).

fof(f97,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f96])).

fof(f236,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f48,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k3_xboole_0(X1,X2))
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f48])).

fof(f95,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f49])).

fof(f152,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_tarski(X0,k3_xboole_0(X1,X2)) )
   => ( ~ r1_tarski(sK14,sK15)
      & r1_tarski(sK14,k3_xboole_0(sK15,sK16)) ) ),
    introduced(choice_axiom,[])).

fof(f153,plain,
    ( ~ r1_tarski(sK14,sK15)
    & r1_tarski(sK14,k3_xboole_0(sK15,sK16)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14,sK15,sK16])],[f95,f152])).

fof(f234,plain,(
    ~ r1_tarski(sK14,sK15) ),
    inference(cnf_transformation,[],[f153])).

fof(f233,plain,(
    r1_tarski(sK14,k3_xboole_0(sK15,sK16)) ),
    inference(cnf_transformation,[],[f153])).

cnf(c_76,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f232])).

cnf(c_3773,plain,
    ( r1_tarski(k3_xboole_0(sK15,X0),sK15) ),
    inference(instantiation,[status(thm)],[c_76])).

cnf(c_5654,plain,
    ( r1_tarski(k3_xboole_0(sK15,sK16),sK15) ),
    inference(instantiation,[status(thm)],[c_3773])).

cnf(c_80,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f236])).

cnf(c_3567,plain,
    ( ~ r1_tarski(X0,sK15)
    | ~ r1_tarski(sK14,X0)
    | r1_tarski(sK14,sK15) ),
    inference(instantiation,[status(thm)],[c_80])).

cnf(c_3772,plain,
    ( ~ r1_tarski(k3_xboole_0(sK15,X0),sK15)
    | ~ r1_tarski(sK14,k3_xboole_0(sK15,X0))
    | r1_tarski(sK14,sK15) ),
    inference(instantiation,[status(thm)],[c_3567])).

cnf(c_4404,plain,
    ( ~ r1_tarski(k3_xboole_0(sK15,sK16),sK15)
    | ~ r1_tarski(sK14,k3_xboole_0(sK15,sK16))
    | r1_tarski(sK14,sK15) ),
    inference(instantiation,[status(thm)],[c_3772])).

cnf(c_77,negated_conjecture,
    ( ~ r1_tarski(sK14,sK15) ),
    inference(cnf_transformation,[],[f234])).

cnf(c_78,negated_conjecture,
    ( r1_tarski(sK14,k3_xboole_0(sK15,sK16)) ),
    inference(cnf_transformation,[],[f233])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5654,c_4404,c_77,c_78])).

%------------------------------------------------------------------------------
