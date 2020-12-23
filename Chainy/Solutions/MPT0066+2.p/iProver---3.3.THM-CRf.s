%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0066+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:17 EST 2020

% Result     : Theorem 1.48s
% Output     : CNFRefutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   20 (  32 expanded)
%              Number of clauses        :    7 (   7 expanded)
%              Number of leaves         :    3 (   7 expanded)
%              Depth                    :    7
%              Number of atoms          :   49 (  91 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f42,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f130,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r2_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f131,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r2_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f130])).

fof(f304,plain,(
    ! [X2,X0,X1] :
      ( r2_xboole_0(X0,X2)
      | ~ r2_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f131])).

fof(f100,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f101,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_xboole_0(X1,X2)
          & r1_tarski(X0,X1) )
       => r2_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f100])).

fof(f167,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r2_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f101])).

fof(f168,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r2_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f167])).

fof(f228,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_xboole_0(X0,X2)
        & r2_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r2_xboole_0(sK15,sK17)
      & r2_xboole_0(sK16,sK17)
      & r1_tarski(sK15,sK16) ) ),
    introduced(choice_axiom,[])).

fof(f229,plain,
    ( ~ r2_xboole_0(sK15,sK17)
    & r2_xboole_0(sK16,sK17)
    & r1_tarski(sK15,sK16) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16,sK17])],[f168,f228])).

fof(f369,plain,(
    ~ r2_xboole_0(sK15,sK17) ),
    inference(cnf_transformation,[],[f229])).

fof(f368,plain,(
    r2_xboole_0(sK16,sK17) ),
    inference(cnf_transformation,[],[f229])).

fof(f367,plain,(
    r1_tarski(sK15,sK16) ),
    inference(cnf_transformation,[],[f229])).

cnf(c_72,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_xboole_0(X1,X2)
    | r2_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f304])).

cnf(c_4990,plain,
    ( ~ r1_tarski(X0,sK16)
    | r2_xboole_0(X0,sK17)
    | ~ r2_xboole_0(sK16,sK17) ),
    inference(instantiation,[status(thm)],[c_72])).

cnf(c_5469,plain,
    ( ~ r1_tarski(sK15,sK16)
    | ~ r2_xboole_0(sK16,sK17)
    | r2_xboole_0(sK15,sK17) ),
    inference(instantiation,[status(thm)],[c_4990])).

cnf(c_134,negated_conjecture,
    ( ~ r2_xboole_0(sK15,sK17) ),
    inference(cnf_transformation,[],[f369])).

cnf(c_135,negated_conjecture,
    ( r2_xboole_0(sK16,sK17) ),
    inference(cnf_transformation,[],[f368])).

cnf(c_136,negated_conjecture,
    ( r1_tarski(sK15,sK16) ),
    inference(cnf_transformation,[],[f367])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5469,c_134,c_135,c_136])).

%------------------------------------------------------------------------------
