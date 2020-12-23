%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0092+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:20 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   26 (  31 expanded)
%              Number of clauses        :   10 (  10 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    7
%              Number of atoms          :   52 (  64 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f123,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f449,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f123])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f145,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f329,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f145])).

fof(f105,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f197,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f105])).

fof(f198,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f197])).

fof(f428,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f198])).

fof(f131,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f132,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f131])).

fof(f225,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X2,X1))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f132])).

fof(f284,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,k4_xboole_0(X2,X1))
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK15,k4_xboole_0(sK17,sK16))
      & r1_tarski(sK15,sK16) ) ),
    introduced(choice_axiom,[])).

fof(f285,plain,
    ( ~ r1_xboole_0(sK15,k4_xboole_0(sK17,sK16))
    & r1_tarski(sK15,sK16) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16,sK17])],[f225,f284])).

fof(f459,plain,(
    ~ r1_xboole_0(sK15,k4_xboole_0(sK17,sK16)) ),
    inference(cnf_transformation,[],[f285])).

fof(f458,plain,(
    r1_tarski(sK15,sK16) ),
    inference(cnf_transformation,[],[f285])).

cnf(c_160,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f449])).

cnf(c_12586,plain,
    ( r1_xboole_0(k4_xboole_0(sK17,sK16),sK16) ),
    inference(instantiation,[status(thm)],[c_160])).

cnf(c_41,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f329])).

cnf(c_7528,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK17,sK16),sK16)
    | r1_xboole_0(sK16,k4_xboole_0(sK17,sK16)) ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_139,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | ~ r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f428])).

cnf(c_6328,plain,
    ( ~ r1_xboole_0(X0,k4_xboole_0(sK17,sK16))
    | r1_xboole_0(sK15,k4_xboole_0(sK17,sK16))
    | ~ r1_tarski(sK15,X0) ),
    inference(instantiation,[status(thm)],[c_139])).

cnf(c_7378,plain,
    ( ~ r1_xboole_0(sK16,k4_xboole_0(sK17,sK16))
    | r1_xboole_0(sK15,k4_xboole_0(sK17,sK16))
    | ~ r1_tarski(sK15,sK16) ),
    inference(instantiation,[status(thm)],[c_6328])).

cnf(c_169,negated_conjecture,
    ( ~ r1_xboole_0(sK15,k4_xboole_0(sK17,sK16)) ),
    inference(cnf_transformation,[],[f459])).

cnf(c_170,negated_conjecture,
    ( r1_tarski(sK15,sK16) ),
    inference(cnf_transformation,[],[f458])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12586,c_7528,c_7378,c_169,c_170])).

%------------------------------------------------------------------------------
