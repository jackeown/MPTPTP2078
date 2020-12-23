%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0250+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:30 EST 2020

% Result     : Theorem 7.80s
% Output     : CNFRefutation 7.80s
% Verified   : 
% Statistics : Number of formulae       :   30 (  46 expanded)
%              Number of clauses        :    9 (  11 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :    8
%              Number of atoms          :   44 (  67 expanded)
%              Number of equality atoms :   11 (  22 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f295,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f467,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f295])).

fof(f1033,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(cnf_transformation,[],[f467])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f856,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f796,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f1125,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f856,f796])).

fof(f1377,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k5_xboole_0(k5_xboole_0(k1_tarski(X0),X1),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),X1))),X1) ) ),
    inference(definition_unfolding,[],[f1033,f1125])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f853,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f645,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f346,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f347,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
       => r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f346])).

fof(f498,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f347])).

fof(f639,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) )
   => ( ~ r2_hidden(sK35,sK36)
      & r1_tarski(k2_xboole_0(k1_tarski(sK35),sK36),sK36) ) ),
    introduced(choice_axiom,[])).

fof(f640,plain,
    ( ~ r2_hidden(sK35,sK36)
    & r1_tarski(k2_xboole_0(k1_tarski(sK35),sK36),sK36) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK35,sK36])],[f498,f639])).

fof(f1120,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK35),sK36),sK36) ),
    inference(cnf_transformation,[],[f640])).

fof(f1438,plain,(
    r1_tarski(k5_xboole_0(k5_xboole_0(k1_tarski(sK35),sK36),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),sK36))),sK36) ),
    inference(definition_unfolding,[],[f1120,f1125])).

fof(f1121,plain,(
    ~ r2_hidden(sK35,sK36) ),
    inference(cnf_transformation,[],[f640])).

cnf(c_380,plain,
    ( ~ r1_tarski(k5_xboole_0(k5_xboole_0(k1_tarski(X0),X1),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),X1))),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f1377])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f853])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f645])).

cnf(c_8264,plain,
    ( ~ r1_tarski(k5_xboole_0(X0,k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),X0)))),X0)
    | r2_hidden(X1,X0) ),
    inference(theory_normalisation,[status(thm)],[c_380,c_211,c_7])).

cnf(c_14626,plain,
    ( ~ r1_tarski(k5_xboole_0(sK36,k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),sK36)))),sK36)
    | r2_hidden(sK35,sK36) ),
    inference(instantiation,[status(thm)],[c_8264])).

cnf(c_468,negated_conjecture,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(k1_tarski(sK35),sK36),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),sK36))),sK36) ),
    inference(cnf_transformation,[],[f1438])).

cnf(c_8230,negated_conjecture,
    ( r1_tarski(k5_xboole_0(sK36,k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),sK36)))),sK36) ),
    inference(theory_normalisation,[status(thm)],[c_468,c_211,c_7])).

cnf(c_467,negated_conjecture,
    ( ~ r2_hidden(sK35,sK36) ),
    inference(cnf_transformation,[],[f1121])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14626,c_8230,c_467])).

%------------------------------------------------------------------------------
