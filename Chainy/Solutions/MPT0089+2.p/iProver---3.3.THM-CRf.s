%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0089+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:20 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   17 (  17 expanded)
%              Number of clauses        :    6 (   6 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    6
%              Number of atoms          :   23 (  23 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f123,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f444,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f123])).

fof(f126,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f219,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f126])).

fof(f447,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f219])).

fof(f128,conjecture,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f129,negated_conjecture,(
    ~ ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(negated_conjecture,[],[f128])).

fof(f221,plain,(
    ? [X0,X1] : ~ r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(ennf_transformation,[],[f129])).

fof(f279,plain,
    ( ? [X0,X1] : ~ r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))
   => ~ r1_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15)) ),
    introduced(choice_axiom,[])).

fof(f280,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16])],[f221,f279])).

fof(f449,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15)) ),
    inference(cnf_transformation,[],[f280])).

cnf(c_160,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f444])).

cnf(c_6720,plain,
    ( r1_xboole_0(k4_xboole_0(sK15,sK16),sK16) ),
    inference(instantiation,[status(thm)],[c_160])).

cnf(c_163,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f447])).

cnf(c_6033,plain,
    ( r1_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15))
    | ~ r1_xboole_0(k4_xboole_0(sK15,sK16),sK16) ),
    inference(instantiation,[status(thm)],[c_163])).

cnf(c_165,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(sK15,sK16),k4_xboole_0(sK16,sK15)) ),
    inference(cnf_transformation,[],[f449])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6720,c_6033,c_165])).

%------------------------------------------------------------------------------
