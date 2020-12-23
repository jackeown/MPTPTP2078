%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0063+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:16 EST 2020

% Result     : Theorem 1.52s
% Output     : CNFRefutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   27 (  39 expanded)
%              Number of clauses        :   10 (  10 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :    7
%              Number of atoms          :   72 ( 114 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f191,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f192,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f191])).

fof(f254,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f192])).

fof(f42,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f127,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r2_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f128,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r2_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f127])).

fof(f296,plain,(
    ! [X2,X0,X1] :
      ( r2_xboole_0(X0,X2)
      | ~ r2_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f128])).

fof(f97,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_xboole_0(X1,X2)
        & r2_xboole_0(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f98,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_xboole_0(X1,X2)
          & r2_xboole_0(X0,X1) )
       => r2_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f97])).

fof(f159,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r2_xboole_0(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f98])).

fof(f160,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r2_xboole_0(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(flattening,[],[f159])).

fof(f220,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_xboole_0(X0,X2)
        & r2_xboole_0(X1,X2)
        & r2_xboole_0(X0,X1) )
   => ( ~ r2_xboole_0(sK15,sK17)
      & r2_xboole_0(sK16,sK17)
      & r2_xboole_0(sK15,sK16) ) ),
    introduced(choice_axiom,[])).

fof(f221,plain,
    ( ~ r2_xboole_0(sK15,sK17)
    & r2_xboole_0(sK16,sK17)
    & r2_xboole_0(sK15,sK16) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16,sK17])],[f160,f220])).

fof(f358,plain,(
    ~ r2_xboole_0(sK15,sK17) ),
    inference(cnf_transformation,[],[f221])).

fof(f357,plain,(
    r2_xboole_0(sK16,sK17) ),
    inference(cnf_transformation,[],[f221])).

fof(f356,plain,(
    r2_xboole_0(sK15,sK16) ),
    inference(cnf_transformation,[],[f221])).

cnf(c_32,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f254])).

cnf(c_5277,plain,
    ( r1_tarski(X0,sK16)
    | ~ r2_xboole_0(X0,sK16) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_8662,plain,
    ( r1_tarski(sK15,sK16)
    | ~ r2_xboole_0(sK15,sK16) ),
    inference(instantiation,[status(thm)],[c_5277])).

cnf(c_72,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_xboole_0(X1,X2)
    | r2_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f296])).

cnf(c_4906,plain,
    ( ~ r1_tarski(X0,sK16)
    | r2_xboole_0(X0,sK17)
    | ~ r2_xboole_0(sK16,sK17) ),
    inference(instantiation,[status(thm)],[c_72])).

cnf(c_5954,plain,
    ( ~ r1_tarski(sK15,sK16)
    | ~ r2_xboole_0(sK16,sK17)
    | r2_xboole_0(sK15,sK17) ),
    inference(instantiation,[status(thm)],[c_4906])).

cnf(c_131,negated_conjecture,
    ( ~ r2_xboole_0(sK15,sK17) ),
    inference(cnf_transformation,[],[f358])).

cnf(c_132,negated_conjecture,
    ( r2_xboole_0(sK16,sK17) ),
    inference(cnf_transformation,[],[f357])).

cnf(c_133,negated_conjecture,
    ( r2_xboole_0(sK15,sK16) ),
    inference(cnf_transformation,[],[f356])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8662,c_5954,c_131,c_132,c_133])).

%------------------------------------------------------------------------------
