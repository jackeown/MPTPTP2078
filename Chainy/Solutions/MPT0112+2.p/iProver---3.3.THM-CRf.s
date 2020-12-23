%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0112+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:22 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   37 (  46 expanded)
%              Number of clauses        :   14 (  14 expanded)
%              Number of leaves         :    8 (  12 expanded)
%              Depth                    :    9
%              Number of atoms          :   50 (  66 expanded)
%              Number of equality atoms :   28 (  38 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f53,conjecture,(
    ! [X0,X1] :
      ~ ( k1_xboole_0 = k4_xboole_0(X1,X0)
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_xboole_0 = k4_xboole_0(X1,X0)
          & r2_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f53])).

fof(f187,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X1,X0)
      & r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f54])).

fof(f318,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(X1,X0)
        & r2_xboole_0(X0,X1) )
   => ( k1_xboole_0 = k4_xboole_0(sK14,sK13)
      & r2_xboole_0(sK13,sK14) ) ),
    introduced(choice_axiom,[])).

fof(f319,plain,
    ( k1_xboole_0 = k4_xboole_0(sK14,sK13)
    & r2_xboole_0(sK13,sK14) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14])],[f187,f318])).

fof(f417,plain,(
    k1_xboole_0 = k4_xboole_0(sK14,sK13) ),
    inference(cnf_transformation,[],[f319])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f333,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f574,plain,(
    o_0_0_xboole_0 = k4_xboole_0(sK14,sK13) ),
    inference(definition_unfolding,[],[f417,f333])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f329,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f99,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f467,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f99])).

fof(f538,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f329,f467,f467])).

fof(f85,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f452,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f85])).

fof(f89,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f457,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f89])).

fof(f608,plain,(
    ! [X0] : k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f457,f333])).

fof(f115,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f225,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f115])).

fof(f483,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f225])).

fof(f416,plain,(
    r2_xboole_0(sK13,sK14) ),
    inference(cnf_transformation,[],[f319])).

cnf(c_89,negated_conjecture,
    ( o_0_0_xboole_0 = k4_xboole_0(sK14,sK13) ),
    inference(cnf_transformation,[],[f574])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f538])).

cnf(c_125,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f452])).

cnf(c_6027,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_125])).

cnf(c_8316,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_6027])).

cnf(c_12942,plain,
    ( r1_tarski(k4_xboole_0(sK14,o_0_0_xboole_0),sK13) = iProver_top ),
    inference(superposition,[status(thm)],[c_89,c_8316])).

cnf(c_130,plain,
    ( k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f608])).

cnf(c_12990,plain,
    ( r1_tarski(sK14,sK13) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12942,c_130])).

cnf(c_155,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f483])).

cnf(c_7280,plain,
    ( ~ r1_tarski(sK14,sK13)
    | ~ r2_xboole_0(sK13,sK14) ),
    inference(instantiation,[status(thm)],[c_155])).

cnf(c_7281,plain,
    ( r1_tarski(sK14,sK13) != iProver_top
    | r2_xboole_0(sK13,sK14) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7280])).

cnf(c_90,negated_conjecture,
    ( r2_xboole_0(sK13,sK14) ),
    inference(cnf_transformation,[],[f416])).

cnf(c_205,plain,
    ( r2_xboole_0(sK13,sK14) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_90])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12990,c_7281,c_205])).

%------------------------------------------------------------------------------
