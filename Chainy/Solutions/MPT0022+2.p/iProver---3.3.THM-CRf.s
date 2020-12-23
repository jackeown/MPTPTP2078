%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0022+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:12 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   38 (  63 expanded)
%              Number of clauses        :   15 (  16 expanded)
%              Number of leaves         :    8 (  18 expanded)
%              Depth                    :   10
%              Number of atoms          :   57 (  96 expanded)
%              Number of equality atoms :   45 (  84 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f45,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = k1_xboole_0
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(X0,X1) = k1_xboole_0
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f45])).

fof(f90,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 != X0
      & k2_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f46])).

fof(f147,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 != X0
        & k2_xboole_0(X0,X1) = k1_xboole_0 )
   => ( k1_xboole_0 != sK14
      & k2_xboole_0(sK14,sK15) = k1_xboole_0 ) ),
    introduced(choice_axiom,[])).

fof(f148,plain,
    ( k1_xboole_0 != sK14
    & k2_xboole_0(sK14,sK15) = k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14,sK15])],[f90,f147])).

fof(f225,plain,(
    k2_xboole_0(sK14,sK15) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f148])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f156,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f255,plain,(
    k2_xboole_0(sK14,sK15) = o_0_0_xboole_0 ),
    inference(definition_unfolding,[],[f225,f156])).

fof(f54,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f234,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f54])).

fof(f47,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f227,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f47])).

fof(f256,plain,(
    ! [X0] : k2_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f227,f156])).

fof(f49,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f229,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f49])).

fof(f257,plain,(
    ! [X0] : r1_tarski(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f229,f156])).

fof(f50,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f93,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f50])).

fof(f230,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f258,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ r1_tarski(X0,o_0_0_xboole_0) ) ),
    inference(definition_unfolding,[],[f230,f156,f156])).

fof(f226,plain,(
    k1_xboole_0 != sK14 ),
    inference(cnf_transformation,[],[f148])).

fof(f254,plain,(
    o_0_0_xboole_0 != sK14 ),
    inference(definition_unfolding,[],[f226,f156])).

cnf(c_75,negated_conjecture,
    ( k2_xboole_0(sK14,sK15) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f255])).

cnf(c_83,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f234])).

cnf(c_3532,plain,
    ( k2_xboole_0(sK14,o_0_0_xboole_0) = k2_xboole_0(sK14,sK15) ),
    inference(superposition,[status(thm)],[c_75,c_83])).

cnf(c_3547,plain,
    ( k2_xboole_0(sK14,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3532,c_75])).

cnf(c_76,plain,
    ( k2_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f256])).

cnf(c_3622,plain,
    ( sK14 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_3547,c_76])).

cnf(c_1519,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3460,plain,
    ( sK14 != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = sK14 ),
    inference(instantiation,[status(thm)],[c_1519])).

cnf(c_3461,plain,
    ( sK14 != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK14
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3460])).

cnf(c_78,plain,
    ( r1_tarski(o_0_0_xboole_0,X0) ),
    inference(cnf_transformation,[],[f257])).

cnf(c_112,plain,
    ( r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_78])).

cnf(c_79,plain,
    ( ~ r1_tarski(X0,o_0_0_xboole_0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f258])).

cnf(c_109,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0)
    | o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_79])).

cnf(c_74,negated_conjecture,
    ( o_0_0_xboole_0 != sK14 ),
    inference(cnf_transformation,[],[f254])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3622,c_3461,c_112,c_109,c_74])).

%------------------------------------------------------------------------------
