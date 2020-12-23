%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0102+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:21 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   36 (  67 expanded)
%              Number of clauses        :   12 (  21 expanded)
%              Number of leaves         :    9 (  19 expanded)
%              Depth                    :   10
%              Number of atoms          :   37 (  68 expanded)
%              Number of equality atoms :   36 (  67 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f143,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f488,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f143])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f311,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f608,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(definition_unfolding,[],[f488,f311])).

fof(f142,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f487,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f142])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f308,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f103,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f444,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f103])).

fof(f581,plain,(
    ! [X0] : k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f444,f311])).

fof(f146,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f147,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f146])).

fof(f246,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f147])).

fof(f302,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
   => k3_xboole_0(sK15,sK16) != k5_xboole_0(k5_xboole_0(sK15,sK16),k2_xboole_0(sK15,sK16)) ),
    introduced(choice_axiom,[])).

fof(f303,plain,(
    k3_xboole_0(sK15,sK16) != k5_xboole_0(k5_xboole_0(sK15,sK16),k2_xboole_0(sK15,sK16)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16])],[f246,f302])).

fof(f491,plain,(
    k3_xboole_0(sK15,sK16) != k5_xboole_0(k5_xboole_0(sK15,sK16),k2_xboole_0(sK15,sK16)) ),
    inference(cnf_transformation,[],[f303])).

fof(f145,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f490,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f145])).

fof(f89,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f430,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f89])).

fof(f493,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f490,f430])).

fof(f610,plain,(
    k5_xboole_0(k5_xboole_0(sK15,sK16),k5_xboole_0(k5_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))) != k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)) ),
    inference(definition_unfolding,[],[f491,f430,f493])).

cnf(c_182,plain,
    ( k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f608])).

cnf(c_181,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f487])).

cnf(c_6836,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(o_0_0_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_182,c_181])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f308])).

cnf(c_138,plain,
    ( k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f581])).

cnf(c_6744,plain,
    ( k5_xboole_0(o_0_0_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_5,c_138])).

cnf(c_7591,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_6836,c_6744])).

cnf(c_184,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(sK15,sK16),k5_xboole_0(k5_xboole_0(sK15,sK16),k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))) != k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)) ),
    inference(cnf_transformation,[],[f610])).

cnf(c_2878,negated_conjecture,
    ( k5_xboole_0(sK15,k5_xboole_0(sK15,k5_xboole_0(sK16,k5_xboole_0(sK16,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))))) != k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)) ),
    inference(theory_normalisation,[status(thm)],[c_184,c_181,c_5])).

cnf(c_7594,plain,
    ( k5_xboole_0(sK15,k5_xboole_0(sK15,k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)))) != k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)) ),
    inference(demodulation,[status(thm)],[c_7591,c_2878])).

cnf(c_7599,plain,
    ( k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)) != k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)) ),
    inference(demodulation,[status(thm)],[c_7594,c_7591])).

cnf(c_7600,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_7599])).

%------------------------------------------------------------------------------
