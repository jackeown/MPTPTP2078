%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0090+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:20 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 145 expanded)
%              Number of clauses        :   20 (  38 expanded)
%              Number of leaves         :   10 (  41 expanded)
%              Depth                    :   14
%              Number of atoms          :   82 ( 222 expanded)
%              Number of equality atoms :   58 ( 169 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f53,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f370,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f53])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f290,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f489,plain,(
    ! [X0] : k2_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f370,f290])).

fof(f129,conjecture,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f130,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
      <=> k4_xboole_0(X0,X1) = X0 ) ),
    inference(negated_conjecture,[],[f129])).

fof(f222,plain,(
    ? [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <~> k4_xboole_0(X0,X1) = X0 ) ),
    inference(ennf_transformation,[],[f130])).

fof(f280,plain,(
    ? [X0,X1] :
      ( ( k4_xboole_0(X0,X1) != X0
        | ~ r1_xboole_0(X0,X1) )
      & ( k4_xboole_0(X0,X1) = X0
        | r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f222])).

fof(f281,plain,
    ( ? [X0,X1] :
        ( ( k4_xboole_0(X0,X1) != X0
          | ~ r1_xboole_0(X0,X1) )
        & ( k4_xboole_0(X0,X1) = X0
          | r1_xboole_0(X0,X1) ) )
   => ( ( k4_xboole_0(sK15,sK16) != sK15
        | ~ r1_xboole_0(sK15,sK16) )
      & ( k4_xboole_0(sK15,sK16) = sK15
        | r1_xboole_0(sK15,sK16) ) ) ),
    introduced(choice_axiom,[])).

fof(f282,plain,
    ( ( k4_xboole_0(sK15,sK16) != sK15
      | ~ r1_xboole_0(sK15,sK16) )
    & ( k4_xboole_0(sK15,sK16) = sK15
      | r1_xboole_0(sK15,sK16) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16])],[f280,f281])).

fof(f452,plain,
    ( k4_xboole_0(sK15,sK16) = sK15
    | r1_xboole_0(sK15,sK16) ),
    inference(cnf_transformation,[],[f282])).

fof(f122,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f218,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f122])).

fof(f445,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f218])).

fof(f87,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f407,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f87])).

fof(f532,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f445,f407,f407])).

fof(f77,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f397,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f77])).

fof(f509,plain,(
    ! [X0] : k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f397,f290])).

fof(f65,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f384,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

fof(f502,plain,(
    ! [X0] : o_0_0_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) ),
    inference(definition_unfolding,[],[f384,f407,f290,f290])).

fof(f86,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f406,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f86])).

fof(f512,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f406,f407])).

fof(f123,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f446,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f123])).

fof(f453,plain,
    ( k4_xboole_0(sK15,sK16) != sK15
    | ~ r1_xboole_0(sK15,sK16) ),
    inference(cnf_transformation,[],[f282])).

cnf(c_85,plain,
    ( k2_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f489])).

cnf(c_167,negated_conjecture,
    ( r1_xboole_0(sK15,sK16)
    | k4_xboole_0(sK15,sK16) = sK15 ),
    inference(cnf_transformation,[],[f452])).

cnf(c_5108,plain,
    ( k4_xboole_0(sK15,sK16) = sK15
    | r1_xboole_0(sK15,sK16) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_167])).

cnf(c_159,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f532])).

cnf(c_5115,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,X2))
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_159])).

cnf(c_9999,plain,
    ( k4_xboole_0(sK15,k4_xboole_0(sK15,k2_xboole_0(sK16,X0))) = k4_xboole_0(sK15,k4_xboole_0(sK15,X0))
    | k4_xboole_0(sK15,sK16) = sK15 ),
    inference(superposition,[status(thm)],[c_5108,c_5115])).

cnf(c_10628,plain,
    ( k4_xboole_0(sK15,k4_xboole_0(sK15,o_0_0_xboole_0)) = k4_xboole_0(sK15,k4_xboole_0(sK15,sK16))
    | k4_xboole_0(sK15,sK16) = sK15 ),
    inference(superposition,[status(thm)],[c_85,c_9999])).

cnf(c_112,plain,
    ( k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f509])).

cnf(c_99,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f502])).

cnf(c_5264,plain,
    ( k4_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_99,c_112])).

cnf(c_10975,plain,
    ( k4_xboole_0(sK15,k4_xboole_0(sK15,sK16)) = o_0_0_xboole_0
    | k4_xboole_0(sK15,sK16) = sK15 ),
    inference(demodulation,[status(thm)],[c_10628,c_112,c_5264])).

cnf(c_121,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f512])).

cnf(c_11333,plain,
    ( k4_xboole_0(sK15,sK16) = sK15
    | k4_xboole_0(sK15,o_0_0_xboole_0) = k4_xboole_0(sK15,sK16) ),
    inference(superposition,[status(thm)],[c_10975,c_121])).

cnf(c_11386,plain,
    ( k4_xboole_0(sK15,sK16) = sK15 ),
    inference(demodulation,[status(thm)],[c_11333,c_112])).

cnf(c_160,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f446])).

cnf(c_5114,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_160])).

cnf(c_11588,plain,
    ( r1_xboole_0(sK15,sK16) = iProver_top ),
    inference(superposition,[status(thm)],[c_11386,c_5114])).

cnf(c_166,negated_conjecture,
    ( ~ r1_xboole_0(sK15,sK16)
    | k4_xboole_0(sK15,sK16) != sK15 ),
    inference(cnf_transformation,[],[f453])).

cnf(c_172,plain,
    ( k4_xboole_0(sK15,sK16) != sK15
    | r1_xboole_0(sK15,sK16) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_166])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11588,c_11386,c_172])).

%------------------------------------------------------------------------------
