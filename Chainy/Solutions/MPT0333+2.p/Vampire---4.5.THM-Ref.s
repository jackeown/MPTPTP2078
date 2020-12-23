%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0333+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:24 EST 2020

% Result     : Theorem 2.70s
% Output     : Refutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   27 (  65 expanded)
%              Number of leaves         :    7 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   30 (  69 expanded)
%              Number of equality atoms :   29 (  68 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3486,plain,(
    $false ),
    inference(subsumption_resolution,[],[f698,f3485])).

fof(f3485,plain,(
    ! [X6,X4,X5,X3] : k2_zfmisc_1(k2_tarski(X3,X6),k2_tarski(X4,X5)) = k2_xboole_0(k2_tarski(k4_tarski(X3,X4),k4_tarski(X3,X5)),k2_tarski(k4_tarski(X6,X4),k4_tarski(X6,X5))) ),
    inference(forward_demodulation,[],[f3470,f793])).

fof(f793,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k2_tarski(X0,X0),k2_tarski(X1,X2)) ),
    inference(forward_demodulation,[],[f728,f697])).

fof(f697,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f566,f546])).

fof(f546,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f192])).

fof(f192,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f566,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f262])).

fof(f262,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(f728,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)),k2_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f605,f696])).

fof(f696,plain,(
    ! [X0] : k1_tarski(X0) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)) ),
    inference(definition_unfolding,[],[f567,f546])).

fof(f567,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f267])).

fof(f267,axiom,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

fof(f605,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f384])).

fof(f384,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f3470,plain,(
    ! [X6,X4,X5,X3] : k2_zfmisc_1(k2_tarski(X3,X6),k2_tarski(X4,X5)) = k2_xboole_0(k2_tarski(k4_tarski(X3,X4),k4_tarski(X3,X5)),k2_zfmisc_1(k2_tarski(X6,X6),k2_tarski(X4,X5))) ),
    inference(superposition,[],[f805,f793])).

fof(f805,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k2_tarski(X0,X0),X2),k2_zfmisc_1(k2_tarski(X1,X1),X2)) ),
    inference(forward_demodulation,[],[f804,f697])).

fof(f804,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)),X2),k2_zfmisc_1(k2_tarski(X1,X1),X2)) ),
    inference(forward_demodulation,[],[f733,f697])).

fof(f733,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)),X2),k2_zfmisc_1(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)),X2)) ),
    inference(definition_unfolding,[],[f635,f696,f696])).

fof(f635,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) ),
    inference(cnf_transformation,[],[f345])).

fof(f345,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1)))
      & k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_zfmisc_1)).

fof(f698,plain,(
    k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_xboole_0(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k2_tarski(k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))) ),
    inference(definition_unfolding,[],[f545,f546])).

fof(f545,plain,(
    k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)) ),
    inference(cnf_transformation,[],[f496])).

fof(f496,plain,(
    k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f443,f495])).

fof(f495,plain,
    ( ? [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) != k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))
   => k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)) ),
    introduced(choice_axiom,[])).

fof(f443,plain,(
    ? [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) != k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(ennf_transformation,[],[f360])).

fof(f360,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(negated_conjecture,[],[f359])).

fof(f359,conjecture,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).
%------------------------------------------------------------------------------
