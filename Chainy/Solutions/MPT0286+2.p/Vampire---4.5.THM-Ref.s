%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0286+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:21 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :   10 (  10 expanded)
%              Number of leaves         :    3 (   3 expanded)
%              Depth                    :    6
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f532,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f490])).

fof(f490,plain,(
    k3_tarski(k2_tarski(sK0,sK1)) != k3_tarski(k2_tarski(sK0,sK1)) ),
    inference(definition_unfolding,[],[f429,f439])).

fof(f439,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f309])).

fof(f309,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f429,plain,(
    k2_xboole_0(sK0,sK1) != k3_tarski(k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f409])).

fof(f409,plain,(
    k2_xboole_0(sK0,sK1) != k3_tarski(k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f388,f408])).

fof(f408,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k3_tarski(k2_tarski(X0,X1))
   => k2_xboole_0(sK0,sK1) != k3_tarski(k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f388,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k3_tarski(k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f385])).

fof(f385,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f384])).

fof(f384,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_zfmisc_1)).
%------------------------------------------------------------------------------
