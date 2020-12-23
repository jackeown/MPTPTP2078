%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0169+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   19 (  24 expanded)
%              Number of leaves         :    6 (   8 expanded)
%              Depth                    :    6
%              Number of atoms          :   20 (  25 expanded)
%              Number of equality atoms :   19 (  24 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f339,plain,(
    $false ),
    inference(subsumption_resolution,[],[f299,f333])).

fof(f333,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3)) ),
    inference(definition_unfolding,[],[f292,f296])).

fof(f296,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k2_enumset1(X4,X4,X4,X4)) ),
    inference(definition_unfolding,[],[f253,f295])).

fof(f295,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_enumset1(X6,X6,X6,X6)) ),
    inference(definition_unfolding,[],[f245,f273])).

fof(f273,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f231])).

fof(f231,axiom,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).

fof(f245,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(cnf_transformation,[],[f210])).

fof(f210,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

fof(f253,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f229])).

fof(f229,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_enumset1)).

fof(f292,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f221])).

fof(f221,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f299,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f244,f295])).

fof(f244,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f239])).

fof(f239,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f237,f238])).

fof(f238,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k5_enumset1(X0,X0,X0,X0,X1,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f237,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(ennf_transformation,[],[f235])).

fof(f235,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(negated_conjecture,[],[f234])).

fof(f234,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_enumset1)).
%------------------------------------------------------------------------------
