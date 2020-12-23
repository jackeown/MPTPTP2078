%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0604+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   13 (  17 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    6
%              Number of atoms          :   14 (  18 expanded)
%              Number of equality atoms :   13 (  17 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1816,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1617,f1616])).

fof(f1616,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f1228,f1425])).

fof(f1425,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f254])).

fof(f254,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f1228,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f821])).

fof(f821,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relat_1)).

fof(f1617,plain,(
    k2_tarski(sK0,sK0) != k3_relat_1(k2_tarski(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))) ),
    inference(definition_unfolding,[],[f1225,f1425,f1425])).

fof(f1225,plain,(
    k1_tarski(sK0) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK0))) ),
    inference(cnf_transformation,[],[f1069])).

fof(f1069,plain,(
    k1_tarski(sK0) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f878,f1068])).

fof(f1068,plain,
    ( ? [X0] : k1_tarski(X0) != k3_relat_1(k1_tarski(k4_tarski(X0,X0)))
   => k1_tarski(sK0) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK0))) ),
    introduced(choice_axiom,[])).

fof(f878,plain,(
    ? [X0] : k1_tarski(X0) != k3_relat_1(k1_tarski(k4_tarski(X0,X0))) ),
    inference(ennf_transformation,[],[f809])).

fof(f809,negated_conjecture,(
    ~ ! [X0] : k1_tarski(X0) = k3_relat_1(k1_tarski(k4_tarski(X0,X0))) ),
    inference(negated_conjecture,[],[f808])).

fof(f808,conjecture,(
    ! [X0] : k1_tarski(X0) = k3_relat_1(k1_tarski(k4_tarski(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t208_relat_1)).
%------------------------------------------------------------------------------
