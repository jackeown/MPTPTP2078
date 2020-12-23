%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0604+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:17 EST 2020

% Result     : Theorem 0.16s
% Output     : Refutation 0.16s
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
fof(f13,plain,(
    $false ),
    inference(subsumption_resolution,[],[f12,f11])).

fof(f11,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f10,f9])).

fof(f9,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f10,plain,(
    ! [X0,X1] : k3_relat_1(k1_tarski(k4_tarski(X0,X1))) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_relat_1(k1_tarski(k4_tarski(X0,X1))) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relat_1)).

fof(f12,plain,(
    k2_tarski(sK0,sK0) != k3_relat_1(k2_tarski(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))) ),
    inference(definition_unfolding,[],[f8,f9,f9])).

fof(f8,plain,(
    k1_tarski(sK0) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK0))) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k1_tarski(sK0) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f5,f6])).

% (11568)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% (11561)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
fof(f6,plain,
    ( ? [X0] : k1_tarski(X0) != k3_relat_1(k1_tarski(k4_tarski(X0,X0)))
   => k1_tarski(sK0) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK0))) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0] : k1_tarski(X0) != k3_relat_1(k1_tarski(k4_tarski(X0,X0))) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] : k1_tarski(X0) = k3_relat_1(k1_tarski(k4_tarski(X0,X0))) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] : k1_tarski(X0) = k3_relat_1(k1_tarski(k4_tarski(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t208_relat_1)).

%------------------------------------------------------------------------------
