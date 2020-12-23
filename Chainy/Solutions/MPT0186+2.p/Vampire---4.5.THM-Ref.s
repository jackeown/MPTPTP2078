%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0186+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:15 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   20 (  29 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :    9
%              Number of atoms          :   21 (  30 expanded)
%              Number of equality atoms :   20 (  29 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f541,plain,(
    $false ),
    inference(subsumption_resolution,[],[f540,f502])).

fof(f502,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(definition_unfolding,[],[f369,f366])).

fof(f366,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f200])).

fof(f200,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f369,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f198])).

fof(f198,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f540,plain,(
    k2_xboole_0(k1_enumset1(sK15,sK16,sK17),k1_tarski(sK18)) != k2_xboole_0(k1_tarski(sK15),k1_enumset1(sK16,sK17,sK18)) ),
    inference(forward_demodulation,[],[f539,f397])).

fof(f397,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(cnf_transformation,[],[f251])).

fof(f251,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).

fof(f539,plain,(
    k2_xboole_0(k1_enumset1(sK15,sK16,sK17),k1_tarski(sK18)) != k2_xboole_0(k1_tarski(sK15),k1_enumset1(sK16,sK18,sK17)) ),
    inference(forward_demodulation,[],[f538,f394])).

fof(f394,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f190])).

fof(f190,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

fof(f538,plain,(
    k2_xboole_0(k1_enumset1(sK15,sK16,sK17),k1_tarski(sK18)) != k2_xboole_0(k1_tarski(sK15),k1_enumset1(sK17,sK16,sK18)) ),
    inference(forward_demodulation,[],[f499,f502])).

fof(f499,plain,(
    k2_xboole_0(k1_enumset1(sK15,sK16,sK17),k1_tarski(sK18)) != k2_xboole_0(k1_enumset1(sK15,sK17,sK16),k1_tarski(sK18)) ),
    inference(definition_unfolding,[],[f365,f366,f366])).

fof(f365,plain,(
    k2_enumset1(sK15,sK16,sK17,sK18) != k2_enumset1(sK15,sK17,sK16,sK18) ),
    inference(cnf_transformation,[],[f293])).

fof(f293,plain,(
    k2_enumset1(sK15,sK16,sK17,sK18) != k2_enumset1(sK15,sK17,sK16,sK18) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16,sK17,sK18])],[f256,f292])).

fof(f292,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X2,X1,X3)
   => k2_enumset1(sK15,sK16,sK17,sK18) != k2_enumset1(sK15,sK17,sK16,sK18) ),
    introduced(choice_axiom,[])).

fof(f256,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X2,X1,X3) ),
    inference(ennf_transformation,[],[f194])).

fof(f194,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    inference(negated_conjecture,[],[f193])).

% (19341)Refutation not found, incomplete strategy% (19341)------------------------------
% (19341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19342)ott+11_8:1_av=off:bs=on:bce=on:fde=none:gsp=input_only:gs=on:gsem=on:irw=on:lcm=predicate:nm=6:nwc=1.5:sd=2:ss=axioms:st=1.2:sos=theory:urr=on:updr=off_49 on theBenchmark
% (19333)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_11 on theBenchmark
% (19339)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% (19339)Refutation not found, incomplete strategy% (19339)------------------------------
% (19339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19339)Termination reason: Refutation not found, incomplete strategy

% (19339)Memory used [KB]: 11001
% (19339)Time elapsed: 0.155 s
% (19339)------------------------------
% (19339)------------------------------
% (19333)Refutation not found, incomplete strategy% (19333)------------------------------
% (19333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19333)Termination reason: Refutation not found, incomplete strategy

% (19333)Memory used [KB]: 11129
% (19333)Time elapsed: 0.156 s
% (19333)------------------------------
% (19333)------------------------------
fof(f193,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).
%------------------------------------------------------------------------------
