%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0880+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:55 EST 2020

% Result     : Theorem 1.62s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   19 (  34 expanded)
%              Number of leaves         :    6 (  13 expanded)
%              Depth                    :    8
%              Number of atoms          :   21 (  37 expanded)
%              Number of equality atoms :   20 (  36 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
% (32435)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_4 on theBenchmark
fof(f3298,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f3297])).

fof(f3297,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK63),k1_tarski(sK64)),k1_tarski(sK65)),k1_tarski(sK66)) != k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK63),k1_tarski(sK64)),k1_tarski(sK65)),k1_tarski(sK66)) ),
    inference(forward_demodulation,[],[f3290,f3138])).

fof(f3138,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)) = k2_xboole_0(k1_tarski(k4_tarski(X0,X2)),k1_tarski(k4_tarski(X1,X2))) ),
    inference(definition_unfolding,[],[f2409,f2414,f2414])).

fof(f2414,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f226])).

fof(f226,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f2409,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f394])).

fof(f394,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f3290,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK63),k1_tarski(sK64)),k1_tarski(sK65)),k1_tarski(sK66)) != k2_zfmisc_1(k2_xboole_0(k1_tarski(k4_tarski(sK63,sK65)),k1_tarski(k4_tarski(sK64,sK65))),k1_tarski(sK66)) ),
    inference(superposition,[],[f3064,f3138])).

fof(f3064,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK63),k1_tarski(sK64)),k1_tarski(sK65)),k1_tarski(sK66)) != k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK63,sK65),sK66)),k1_tarski(k4_tarski(k4_tarski(sK64,sK65),sK66))) ),
    inference(definition_unfolding,[],[f2257,f2282,f2414,f2414,f2265,f2265])).

fof(f2265,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1274])).

fof(f1274,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f2282,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1275])).

fof(f1275,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f2257,plain,(
    k3_zfmisc_1(k2_tarski(sK63,sK64),k1_tarski(sK65),k1_tarski(sK66)) != k2_tarski(k3_mcart_1(sK63,sK65,sK66),k3_mcart_1(sK64,sK65,sK66)) ),
    inference(cnf_transformation,[],[f1895])).

fof(f1895,plain,(
    k3_zfmisc_1(k2_tarski(sK63,sK64),k1_tarski(sK65),k1_tarski(sK66)) != k2_tarski(k3_mcart_1(sK63,sK65,sK66),k3_mcart_1(sK64,sK65,sK66)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK63,sK64,sK65,sK66])],[f1341,f1894])).

fof(f1894,plain,
    ( ? [X0,X1,X2,X3] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) != k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3))
   => k3_zfmisc_1(k2_tarski(sK63,sK64),k1_tarski(sK65),k1_tarski(sK66)) != k2_tarski(k3_mcart_1(sK63,sK65,sK66),k3_mcart_1(sK64,sK65,sK66)) ),
    introduced(choice_axiom,[])).

fof(f1341,plain,(
    ? [X0,X1,X2,X3] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) != k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3)) ),
    inference(ennf_transformation,[],[f1328])).

fof(f1328,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) = k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3)) ),
    inference(negated_conjecture,[],[f1327])).

fof(f1327,conjecture,(
    ! [X0,X1,X2,X3] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) = k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_mcart_1)).
%------------------------------------------------------------------------------
