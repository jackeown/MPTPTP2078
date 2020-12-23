%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0867+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   16 (  35 expanded)
%              Number of leaves         :    5 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :   17 (  36 expanded)
%              Number of equality atoms :   16 (  35 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3915,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3588,f3591])).

% (22207)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_7 on theBenchmark
% (22221)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_48 on theBenchmark
fof(f3591,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_xboole_0(k1_enumset1(X0,X0,X0),k1_tarski(X1)),k2_xboole_0(k1_enumset1(X2,X2,X2),k1_tarski(X3))) = k2_xboole_0(k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2)),k1_tarski(k4_tarski(X1,X3))) ),
    inference(definition_unfolding,[],[f2524,f3582,f3582,f2525])).

fof(f2525,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f231])).

% (22208)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_23 on theBenchmark
fof(f231,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f3582,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_tarski(X1)) ),
    inference(definition_unfolding,[],[f2550,f2525])).

fof(f2550,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f262])).

fof(f262,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f2524,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f363])).

fof(f363,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(f3588,plain,(
    k2_zfmisc_1(k2_xboole_0(k1_enumset1(sK97,sK97,sK97),k1_tarski(sK98)),k2_xboole_0(k1_enumset1(sK99,sK99,sK99),k1_tarski(sK100))) != k2_xboole_0(k1_enumset1(k4_tarski(sK97,sK99),k4_tarski(sK97,sK100),k4_tarski(sK98,sK99)),k1_tarski(k4_tarski(sK98,sK100))) ),
    inference(definition_unfolding,[],[f2512,f3582,f3582,f2525])).

fof(f2512,plain,(
    k2_zfmisc_1(k2_tarski(sK97,sK98),k2_tarski(sK99,sK100)) != k2_enumset1(k4_tarski(sK97,sK99),k4_tarski(sK97,sK100),k4_tarski(sK98,sK99),k4_tarski(sK98,sK100)) ),
    inference(cnf_transformation,[],[f2023])).

fof(f2023,plain,(
    k2_zfmisc_1(k2_tarski(sK97,sK98),k2_tarski(sK99,sK100)) != k2_enumset1(k4_tarski(sK97,sK99),k4_tarski(sK97,sK100),k4_tarski(sK98,sK99),k4_tarski(sK98,sK100)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK97,sK98,sK99,sK100])],[f1323,f2022])).

fof(f2022,plain,
    ( ? [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) != k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))
   => k2_zfmisc_1(k2_tarski(sK97,sK98),k2_tarski(sK99,sK100)) != k2_enumset1(k4_tarski(sK97,sK99),k4_tarski(sK97,sK100),k4_tarski(sK98,sK99),k4_tarski(sK98,sK100)) ),
    introduced(choice_axiom,[])).

fof(f1323,plain,(
    ? [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) != k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(ennf_transformation,[],[f1307])).

fof(f1307,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(negated_conjecture,[],[f1306])).

fof(f1306,conjecture,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_mcart_1)).
%------------------------------------------------------------------------------
