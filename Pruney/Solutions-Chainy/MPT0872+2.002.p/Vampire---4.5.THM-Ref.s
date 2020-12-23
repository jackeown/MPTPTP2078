%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   13 (  15 expanded)
%              Number of leaves         :    4 (   5 expanded)
%              Depth                    :    6
%              Number of atoms          :   14 (  16 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f12])).

fof(f12,plain,(
    k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3) != k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3) ),
    inference(definition_unfolding,[],[f8,f11,f9])).

fof(f9,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f11,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f10,f9])).

fof(f10,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f8,plain,(
    k4_mcart_1(sK0,sK1,sK2,sK3) != k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k4_mcart_1(sK0,sK1,sK2,sK3) != k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) != k3_mcart_1(k4_tarski(X0,X1),X2,X3)
   => k4_mcart_1(sK0,sK1,sK2,sK3) != k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) != k3_mcart_1(k4_tarski(X0,X1),X2,X3) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k3_mcart_1(k4_tarski(X0,X1),X2,X3) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k3_mcart_1(k4_tarski(X0,X1),X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n021.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:40:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (32592)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.46  % (32589)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.46  % (32592)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f13,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(trivial_inequality_removal,[],[f12])).
% 0.22/0.46  fof(f12,plain,(
% 0.22/0.46    k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3) != k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3)),
% 0.22/0.46    inference(definition_unfolding,[],[f8,f11,f9])).
% 0.22/0.46  fof(f9,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.22/0.46  fof(f11,plain,(
% 0.22/0.46    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.22/0.46    inference(definition_unfolding,[],[f10,f9])).
% 0.22/0.46  fof(f10,plain,(
% 0.22/0.46    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).
% 0.22/0.46  fof(f8,plain,(
% 0.22/0.46    k4_mcart_1(sK0,sK1,sK2,sK3) != k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3)),
% 0.22/0.46    inference(cnf_transformation,[],[f7])).
% 0.22/0.46  fof(f7,plain,(
% 0.22/0.46    k4_mcart_1(sK0,sK1,sK2,sK3) != k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3)),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f5,f6])).
% 0.22/0.46  fof(f6,plain,(
% 0.22/0.46    ? [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) != k3_mcart_1(k4_tarski(X0,X1),X2,X3) => k4_mcart_1(sK0,sK1,sK2,sK3) != k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3)),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f5,plain,(
% 0.22/0.46    ? [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) != k3_mcart_1(k4_tarski(X0,X1),X2,X3)),
% 0.22/0.46    inference(ennf_transformation,[],[f4])).
% 0.22/0.46  fof(f4,negated_conjecture,(
% 0.22/0.46    ~! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k3_mcart_1(k4_tarski(X0,X1),X2,X3)),
% 0.22/0.46    inference(negated_conjecture,[],[f3])).
% 0.22/0.46  fof(f3,conjecture,(
% 0.22/0.46    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k3_mcart_1(k4_tarski(X0,X1),X2,X3)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_mcart_1)).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (32592)------------------------------
% 0.22/0.46  % (32592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (32592)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (32592)Memory used [KB]: 6012
% 0.22/0.46  % (32592)Time elapsed: 0.004 s
% 0.22/0.46  % (32592)------------------------------
% 0.22/0.46  % (32592)------------------------------
% 0.22/0.47  % (32585)Success in time 0.103 s
%------------------------------------------------------------------------------
