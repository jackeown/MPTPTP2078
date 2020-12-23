%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   19 (  31 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :    8
%              Number of atoms          :   27 (  46 expanded)
%              Number of equality atoms :   26 (  45 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f172,plain,(
    $false ),
    inference(subsumption_resolution,[],[f10,f171])).

fof(f171,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k3_mcart_1(k4_tarski(X0,X1),X2,X3) ),
    inference(forward_demodulation,[],[f155,f11])).

fof(f11,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f155,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k3_mcart_1(k4_tarski(X0,X1),X2,X3) ),
    inference(superposition,[],[f146,f146])).

fof(f146,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X14,X12,X10,X8,X15,X13,X11,X9] :
      ( k4_mcart_1(X12,X13,X14,X15) != k4_mcart_1(X8,X9,X10,X11)
      | k3_mcart_1(X12,X13,X14) = k4_tarski(k4_tarski(X8,X9),X10) ) ),
    inference(superposition,[],[f19,f12])).

fof(f12,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_mcart_1)).

fof(f19,plain,(
    ! [X14,X12,X17,X15,X13,X16] :
      ( k4_mcart_1(X12,X13,X14,X15) != k4_tarski(X16,X17)
      | k3_mcart_1(X12,X13,X14) = X16 ) ),
    inference(superposition,[],[f13,f11])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k4_tarski(X0,X1) != k4_tarski(X2,X3) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( k4_tarski(X0,X1) = k4_tarski(X2,X3)
     => ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_zfmisc_1)).

fof(f10,plain,(
    k4_mcart_1(sK0,sK1,sK2,sK3) != k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k4_mcart_1(sK0,sK1,sK2,sK3) != k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f6,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) != k3_mcart_1(k4_tarski(X0,X1),X2,X3)
   => k4_mcart_1(sK0,sK1,sK2,sK3) != k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) != k3_mcart_1(k4_tarski(X0,X1),X2,X3) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k3_mcart_1(k4_tarski(X0,X1),X2,X3) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k3_mcart_1(k4_tarski(X0,X1),X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:31:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (28274)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.47  % (28274)Refutation not found, incomplete strategy% (28274)------------------------------
% 0.21/0.47  % (28274)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (28274)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (28274)Memory used [KB]: 1663
% 0.21/0.47  % (28274)Time elapsed: 0.049 s
% 0.21/0.47  % (28274)------------------------------
% 0.21/0.47  % (28274)------------------------------
% 0.21/0.48  % (28266)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.49  % (28258)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (28258)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f172,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f10,f171])).
% 0.21/0.51  fof(f171,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k3_mcart_1(k4_tarski(X0,X1),X2,X3)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f155,f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k3_mcart_1(k4_tarski(X0,X1),X2,X3)) )),
% 0.21/0.51    inference(superposition,[],[f146,f146])).
% 0.21/0.51  fof(f146,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.21/0.51    inference(equality_resolution,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X14,X12,X10,X8,X15,X13,X11,X9] : (k4_mcart_1(X12,X13,X14,X15) != k4_mcart_1(X8,X9,X10,X11) | k3_mcart_1(X12,X13,X14) = k4_tarski(k4_tarski(X8,X9),X10)) )),
% 0.21/0.51    inference(superposition,[],[f19,f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_mcart_1)).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ( ! [X14,X12,X17,X15,X13,X16] : (k4_mcart_1(X12,X13,X14,X15) != k4_tarski(X16,X17) | k3_mcart_1(X12,X13,X14) = X16) )),
% 0.21/0.51    inference(superposition,[],[f13,f11])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k4_tarski(X0,X1) != k4_tarski(X2,X3) | X0 = X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((X1 = X3 & X0 = X2) | k4_tarski(X0,X1) != k4_tarski(X2,X3))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (k4_tarski(X0,X1) = k4_tarski(X2,X3) => (X1 = X3 & X0 = X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_zfmisc_1)).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    k4_mcart_1(sK0,sK1,sK2,sK3) != k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    k4_mcart_1(sK0,sK1,sK2,sK3) != k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f6,f8])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) != k3_mcart_1(k4_tarski(X0,X1),X2,X3) => k4_mcart_1(sK0,sK1,sK2,sK3) != k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3)),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f6,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) != k3_mcart_1(k4_tarski(X0,X1),X2,X3)),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k3_mcart_1(k4_tarski(X0,X1),X2,X3)),
% 0.21/0.51    inference(negated_conjecture,[],[f4])).
% 0.21/0.51  fof(f4,conjecture,(
% 0.21/0.51    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k3_mcart_1(k4_tarski(X0,X1),X2,X3)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_mcart_1)).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (28258)------------------------------
% 0.21/0.51  % (28258)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (28258)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (28258)Memory used [KB]: 6396
% 0.21/0.51  % (28258)Time elapsed: 0.072 s
% 0.21/0.51  % (28258)------------------------------
% 0.21/0.51  % (28258)------------------------------
% 0.21/0.51  % (28252)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (28250)Success in time 0.146 s
%------------------------------------------------------------------------------
