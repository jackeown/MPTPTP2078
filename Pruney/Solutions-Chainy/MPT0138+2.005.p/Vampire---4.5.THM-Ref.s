%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   28 (  52 expanded)
%              Number of leaves         :    7 (  18 expanded)
%              Depth                    :   13
%              Number of atoms          :   29 (  53 expanded)
%              Number of equality atoms :   28 (  52 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    7 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f131,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f130])).

fof(f130,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))) ),
    inference(forward_demodulation,[],[f129,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f129,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))))) ),
    inference(superposition,[],[f108,f29])).

fof(f108,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))) ),
    inference(forward_demodulation,[],[f107,f29])).

fof(f107,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))) ),
    inference(forward_demodulation,[],[f106,f29])).

fof(f106,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k2_xboole_0(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k1_tarski(sK5))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))) ),
    inference(forward_demodulation,[],[f105,f29])).

fof(f105,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k2_xboole_0(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k1_tarski(sK5))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))))) ),
    inference(forward_demodulation,[],[f104,f29])).

fof(f104,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k2_xboole_0(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k1_tarski(sK5))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))) ),
    inference(forward_demodulation,[],[f51,f29])).

fof(f51,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k2_xboole_0(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k1_tarski(sK5))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))) ),
    inference(definition_unfolding,[],[f27,f49,f50,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(X3)) ),
    inference(definition_unfolding,[],[f34,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f32,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k2_xboole_0(k2_xboole_0(k1_tarski(X3),k1_tarski(X4)),k1_tarski(X5))) ),
    inference(definition_unfolding,[],[f35,f48,f48])).

fof(f35,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

fof(f27,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f14,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))
   => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:02:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (26020)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.51  % (26027)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.52  % (26012)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (26036)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (26012)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f131,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f130])).
% 0.20/0.52  fof(f130,plain,(
% 0.20/0.52    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))))))),
% 0.20/0.52    inference(forward_demodulation,[],[f129,f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.20/0.52  fof(f129,plain,(
% 0.20/0.52    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))),
% 0.20/0.52    inference(superposition,[],[f108,f29])).
% 0.20/0.52  fof(f108,plain,(
% 0.20/0.52    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))))),
% 0.20/0.52    inference(forward_demodulation,[],[f107,f29])).
% 0.20/0.52  fof(f107,plain,(
% 0.20/0.52    k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))))))),
% 0.20/0.52    inference(forward_demodulation,[],[f106,f29])).
% 0.20/0.52  fof(f106,plain,(
% 0.20/0.52    k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k2_xboole_0(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k1_tarski(sK5))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))))))),
% 0.20/0.52    inference(forward_demodulation,[],[f105,f29])).
% 0.20/0.52  fof(f105,plain,(
% 0.20/0.52    k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k2_xboole_0(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k1_tarski(sK5))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))),
% 0.20/0.52    inference(forward_demodulation,[],[f104,f29])).
% 0.20/0.52  fof(f104,plain,(
% 0.20/0.52    k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k2_xboole_0(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k1_tarski(sK5))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))))),
% 0.20/0.52    inference(forward_demodulation,[],[f51,f29])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k2_xboole_0(k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4)),k1_tarski(sK5))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))),
% 0.20/0.52    inference(definition_unfolding,[],[f27,f49,f50,f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(X3))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f34,f48])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f32,f33])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k2_xboole_0(k2_xboole_0(k1_tarski(X3),k1_tarski(X4)),k1_tarski(X5)))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f35,f48,f48])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5))),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f14,f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))),
% 0.20/0.52    inference(negated_conjecture,[],[f11])).
% 0.20/0.52  fof(f11,conjecture,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (26012)------------------------------
% 0.20/0.52  % (26012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (26012)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (26012)Memory used [KB]: 1791
% 0.20/0.52  % (26012)Time elapsed: 0.106 s
% 0.20/0.52  % (26012)------------------------------
% 0.20/0.52  % (26012)------------------------------
% 0.20/0.52  % (26036)Refutation not found, incomplete strategy% (26036)------------------------------
% 0.20/0.52  % (26036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (26036)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (26036)Memory used [KB]: 1663
% 0.20/0.52  % (26036)Time elapsed: 0.005 s
% 0.20/0.52  % (26036)------------------------------
% 0.20/0.52  % (26036)------------------------------
% 0.20/0.52  % (26006)Success in time 0.166 s
%------------------------------------------------------------------------------
