%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:50 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   36 ( 263 expanded)
%              Number of leaves         :    4 (  85 expanded)
%              Depth                    :   15
%              Number of atoms          :   58 ( 402 expanded)
%              Number of equality atoms :   57 ( 401 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f84,plain,(
    $false ),
    inference(global_subsumption,[],[f82,f83])).

fof(f83,plain,(
    sK0 = sK4 ),
    inference(forward_demodulation,[],[f73,f9])).

fof(f9,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f73,plain,(
    sK4 = k1_mcart_1(k4_tarski(sK0,sK1)) ),
    inference(superposition,[],[f9,f62])).

fof(f62,plain,(
    k4_tarski(sK4,sK5) = k4_tarski(sK0,sK1) ),
    inference(forward_demodulation,[],[f60,f32])).

fof(f32,plain,(
    ! [X4,X5,X3] : k4_tarski(X3,X4) = k1_mcart_1(k3_mcart_1(X3,X4,X5)) ),
    inference(superposition,[],[f9,f27])).

fof(f27,plain,(
    ! [X6,X4,X5] : k4_tarski(k4_tarski(X4,X5),X6) = k3_mcart_1(X4,X5,X6) ),
    inference(forward_demodulation,[],[f25,f9])).

fof(f25,plain,(
    ! [X6,X4,X7,X5] : k4_tarski(k4_tarski(X4,X5),X6) = k1_mcart_1(k4_tarski(k3_mcart_1(X4,X5,X6),X7)) ),
    inference(superposition,[],[f9,f14])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f12,f11])).

fof(f11,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f12,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_mcart_1)).

fof(f60,plain,(
    k4_tarski(sK4,sK5) = k1_mcart_1(k3_mcart_1(sK0,sK1,sK2)) ),
    inference(superposition,[],[f32,f46])).

fof(f46,plain,(
    k3_mcart_1(sK0,sK1,sK2) = k3_mcart_1(sK4,sK5,sK2) ),
    inference(backward_demodulation,[],[f19,f44])).

fof(f44,plain,(
    sK2 = sK6 ),
    inference(forward_demodulation,[],[f42,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_mcart_1(k3_mcart_1(X0,X1,X2)) = X2 ),
    inference(superposition,[],[f10,f27])).

fof(f10,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f3])).

fof(f42,plain,(
    sK6 = k2_mcart_1(k3_mcart_1(sK0,sK1,sK2)) ),
    inference(superposition,[],[f31,f19])).

fof(f19,plain,(
    k3_mcart_1(sK0,sK1,sK2) = k3_mcart_1(sK4,sK5,sK6) ),
    inference(forward_demodulation,[],[f16,f9])).

fof(f16,plain,(
    k3_mcart_1(sK4,sK5,sK6) = k1_mcart_1(k4_tarski(k3_mcart_1(sK0,sK1,sK2),sK3)) ),
    inference(superposition,[],[f9,f13])).

fof(f13,plain,(
    k4_tarski(k3_mcart_1(sK0,sK1,sK2),sK3) = k4_tarski(k3_mcart_1(sK4,sK5,sK6),sK7) ),
    inference(definition_unfolding,[],[f8,f11,f11])).

fof(f8,plain,(
    k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)
       => ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 ) ) ),
    inference(negated_conjecture,[],[f4])).

% (26983)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f4,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)
     => ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_mcart_1)).

fof(f82,plain,(
    sK0 != sK4 ),
    inference(global_subsumption,[],[f49,f76])).

fof(f76,plain,(
    sK1 = sK5 ),
    inference(forward_demodulation,[],[f72,f10])).

fof(f72,plain,(
    sK5 = k2_mcart_1(k4_tarski(sK0,sK1)) ),
    inference(superposition,[],[f10,f62])).

fof(f49,plain,
    ( sK1 != sK5
    | sK0 != sK4 ),
    inference(global_subsumption,[],[f17,f48])).

fof(f48,plain,
    ( sK3 != sK7
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(trivial_inequality_removal,[],[f47])).

fof(f47,plain,
    ( sK2 != sK2
    | sK3 != sK7
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(backward_demodulation,[],[f7,f44])).

fof(f7,plain,
    ( sK3 != sK7
    | sK1 != sK5
    | sK2 != sK6
    | sK0 != sK4 ),
    inference(cnf_transformation,[],[f6])).

fof(f17,plain,(
    sK3 = sK7 ),
    inference(forward_demodulation,[],[f15,f10])).

fof(f15,plain,(
    sK7 = k2_mcart_1(k4_tarski(k3_mcart_1(sK0,sK1,sK2),sK3)) ),
    inference(superposition,[],[f10,f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:41:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.50  % (26973)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (26984)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (26997)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.51  % (27000)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.51  % (26973)Refutation not found, incomplete strategy% (26973)------------------------------
% 0.20/0.51  % (26973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (26989)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % (26973)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (26973)Memory used [KB]: 1663
% 0.20/0.51  % (26973)Time elapsed: 0.093 s
% 0.20/0.51  % (26973)------------------------------
% 0.20/0.51  % (26973)------------------------------
% 0.20/0.51  % (26992)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.52  % (26997)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f84,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(global_subsumption,[],[f82,f83])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    sK0 = sK4),
% 0.20/0.52    inference(forward_demodulation,[],[f73,f9])).
% 0.20/0.52  fof(f9,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    sK4 = k1_mcart_1(k4_tarski(sK0,sK1))),
% 0.20/0.52    inference(superposition,[],[f9,f62])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    k4_tarski(sK4,sK5) = k4_tarski(sK0,sK1)),
% 0.20/0.52    inference(forward_demodulation,[],[f60,f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X4,X5,X3] : (k4_tarski(X3,X4) = k1_mcart_1(k3_mcart_1(X3,X4,X5))) )),
% 0.20/0.52    inference(superposition,[],[f9,f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ( ! [X6,X4,X5] : (k4_tarski(k4_tarski(X4,X5),X6) = k3_mcart_1(X4,X5,X6)) )),
% 0.20/0.52    inference(forward_demodulation,[],[f25,f9])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ( ! [X6,X4,X7,X5] : (k4_tarski(k4_tarski(X4,X5),X6) = k1_mcart_1(k4_tarski(k3_mcart_1(X4,X5,X6),X7))) )),
% 0.20/0.52    inference(superposition,[],[f9,f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f12,f11])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_mcart_1)).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    k4_tarski(sK4,sK5) = k1_mcart_1(k3_mcart_1(sK0,sK1,sK2))),
% 0.20/0.52    inference(superposition,[],[f32,f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    k3_mcart_1(sK0,sK1,sK2) = k3_mcart_1(sK4,sK5,sK2)),
% 0.20/0.52    inference(backward_demodulation,[],[f19,f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    sK2 = sK6),
% 0.20/0.52    inference(forward_demodulation,[],[f42,f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k2_mcart_1(k3_mcart_1(X0,X1,X2)) = X2) )),
% 0.20/0.52    inference(superposition,[],[f10,f27])).
% 0.20/0.52  fof(f10,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    sK6 = k2_mcart_1(k3_mcart_1(sK0,sK1,sK2))),
% 0.20/0.52    inference(superposition,[],[f31,f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    k3_mcart_1(sK0,sK1,sK2) = k3_mcart_1(sK4,sK5,sK6)),
% 0.20/0.52    inference(forward_demodulation,[],[f16,f9])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    k3_mcart_1(sK4,sK5,sK6) = k1_mcart_1(k4_tarski(k3_mcart_1(sK0,sK1,sK2),sK3))),
% 0.20/0.52    inference(superposition,[],[f9,f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    k4_tarski(k3_mcart_1(sK0,sK1,sK2),sK3) = k4_tarski(k3_mcart_1(sK4,sK5,sK6),sK7)),
% 0.20/0.52    inference(definition_unfolding,[],[f8,f11,f11])).
% 0.20/0.52  fof(f8,plain,(
% 0.20/0.52    k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7)),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) => (X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4))),
% 0.20/0.52    inference(negated_conjecture,[],[f4])).
% 0.20/0.52  % (26983)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  fof(f4,conjecture,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) => (X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_mcart_1)).
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    sK0 != sK4),
% 0.20/0.52    inference(global_subsumption,[],[f49,f76])).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    sK1 = sK5),
% 0.20/0.52    inference(forward_demodulation,[],[f72,f10])).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    sK5 = k2_mcart_1(k4_tarski(sK0,sK1))),
% 0.20/0.52    inference(superposition,[],[f10,f62])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    sK1 != sK5 | sK0 != sK4),
% 0.20/0.52    inference(global_subsumption,[],[f17,f48])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    sK3 != sK7 | sK1 != sK5 | sK0 != sK4),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f47])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    sK2 != sK2 | sK3 != sK7 | sK1 != sK5 | sK0 != sK4),
% 0.20/0.52    inference(backward_demodulation,[],[f7,f44])).
% 0.20/0.52  fof(f7,plain,(
% 0.20/0.52    sK3 != sK7 | sK1 != sK5 | sK2 != sK6 | sK0 != sK4),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    sK3 = sK7),
% 0.20/0.52    inference(forward_demodulation,[],[f15,f10])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    sK7 = k2_mcart_1(k4_tarski(k3_mcart_1(sK0,sK1,sK2),sK3))),
% 0.20/0.52    inference(superposition,[],[f10,f13])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (26997)------------------------------
% 0.20/0.52  % (26997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (26997)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (26997)Memory used [KB]: 6268
% 0.20/0.52  % (26997)Time elapsed: 0.101 s
% 0.20/0.52  % (26997)------------------------------
% 0.20/0.52  % (26997)------------------------------
% 0.20/0.52  % (26995)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (26983)Refutation not found, incomplete strategy% (26983)------------------------------
% 0.20/0.52  % (26983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (26983)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (26983)Memory used [KB]: 10618
% 0.20/0.52  % (26983)Time elapsed: 0.107 s
% 0.20/0.52  % (26983)------------------------------
% 0.20/0.52  % (26983)------------------------------
% 0.20/0.52  % (26972)Success in time 0.159 s
%------------------------------------------------------------------------------
