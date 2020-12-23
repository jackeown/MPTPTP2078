%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:50 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   36 ( 247 expanded)
%              Number of leaves         :    5 (  80 expanded)
%              Depth                    :   15
%              Number of atoms          :   68 ( 477 expanded)
%              Number of equality atoms :   67 ( 476 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f49,plain,(
    $false ),
    inference(subsumption_resolution,[],[f48,f44])).

fof(f44,plain,(
    sK0 != sK4 ),
    inference(subsumption_resolution,[],[f34,f43])).

fof(f43,plain,(
    sK1 = sK5 ),
    inference(forward_demodulation,[],[f39,f12])).

fof(f12,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f39,plain,(
    sK5 = k2_mcart_1(k4_tarski(sK0,sK1)) ),
    inference(superposition,[],[f12,f32])).

fof(f32,plain,(
    k4_tarski(sK4,sK5) = k4_tarski(sK0,sK1) ),
    inference(forward_demodulation,[],[f30,f17])).

fof(f17,plain,(
    ! [X4,X5,X3] : k4_tarski(X3,X4) = k1_mcart_1(k3_mcart_1(X3,X4,X5)) ),
    inference(superposition,[],[f11,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f11,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f30,plain,(
    k4_tarski(sK4,sK5) = k1_mcart_1(k3_mcart_1(sK0,sK1,sK2)) ),
    inference(superposition,[],[f17,f29])).

fof(f29,plain,(
    k3_mcart_1(sK4,sK5,sK6) = k3_mcart_1(sK0,sK1,sK2) ),
    inference(forward_demodulation,[],[f28,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k3_mcart_1(X0,X1,X2) = k1_mcart_1(k4_mcart_1(X0,X1,X2,X3)) ),
    inference(forward_demodulation,[],[f20,f13])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k1_mcart_1(k4_mcart_1(X0,X1,X2,X3)) ),
    inference(superposition,[],[f17,f14])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k3_mcart_1(k4_tarski(X0,X1),X2,X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k3_mcart_1(k4_tarski(X0,X1),X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_mcart_1)).

fof(f28,plain,(
    k3_mcart_1(sK4,sK5,sK6) = k1_mcart_1(k4_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(superposition,[],[f22,f26])).

fof(f26,plain,(
    k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK3) ),
    inference(backward_demodulation,[],[f9,f24])).

fof(f24,plain,(
    sK3 = sK7 ),
    inference(forward_demodulation,[],[f23,f21])).

% (13081)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f21,plain,(
    ! [X6,X4,X7,X5] : k2_mcart_1(k4_mcart_1(X4,X5,X6,X7)) = X7 ),
    inference(superposition,[],[f16,f14])).

fof(f16,plain,(
    ! [X2,X0,X1] : k2_mcart_1(k3_mcart_1(X0,X1,X2)) = X2 ),
    inference(superposition,[],[f12,f13])).

fof(f23,plain,(
    sK7 = k2_mcart_1(k4_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(superposition,[],[f21,f9])).

fof(f9,plain,(
    k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,
    ( ( sK3 != sK7
      | sK2 != sK6
      | sK1 != sK5
      | sK0 != sK4 )
    & k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f6,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( X3 != X7
          | X2 != X6
          | X1 != X5
          | X0 != X4 )
        & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) )
   => ( ( sK3 != sK7
        | sK2 != sK6
        | sK1 != sK5
        | sK0 != sK4 )
      & k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7) ) ),
    introduced(choice_axiom,[])).

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

fof(f4,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)
     => ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_mcart_1)).

fof(f34,plain,
    ( sK1 != sK5
    | sK0 != sK4 ),
    inference(subsumption_resolution,[],[f25,f33])).

fof(f33,plain,(
    sK2 = sK6 ),
    inference(forward_demodulation,[],[f31,f16])).

fof(f31,plain,(
    sK6 = k2_mcart_1(k3_mcart_1(sK0,sK1,sK2)) ),
    inference(superposition,[],[f16,f29])).

fof(f25,plain,
    ( sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(subsumption_resolution,[],[f10,f24])).

fof(f10,plain,
    ( sK3 != sK7
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(cnf_transformation,[],[f8])).

fof(f48,plain,(
    sK0 = sK4 ),
    inference(forward_demodulation,[],[f40,f11])).

fof(f40,plain,(
    sK4 = k1_mcart_1(k4_tarski(sK0,sK1)) ),
    inference(superposition,[],[f11,f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:50:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.48  % (13071)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.18/0.49  % (13071)Refutation found. Thanks to Tanya!
% 0.18/0.49  % SZS status Theorem for theBenchmark
% 0.18/0.49  % (13064)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.18/0.49  % SZS output start Proof for theBenchmark
% 0.18/0.49  fof(f49,plain,(
% 0.18/0.49    $false),
% 0.18/0.49    inference(subsumption_resolution,[],[f48,f44])).
% 0.18/0.49  fof(f44,plain,(
% 0.18/0.49    sK0 != sK4),
% 0.18/0.49    inference(subsumption_resolution,[],[f34,f43])).
% 0.18/0.49  fof(f43,plain,(
% 0.18/0.49    sK1 = sK5),
% 0.18/0.49    inference(forward_demodulation,[],[f39,f12])).
% 0.18/0.49  fof(f12,plain,(
% 0.18/0.49    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.18/0.49    inference(cnf_transformation,[],[f3])).
% 0.18/0.49  fof(f3,axiom,(
% 0.18/0.49    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.18/0.49  fof(f39,plain,(
% 0.18/0.49    sK5 = k2_mcart_1(k4_tarski(sK0,sK1))),
% 0.18/0.49    inference(superposition,[],[f12,f32])).
% 0.18/0.49  fof(f32,plain,(
% 0.18/0.49    k4_tarski(sK4,sK5) = k4_tarski(sK0,sK1)),
% 0.18/0.49    inference(forward_demodulation,[],[f30,f17])).
% 0.18/0.49  fof(f17,plain,(
% 0.18/0.49    ( ! [X4,X5,X3] : (k4_tarski(X3,X4) = k1_mcart_1(k3_mcart_1(X3,X4,X5))) )),
% 0.18/0.49    inference(superposition,[],[f11,f13])).
% 0.18/0.49  fof(f13,plain,(
% 0.18/0.49    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f1])).
% 0.18/0.49  fof(f1,axiom,(
% 0.18/0.49    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.18/0.49  fof(f11,plain,(
% 0.18/0.49    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.18/0.49    inference(cnf_transformation,[],[f3])).
% 0.18/0.49  fof(f30,plain,(
% 0.18/0.49    k4_tarski(sK4,sK5) = k1_mcart_1(k3_mcart_1(sK0,sK1,sK2))),
% 0.18/0.49    inference(superposition,[],[f17,f29])).
% 0.18/0.49  fof(f29,plain,(
% 0.18/0.49    k3_mcart_1(sK4,sK5,sK6) = k3_mcart_1(sK0,sK1,sK2)),
% 0.18/0.49    inference(forward_demodulation,[],[f28,f22])).
% 0.18/0.49  fof(f22,plain,(
% 0.18/0.49    ( ! [X2,X0,X3,X1] : (k3_mcart_1(X0,X1,X2) = k1_mcart_1(k4_mcart_1(X0,X1,X2,X3))) )),
% 0.18/0.49    inference(forward_demodulation,[],[f20,f13])).
% 0.18/0.49  fof(f20,plain,(
% 0.18/0.49    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(X0,X1),X2) = k1_mcart_1(k4_mcart_1(X0,X1,X2,X3))) )),
% 0.18/0.49    inference(superposition,[],[f17,f14])).
% 0.18/0.49  fof(f14,plain,(
% 0.18/0.49    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k3_mcart_1(k4_tarski(X0,X1),X2,X3)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f2])).
% 0.18/0.49  fof(f2,axiom,(
% 0.18/0.49    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k3_mcart_1(k4_tarski(X0,X1),X2,X3)),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_mcart_1)).
% 0.18/0.49  fof(f28,plain,(
% 0.18/0.49    k3_mcart_1(sK4,sK5,sK6) = k1_mcart_1(k4_mcart_1(sK0,sK1,sK2,sK3))),
% 0.18/0.49    inference(superposition,[],[f22,f26])).
% 0.18/0.49  fof(f26,plain,(
% 0.18/0.49    k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK3)),
% 0.18/0.49    inference(backward_demodulation,[],[f9,f24])).
% 0.18/0.49  fof(f24,plain,(
% 0.18/0.49    sK3 = sK7),
% 0.18/0.49    inference(forward_demodulation,[],[f23,f21])).
% 0.18/0.50  % (13081)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.18/0.50  fof(f21,plain,(
% 0.18/0.50    ( ! [X6,X4,X7,X5] : (k2_mcart_1(k4_mcart_1(X4,X5,X6,X7)) = X7) )),
% 0.18/0.50    inference(superposition,[],[f16,f14])).
% 0.18/0.50  fof(f16,plain,(
% 0.18/0.50    ( ! [X2,X0,X1] : (k2_mcart_1(k3_mcart_1(X0,X1,X2)) = X2) )),
% 0.18/0.50    inference(superposition,[],[f12,f13])).
% 0.18/0.50  fof(f23,plain,(
% 0.18/0.50    sK7 = k2_mcart_1(k4_mcart_1(sK0,sK1,sK2,sK3))),
% 0.18/0.50    inference(superposition,[],[f21,f9])).
% 0.18/0.50  fof(f9,plain,(
% 0.18/0.50    k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7)),
% 0.18/0.50    inference(cnf_transformation,[],[f8])).
% 0.18/0.50  fof(f8,plain,(
% 0.18/0.50    (sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7)),
% 0.18/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f6,f7])).
% 0.18/0.50  fof(f7,plain,(
% 0.18/0.50    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)) => ((sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k4_mcart_1(sK0,sK1,sK2,sK3) = k4_mcart_1(sK4,sK5,sK6,sK7))),
% 0.18/0.50    introduced(choice_axiom,[])).
% 0.18/0.50  fof(f6,plain,(
% 0.18/0.50    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7))),
% 0.18/0.50    inference(ennf_transformation,[],[f5])).
% 0.18/0.50  fof(f5,negated_conjecture,(
% 0.18/0.50    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) => (X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4))),
% 0.18/0.50    inference(negated_conjecture,[],[f4])).
% 0.18/0.50  fof(f4,conjecture,(
% 0.18/0.50    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) => (X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4))),
% 0.18/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_mcart_1)).
% 0.18/0.50  fof(f34,plain,(
% 0.18/0.50    sK1 != sK5 | sK0 != sK4),
% 0.18/0.50    inference(subsumption_resolution,[],[f25,f33])).
% 0.18/0.50  fof(f33,plain,(
% 0.18/0.50    sK2 = sK6),
% 0.18/0.50    inference(forward_demodulation,[],[f31,f16])).
% 0.18/0.50  fof(f31,plain,(
% 0.18/0.50    sK6 = k2_mcart_1(k3_mcart_1(sK0,sK1,sK2))),
% 0.18/0.50    inference(superposition,[],[f16,f29])).
% 0.18/0.50  fof(f25,plain,(
% 0.18/0.50    sK2 != sK6 | sK1 != sK5 | sK0 != sK4),
% 0.18/0.50    inference(subsumption_resolution,[],[f10,f24])).
% 0.18/0.50  fof(f10,plain,(
% 0.18/0.50    sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4),
% 0.18/0.50    inference(cnf_transformation,[],[f8])).
% 0.18/0.50  fof(f48,plain,(
% 0.18/0.50    sK0 = sK4),
% 0.18/0.50    inference(forward_demodulation,[],[f40,f11])).
% 0.18/0.50  fof(f40,plain,(
% 0.18/0.50    sK4 = k1_mcart_1(k4_tarski(sK0,sK1))),
% 0.18/0.50    inference(superposition,[],[f11,f32])).
% 0.18/0.50  % SZS output end Proof for theBenchmark
% 0.18/0.50  % (13071)------------------------------
% 0.18/0.50  % (13071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.50  % (13071)Termination reason: Refutation
% 0.18/0.50  
% 0.18/0.50  % (13071)Memory used [KB]: 6268
% 0.18/0.50  % (13071)Time elapsed: 0.096 s
% 0.18/0.50  % (13071)------------------------------
% 0.18/0.50  % (13071)------------------------------
% 0.18/0.50  % (13073)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.18/0.50  % (13063)Success in time 0.152 s
%------------------------------------------------------------------------------
