%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:54 EST 2020

% Result     : Theorem 16.35s
% Output     : Refutation 16.74s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 319 expanded)
%              Number of leaves         :    9 ( 100 expanded)
%              Depth                    :   14
%              Number of atoms          :   84 ( 393 expanded)
%              Number of equality atoms :   65 ( 286 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f36956,plain,(
    $false ),
    inference(subsumption_resolution,[],[f15,f36955])).

fof(f36955,plain,(
    ! [X30,X28,X29] : k2_xboole_0(k4_xboole_0(X29,X28),k4_xboole_0(X30,X28)) = k4_xboole_0(k2_xboole_0(X29,X30),X28) ),
    inference(forward_demodulation,[],[f36704,f25262])).

fof(f25262,plain,(
    ! [X57,X56,X55] : k2_xboole_0(k4_xboole_0(X57,k2_xboole_0(X56,X55)),k4_xboole_0(X55,X56)) = k4_xboole_0(k2_xboole_0(X55,X57),X56) ),
    inference(backward_demodulation,[],[f19240,f25209])).

fof(f25209,plain,(
    ! [X33,X31,X32] : k4_xboole_0(k2_xboole_0(X31,X32),X33) = k2_xboole_0(k4_xboole_0(X32,X33),k4_xboole_0(X31,X33)) ),
    inference(backward_demodulation,[],[f7211,f25112])).

fof(f25112,plain,(
    ! [X4,X5,X3] : k4_xboole_0(k2_xboole_0(X5,X3),X4) = k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(k2_xboole_0(X5,X3),X4)) ),
    inference(resolution,[],[f13539,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f13539,plain,(
    ! [X97,X95,X96] : r1_tarski(k4_xboole_0(X95,X96),k4_xboole_0(k2_xboole_0(X97,X95),X96)) ),
    inference(trivial_inequality_removal,[],[f13475])).

fof(f13475,plain,(
    ! [X97,X95,X96] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k4_xboole_0(X95,X96),k4_xboole_0(k2_xboole_0(X97,X95),X96)) ) ),
    inference(superposition,[],[f140,f395])).

fof(f395,plain,(
    ! [X6,X7,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k2_xboole_0(X7,X5))) ),
    inference(superposition,[],[f52,f48])).

fof(f48,plain,(
    ! [X6,X4,X5,X3] : k4_xboole_0(X3,k2_xboole_0(k2_xboole_0(X4,X5),X6)) = k4_xboole_0(X3,k2_xboole_0(X4,k2_xboole_0(X5,X6))) ),
    inference(forward_demodulation,[],[f47,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f47,plain,(
    ! [X6,X4,X5,X3] : k4_xboole_0(k4_xboole_0(X3,X4),k2_xboole_0(X5,X6)) = k4_xboole_0(X3,k2_xboole_0(k2_xboole_0(X4,X5),X6)) ),
    inference(forward_demodulation,[],[f41,f23])).

fof(f41,plain,(
    ! [X6,X4,X5,X3] : k4_xboole_0(k4_xboole_0(X3,X4),k2_xboole_0(X5,X6)) = k4_xboole_0(k4_xboole_0(X3,k2_xboole_0(X4,X5)),X6) ),
    inference(superposition,[],[f23,f23])).

fof(f52,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f25,f23])).

fof(f25,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f22,f16])).

fof(f16,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f140,plain,(
    ! [X6,X8,X7] :
      ( k1_xboole_0 != k4_xboole_0(X8,k2_xboole_0(X6,X7))
      | r1_tarski(k4_xboole_0(X8,X6),k4_xboole_0(X7,X6)) ) ),
    inference(superposition,[],[f44,f18])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f44,plain,(
    ! [X6,X8,X7] :
      ( k1_xboole_0 != k4_xboole_0(X6,k2_xboole_0(X7,X8))
      | r1_tarski(k4_xboole_0(X6,X7),X8) ) ),
    inference(superposition,[],[f21,f23])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7211,plain,(
    ! [X33,X31,X32] : k2_xboole_0(k4_xboole_0(X32,X33),k4_xboole_0(k2_xboole_0(X31,X32),X33)) = k2_xboole_0(k4_xboole_0(X32,X33),k4_xboole_0(X31,X33)) ),
    inference(forward_demodulation,[],[f7044,f185])).

fof(f185,plain,(
    ! [X6,X8,X7] : k2_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X8,X6)) = k2_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X8,k2_xboole_0(X6,X7))) ),
    inference(superposition,[],[f43,f18])).

fof(f43,plain,(
    ! [X4,X5,X3] : k2_xboole_0(X5,k4_xboole_0(X3,X4)) = k2_xboole_0(X5,k4_xboole_0(X3,k2_xboole_0(X4,X5))) ),
    inference(superposition,[],[f18,f23])).

fof(f7044,plain,(
    ! [X33,X31,X32] : k2_xboole_0(k4_xboole_0(X32,X33),k4_xboole_0(k2_xboole_0(X31,X32),X33)) = k2_xboole_0(k4_xboole_0(X32,X33),k4_xboole_0(X31,k2_xboole_0(X33,X32))) ),
    inference(superposition,[],[f185,f219])).

fof(f219,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X2,k2_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X2,X0),k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f46,f17])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f46,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f40,f23])).

fof(f40,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) ),
    inference(superposition,[],[f23,f19])).

fof(f19,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f19240,plain,(
    ! [X57,X56,X55] : k2_xboole_0(k4_xboole_0(X57,k2_xboole_0(X56,X55)),k4_xboole_0(X55,X56)) = k2_xboole_0(k4_xboole_0(X57,X56),k4_xboole_0(X55,X56)) ),
    inference(forward_demodulation,[],[f16976,f830])).

fof(f830,plain,(
    ! [X24,X25] : k2_xboole_0(X25,X24) = k4_xboole_0(k2_xboole_0(X24,X25),k1_xboole_0) ),
    inference(backward_demodulation,[],[f423,f828])).

fof(f828,plain,(
    ! [X7] : k4_xboole_0(X7,k1_xboole_0) = X7 ),
    inference(forward_demodulation,[],[f797,f91])).

fof(f91,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(resolution,[],[f73,f20])).

fof(f73,plain,(
    ! [X5] : r1_tarski(k1_xboole_0,X5) ),
    inference(forward_demodulation,[],[f72,f34])).

fof(f34,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2 ),
    inference(superposition,[],[f24,f17])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(resolution,[],[f20,f16])).

fof(f72,plain,(
    ! [X6,X5] : r1_tarski(k1_xboole_0,k2_xboole_0(X5,k4_xboole_0(X5,X6))) ),
    inference(forward_demodulation,[],[f65,f17])).

fof(f65,plain,(
    ! [X6,X5] : r1_tarski(k1_xboole_0,k2_xboole_0(k4_xboole_0(X5,X6),X5)) ),
    inference(superposition,[],[f31,f25])).

fof(f31,plain,(
    ! [X4,X5] : r1_tarski(k4_xboole_0(X4,X5),k2_xboole_0(X4,X5)) ),
    inference(superposition,[],[f16,f19])).

fof(f797,plain,(
    ! [X7] : k4_xboole_0(X7,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X7) ),
    inference(superposition,[],[f101,f60])).

fof(f60,plain,(
    ! [X5] : k2_xboole_0(X5,k1_xboole_0) = X5 ),
    inference(forward_demodulation,[],[f55,f34])).

fof(f55,plain,(
    ! [X6,X5] : k2_xboole_0(X5,k4_xboole_0(X5,X6)) = k2_xboole_0(X5,k1_xboole_0) ),
    inference(superposition,[],[f18,f25])).

fof(f101,plain,(
    ! [X4,X5] : k2_xboole_0(k4_xboole_0(X5,X4),X4) = k2_xboole_0(X4,X5) ),
    inference(forward_demodulation,[],[f95,f82])).

fof(f82,plain,(
    ! [X10,X11] : k2_xboole_0(X10,X11) = k2_xboole_0(k4_xboole_0(X11,X10),k2_xboole_0(X10,X11)) ),
    inference(superposition,[],[f24,f26])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[],[f19,f17])).

fof(f95,plain,(
    ! [X4,X5] : k2_xboole_0(k4_xboole_0(X5,X4),X4) = k2_xboole_0(k4_xboole_0(X5,X4),k2_xboole_0(X4,X5)) ),
    inference(superposition,[],[f32,f18])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f29,f18])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f18,f19])).

fof(f423,plain,(
    ! [X24,X25] : k4_xboole_0(k2_xboole_0(X25,X24),k1_xboole_0) = k4_xboole_0(k2_xboole_0(X24,X25),k1_xboole_0) ),
    inference(forward_demodulation,[],[f422,f32])).

fof(f422,plain,(
    ! [X24,X25] : k4_xboole_0(k2_xboole_0(X25,X24),k1_xboole_0) = k4_xboole_0(k2_xboole_0(X24,k2_xboole_0(X25,X24)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f407,f17])).

fof(f407,plain,(
    ! [X24,X25] : k4_xboole_0(k2_xboole_0(X25,X24),k1_xboole_0) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X25,X24),X24),k1_xboole_0) ),
    inference(superposition,[],[f28,f52])).

fof(f28,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X5,X4)) = k4_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4)) ),
    inference(superposition,[],[f19,f18])).

fof(f16976,plain,(
    ! [X57,X56,X55] : k2_xboole_0(k4_xboole_0(X57,k2_xboole_0(X56,X55)),k4_xboole_0(X55,X56)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X55,X56),k4_xboole_0(X57,X56)),k1_xboole_0) ),
    inference(superposition,[],[f830,f185])).

fof(f36704,plain,(
    ! [X30,X28,X29] : k2_xboole_0(k4_xboole_0(X29,X28),k4_xboole_0(X30,X28)) = k2_xboole_0(k4_xboole_0(X30,k2_xboole_0(X28,X29)),k4_xboole_0(X29,X28)) ),
    inference(superposition,[],[f791,f18])).

fof(f791,plain,(
    ! [X24,X23,X22] : k2_xboole_0(X24,k4_xboole_0(X22,X23)) = k2_xboole_0(k4_xboole_0(X22,k2_xboole_0(X23,X24)),X24) ),
    inference(superposition,[],[f101,f23])).

fof(f15,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
   => k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:48:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.42  % (840)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.42  % (841)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.44  % (837)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.22/0.44  % (836)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.22/0.45  % (843)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.22/0.46  % (839)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.47  % (838)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.22/0.47  % (842)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.48  % (846)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.22/0.48  % (845)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.22/0.48  % (835)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.22/0.49  % (844)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 5.00/1.02  % (836)Time limit reached!
% 5.00/1.02  % (836)------------------------------
% 5.00/1.02  % (836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.00/1.02  % (836)Termination reason: Time limit
% 5.00/1.02  % (836)Termination phase: Saturation
% 5.00/1.02  
% 5.00/1.02  % (836)Memory used [KB]: 27888
% 5.00/1.02  % (836)Time elapsed: 0.600 s
% 5.00/1.02  % (836)------------------------------
% 5.00/1.02  % (836)------------------------------
% 8.01/1.42  % (835)Time limit reached!
% 8.01/1.42  % (835)------------------------------
% 8.01/1.42  % (835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.01/1.42  % (835)Termination reason: Time limit
% 8.01/1.42  % (835)Termination phase: Saturation
% 8.01/1.42  
% 8.01/1.42  % (835)Memory used [KB]: 38506
% 8.01/1.42  % (835)Time elapsed: 1.0000 s
% 8.01/1.42  % (835)------------------------------
% 8.01/1.42  % (835)------------------------------
% 16.35/2.44  % (846)Refutation found. Thanks to Tanya!
% 16.35/2.44  % SZS status Theorem for theBenchmark
% 16.74/2.45  % SZS output start Proof for theBenchmark
% 16.74/2.45  fof(f36956,plain,(
% 16.74/2.45    $false),
% 16.74/2.45    inference(subsumption_resolution,[],[f15,f36955])).
% 16.74/2.45  fof(f36955,plain,(
% 16.74/2.45    ( ! [X30,X28,X29] : (k2_xboole_0(k4_xboole_0(X29,X28),k4_xboole_0(X30,X28)) = k4_xboole_0(k2_xboole_0(X29,X30),X28)) )),
% 16.74/2.45    inference(forward_demodulation,[],[f36704,f25262])).
% 16.74/2.45  fof(f25262,plain,(
% 16.74/2.45    ( ! [X57,X56,X55] : (k2_xboole_0(k4_xboole_0(X57,k2_xboole_0(X56,X55)),k4_xboole_0(X55,X56)) = k4_xboole_0(k2_xboole_0(X55,X57),X56)) )),
% 16.74/2.45    inference(backward_demodulation,[],[f19240,f25209])).
% 16.74/2.45  fof(f25209,plain,(
% 16.74/2.45    ( ! [X33,X31,X32] : (k4_xboole_0(k2_xboole_0(X31,X32),X33) = k2_xboole_0(k4_xboole_0(X32,X33),k4_xboole_0(X31,X33))) )),
% 16.74/2.45    inference(backward_demodulation,[],[f7211,f25112])).
% 16.74/2.45  fof(f25112,plain,(
% 16.74/2.45    ( ! [X4,X5,X3] : (k4_xboole_0(k2_xboole_0(X5,X3),X4) = k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(k2_xboole_0(X5,X3),X4))) )),
% 16.74/2.45    inference(resolution,[],[f13539,f20])).
% 16.74/2.45  fof(f20,plain,(
% 16.74/2.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 16.74/2.45    inference(cnf_transformation,[],[f11])).
% 16.74/2.45  fof(f11,plain,(
% 16.74/2.45    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 16.74/2.45    inference(ennf_transformation,[],[f3])).
% 16.74/2.45  fof(f3,axiom,(
% 16.74/2.45    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 16.74/2.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 16.74/2.45  fof(f13539,plain,(
% 16.74/2.45    ( ! [X97,X95,X96] : (r1_tarski(k4_xboole_0(X95,X96),k4_xboole_0(k2_xboole_0(X97,X95),X96))) )),
% 16.74/2.45    inference(trivial_inequality_removal,[],[f13475])).
% 16.74/2.45  fof(f13475,plain,(
% 16.74/2.45    ( ! [X97,X95,X96] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k4_xboole_0(X95,X96),k4_xboole_0(k2_xboole_0(X97,X95),X96))) )),
% 16.74/2.45    inference(superposition,[],[f140,f395])).
% 16.74/2.45  fof(f395,plain,(
% 16.74/2.45    ( ! [X6,X7,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k2_xboole_0(X7,X5)))) )),
% 16.74/2.45    inference(superposition,[],[f52,f48])).
% 16.74/2.45  fof(f48,plain,(
% 16.74/2.45    ( ! [X6,X4,X5,X3] : (k4_xboole_0(X3,k2_xboole_0(k2_xboole_0(X4,X5),X6)) = k4_xboole_0(X3,k2_xboole_0(X4,k2_xboole_0(X5,X6)))) )),
% 16.74/2.45    inference(forward_demodulation,[],[f47,f23])).
% 16.74/2.45  fof(f23,plain,(
% 16.74/2.45    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 16.74/2.45    inference(cnf_transformation,[],[f7])).
% 16.74/2.45  fof(f7,axiom,(
% 16.74/2.45    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 16.74/2.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 16.74/2.45  fof(f47,plain,(
% 16.74/2.45    ( ! [X6,X4,X5,X3] : (k4_xboole_0(k4_xboole_0(X3,X4),k2_xboole_0(X5,X6)) = k4_xboole_0(X3,k2_xboole_0(k2_xboole_0(X4,X5),X6))) )),
% 16.74/2.45    inference(forward_demodulation,[],[f41,f23])).
% 16.74/2.45  fof(f41,plain,(
% 16.74/2.45    ( ! [X6,X4,X5,X3] : (k4_xboole_0(k4_xboole_0(X3,X4),k2_xboole_0(X5,X6)) = k4_xboole_0(k4_xboole_0(X3,k2_xboole_0(X4,X5)),X6)) )),
% 16.74/2.45    inference(superposition,[],[f23,f23])).
% 16.74/2.45  fof(f52,plain,(
% 16.74/2.45    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 16.74/2.45    inference(superposition,[],[f25,f23])).
% 16.74/2.45  fof(f25,plain,(
% 16.74/2.45    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 16.74/2.45    inference(resolution,[],[f22,f16])).
% 16.74/2.45  fof(f16,plain,(
% 16.74/2.45    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 16.74/2.45    inference(cnf_transformation,[],[f4])).
% 16.74/2.45  fof(f4,axiom,(
% 16.74/2.45    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 16.74/2.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 16.74/2.45  fof(f22,plain,(
% 16.74/2.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 16.74/2.45    inference(cnf_transformation,[],[f14])).
% 16.74/2.45  fof(f14,plain,(
% 16.74/2.45    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 16.74/2.45    inference(nnf_transformation,[],[f2])).
% 16.74/2.45  fof(f2,axiom,(
% 16.74/2.45    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 16.74/2.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 16.74/2.45  fof(f140,plain,(
% 16.74/2.45    ( ! [X6,X8,X7] : (k1_xboole_0 != k4_xboole_0(X8,k2_xboole_0(X6,X7)) | r1_tarski(k4_xboole_0(X8,X6),k4_xboole_0(X7,X6))) )),
% 16.74/2.45    inference(superposition,[],[f44,f18])).
% 16.74/2.45  fof(f18,plain,(
% 16.74/2.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 16.74/2.45    inference(cnf_transformation,[],[f5])).
% 16.74/2.45  fof(f5,axiom,(
% 16.74/2.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 16.74/2.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 16.74/2.45  fof(f44,plain,(
% 16.74/2.45    ( ! [X6,X8,X7] : (k1_xboole_0 != k4_xboole_0(X6,k2_xboole_0(X7,X8)) | r1_tarski(k4_xboole_0(X6,X7),X8)) )),
% 16.74/2.45    inference(superposition,[],[f21,f23])).
% 16.74/2.45  fof(f21,plain,(
% 16.74/2.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 16.74/2.45    inference(cnf_transformation,[],[f14])).
% 16.74/2.45  fof(f7211,plain,(
% 16.74/2.45    ( ! [X33,X31,X32] : (k2_xboole_0(k4_xboole_0(X32,X33),k4_xboole_0(k2_xboole_0(X31,X32),X33)) = k2_xboole_0(k4_xboole_0(X32,X33),k4_xboole_0(X31,X33))) )),
% 16.74/2.45    inference(forward_demodulation,[],[f7044,f185])).
% 16.74/2.45  fof(f185,plain,(
% 16.74/2.45    ( ! [X6,X8,X7] : (k2_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X8,X6)) = k2_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X8,k2_xboole_0(X6,X7)))) )),
% 16.74/2.45    inference(superposition,[],[f43,f18])).
% 16.74/2.45  fof(f43,plain,(
% 16.74/2.45    ( ! [X4,X5,X3] : (k2_xboole_0(X5,k4_xboole_0(X3,X4)) = k2_xboole_0(X5,k4_xboole_0(X3,k2_xboole_0(X4,X5)))) )),
% 16.74/2.45    inference(superposition,[],[f18,f23])).
% 16.74/2.45  fof(f7044,plain,(
% 16.74/2.45    ( ! [X33,X31,X32] : (k2_xboole_0(k4_xboole_0(X32,X33),k4_xboole_0(k2_xboole_0(X31,X32),X33)) = k2_xboole_0(k4_xboole_0(X32,X33),k4_xboole_0(X31,k2_xboole_0(X33,X32)))) )),
% 16.74/2.45    inference(superposition,[],[f185,f219])).
% 16.74/2.45  fof(f219,plain,(
% 16.74/2.45    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X2,X0),k2_xboole_0(X1,X0))) )),
% 16.74/2.45    inference(superposition,[],[f46,f17])).
% 16.74/2.45  fof(f17,plain,(
% 16.74/2.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 16.74/2.45    inference(cnf_transformation,[],[f1])).
% 16.74/2.45  fof(f1,axiom,(
% 16.74/2.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 16.74/2.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 16.74/2.45  fof(f46,plain,(
% 16.74/2.45    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2))) )),
% 16.74/2.45    inference(forward_demodulation,[],[f40,f23])).
% 16.74/2.45  fof(f40,plain,(
% 16.74/2.45    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2))) )),
% 16.74/2.45    inference(superposition,[],[f23,f19])).
% 16.74/2.45  fof(f19,plain,(
% 16.74/2.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 16.74/2.45    inference(cnf_transformation,[],[f6])).
% 16.74/2.45  fof(f6,axiom,(
% 16.74/2.45    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 16.74/2.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 16.74/2.45  fof(f19240,plain,(
% 16.74/2.45    ( ! [X57,X56,X55] : (k2_xboole_0(k4_xboole_0(X57,k2_xboole_0(X56,X55)),k4_xboole_0(X55,X56)) = k2_xboole_0(k4_xboole_0(X57,X56),k4_xboole_0(X55,X56))) )),
% 16.74/2.45    inference(forward_demodulation,[],[f16976,f830])).
% 16.74/2.45  fof(f830,plain,(
% 16.74/2.45    ( ! [X24,X25] : (k2_xboole_0(X25,X24) = k4_xboole_0(k2_xboole_0(X24,X25),k1_xboole_0)) )),
% 16.74/2.45    inference(backward_demodulation,[],[f423,f828])).
% 16.74/2.45  fof(f828,plain,(
% 16.74/2.45    ( ! [X7] : (k4_xboole_0(X7,k1_xboole_0) = X7) )),
% 16.74/2.45    inference(forward_demodulation,[],[f797,f91])).
% 16.74/2.45  fof(f91,plain,(
% 16.74/2.45    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 16.74/2.45    inference(resolution,[],[f73,f20])).
% 16.74/2.45  fof(f73,plain,(
% 16.74/2.45    ( ! [X5] : (r1_tarski(k1_xboole_0,X5)) )),
% 16.74/2.45    inference(forward_demodulation,[],[f72,f34])).
% 16.74/2.45  fof(f34,plain,(
% 16.74/2.45    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2) )),
% 16.74/2.45    inference(superposition,[],[f24,f17])).
% 16.74/2.45  fof(f24,plain,(
% 16.74/2.45    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 16.74/2.45    inference(resolution,[],[f20,f16])).
% 16.74/2.45  fof(f72,plain,(
% 16.74/2.45    ( ! [X6,X5] : (r1_tarski(k1_xboole_0,k2_xboole_0(X5,k4_xboole_0(X5,X6)))) )),
% 16.74/2.45    inference(forward_demodulation,[],[f65,f17])).
% 16.74/2.45  fof(f65,plain,(
% 16.74/2.45    ( ! [X6,X5] : (r1_tarski(k1_xboole_0,k2_xboole_0(k4_xboole_0(X5,X6),X5))) )),
% 16.74/2.45    inference(superposition,[],[f31,f25])).
% 16.74/2.45  fof(f31,plain,(
% 16.74/2.45    ( ! [X4,X5] : (r1_tarski(k4_xboole_0(X4,X5),k2_xboole_0(X4,X5))) )),
% 16.74/2.45    inference(superposition,[],[f16,f19])).
% 16.74/2.45  fof(f797,plain,(
% 16.74/2.45    ( ! [X7] : (k4_xboole_0(X7,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X7)) )),
% 16.74/2.45    inference(superposition,[],[f101,f60])).
% 16.74/2.45  fof(f60,plain,(
% 16.74/2.45    ( ! [X5] : (k2_xboole_0(X5,k1_xboole_0) = X5) )),
% 16.74/2.45    inference(forward_demodulation,[],[f55,f34])).
% 16.74/2.45  fof(f55,plain,(
% 16.74/2.45    ( ! [X6,X5] : (k2_xboole_0(X5,k4_xboole_0(X5,X6)) = k2_xboole_0(X5,k1_xboole_0)) )),
% 16.74/2.45    inference(superposition,[],[f18,f25])).
% 16.74/2.45  fof(f101,plain,(
% 16.74/2.45    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(X5,X4),X4) = k2_xboole_0(X4,X5)) )),
% 16.74/2.45    inference(forward_demodulation,[],[f95,f82])).
% 16.74/2.45  fof(f82,plain,(
% 16.74/2.45    ( ! [X10,X11] : (k2_xboole_0(X10,X11) = k2_xboole_0(k4_xboole_0(X11,X10),k2_xboole_0(X10,X11))) )),
% 16.74/2.45    inference(superposition,[],[f24,f26])).
% 16.74/2.45  fof(f26,plain,(
% 16.74/2.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) )),
% 16.74/2.45    inference(superposition,[],[f19,f17])).
% 16.74/2.45  fof(f95,plain,(
% 16.74/2.45    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(X5,X4),X4) = k2_xboole_0(k4_xboole_0(X5,X4),k2_xboole_0(X4,X5))) )),
% 16.74/2.45    inference(superposition,[],[f32,f18])).
% 16.74/2.45  fof(f32,plain,(
% 16.74/2.45    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1))) )),
% 16.74/2.45    inference(forward_demodulation,[],[f29,f18])).
% 16.74/2.45  fof(f29,plain,(
% 16.74/2.45    ( ! [X0,X1] : (k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 16.74/2.45    inference(superposition,[],[f18,f19])).
% 16.74/2.45  fof(f423,plain,(
% 16.74/2.45    ( ! [X24,X25] : (k4_xboole_0(k2_xboole_0(X25,X24),k1_xboole_0) = k4_xboole_0(k2_xboole_0(X24,X25),k1_xboole_0)) )),
% 16.74/2.45    inference(forward_demodulation,[],[f422,f32])).
% 16.74/2.45  fof(f422,plain,(
% 16.74/2.45    ( ! [X24,X25] : (k4_xboole_0(k2_xboole_0(X25,X24),k1_xboole_0) = k4_xboole_0(k2_xboole_0(X24,k2_xboole_0(X25,X24)),k1_xboole_0)) )),
% 16.74/2.45    inference(forward_demodulation,[],[f407,f17])).
% 16.74/2.45  fof(f407,plain,(
% 16.74/2.45    ( ! [X24,X25] : (k4_xboole_0(k2_xboole_0(X25,X24),k1_xboole_0) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X25,X24),X24),k1_xboole_0)) )),
% 16.74/2.45    inference(superposition,[],[f28,f52])).
% 16.74/2.45  fof(f28,plain,(
% 16.74/2.45    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X5,X4)) = k4_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4))) )),
% 16.74/2.45    inference(superposition,[],[f19,f18])).
% 16.74/2.45  fof(f16976,plain,(
% 16.74/2.45    ( ! [X57,X56,X55] : (k2_xboole_0(k4_xboole_0(X57,k2_xboole_0(X56,X55)),k4_xboole_0(X55,X56)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X55,X56),k4_xboole_0(X57,X56)),k1_xboole_0)) )),
% 16.74/2.45    inference(superposition,[],[f830,f185])).
% 16.74/2.45  fof(f36704,plain,(
% 16.74/2.45    ( ! [X30,X28,X29] : (k2_xboole_0(k4_xboole_0(X29,X28),k4_xboole_0(X30,X28)) = k2_xboole_0(k4_xboole_0(X30,k2_xboole_0(X28,X29)),k4_xboole_0(X29,X28))) )),
% 16.74/2.45    inference(superposition,[],[f791,f18])).
% 16.74/2.45  fof(f791,plain,(
% 16.74/2.45    ( ! [X24,X23,X22] : (k2_xboole_0(X24,k4_xboole_0(X22,X23)) = k2_xboole_0(k4_xboole_0(X22,k2_xboole_0(X23,X24)),X24)) )),
% 16.74/2.45    inference(superposition,[],[f101,f23])).
% 16.74/2.45  fof(f15,plain,(
% 16.74/2.45    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),
% 16.74/2.45    inference(cnf_transformation,[],[f13])).
% 16.74/2.45  fof(f13,plain,(
% 16.74/2.45    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),
% 16.74/2.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f12])).
% 16.74/2.45  fof(f12,plain,(
% 16.74/2.45    ? [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) => k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),
% 16.74/2.45    introduced(choice_axiom,[])).
% 16.74/2.45  fof(f10,plain,(
% 16.74/2.45    ? [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 16.74/2.45    inference(ennf_transformation,[],[f9])).
% 16.74/2.45  fof(f9,negated_conjecture,(
% 16.74/2.45    ~! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 16.74/2.45    inference(negated_conjecture,[],[f8])).
% 16.74/2.45  fof(f8,conjecture,(
% 16.74/2.45    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 16.74/2.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).
% 16.74/2.45  % SZS output end Proof for theBenchmark
% 16.74/2.45  % (846)------------------------------
% 16.74/2.45  % (846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.74/2.45  % (846)Termination reason: Refutation
% 16.74/2.45  
% 16.74/2.45  % (846)Memory used [KB]: 51427
% 16.74/2.45  % (846)Time elapsed: 2.009 s
% 16.74/2.45  % (846)------------------------------
% 16.74/2.45  % (846)------------------------------
% 16.74/2.46  % (832)Success in time 2.095 s
%------------------------------------------------------------------------------
