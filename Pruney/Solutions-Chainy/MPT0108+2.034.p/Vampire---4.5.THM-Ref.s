%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:22 EST 2020

% Result     : Theorem 2.18s
% Output     : Refutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   73 (1509 expanded)
%              Number of leaves         :   13 ( 508 expanded)
%              Depth                    :   24
%              Number of atoms          :   79 (1720 expanded)
%              Number of equality atoms :   67 (1341 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4514,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4513,f1859])).

fof(f1859,plain,(
    ! [X6,X8,X7] : k5_xboole_0(X6,X7) = k5_xboole_0(k5_xboole_0(X6,k5_xboole_0(X7,X8)),X8) ),
    inference(superposition,[],[f1823,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1823,plain,(
    ! [X2,X1] : k5_xboole_0(k5_xboole_0(X1,X2),X2) = X1 ),
    inference(superposition,[],[f1811,f1704])).

fof(f1704,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f1513,f1702])).

fof(f1702,plain,(
    ! [X8] : k5_xboole_0(k1_xboole_0,X8) = X8 ),
    inference(forward_demodulation,[],[f1680,f21])).

fof(f21,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f1680,plain,(
    ! [X8] : k5_xboole_0(X8,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X8) ),
    inference(superposition,[],[f1513,f1300])).

fof(f1300,plain,(
    ! [X4] : k1_xboole_0 = k5_xboole_0(X4,X4) ),
    inference(backward_demodulation,[],[f991,f1249])).

fof(f1249,plain,(
    ! [X7] : k1_xboole_0 = k3_xboole_0(k5_xboole_0(X7,X7),k5_xboole_0(X7,k5_xboole_0(X7,X7))) ),
    inference(superposition,[],[f52,f816])).

fof(f816,plain,(
    ! [X4] : k3_xboole_0(X4,k5_xboole_0(X4,k5_xboole_0(X4,X4))) = X4 ),
    inference(superposition,[],[f37,f778])).

fof(f778,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f777,f21])).

fof(f777,plain,(
    ! [X0] : k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(forward_demodulation,[],[f725,f154])).

fof(f154,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f32,f21])).

fof(f725,plain,(
    ! [X0] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0))) = X0 ),
    inference(superposition,[],[f37,f231])).

fof(f231,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1) ),
    inference(resolution,[],[f216,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f216,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f201,f58])).

fof(f58,plain,(
    ! [X2,X3] : k1_xboole_0 = k3_xboole_0(X3,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(superposition,[],[f52,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f201,plain,(
    ! [X6,X8,X7] : r1_xboole_0(k3_xboole_0(X6,k5_xboole_0(X7,k3_xboole_0(X7,X8))),X8) ),
    inference(forward_demodulation,[],[f188,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) ),
    inference(backward_demodulation,[],[f42,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f42,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f33,f26,f26])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f33,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f188,plain,(
    ! [X6,X8,X7] : r1_xboole_0(k5_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,k3_xboole_0(X7,X8))),X8) ),
    inference(superposition,[],[f45,f34])).

fof(f45,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(backward_demodulation,[],[f38,f39])).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f27,f26,f26])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))),X1) ),
    inference(definition_unfolding,[],[f24,f26])).

fof(f24,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_xboole_1)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f23,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f25,f26])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f52,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(resolution,[],[f30,f45])).

fof(f991,plain,(
    ! [X4] : k5_xboole_0(X4,X4) = k3_xboole_0(k5_xboole_0(X4,X4),k5_xboole_0(X4,k5_xboole_0(X4,X4))) ),
    inference(forward_demodulation,[],[f990,f21])).

fof(f990,plain,(
    ! [X4] : k5_xboole_0(X4,X4) = k3_xboole_0(k5_xboole_0(X4,X4),k5_xboole_0(X4,k5_xboole_0(X4,k5_xboole_0(X4,k1_xboole_0)))) ),
    inference(forward_demodulation,[],[f950,f32])).

fof(f950,plain,(
    ! [X4] : k5_xboole_0(X4,X4) = k3_xboole_0(k5_xboole_0(X4,X4),k5_xboole_0(k5_xboole_0(X4,X4),k5_xboole_0(X4,k1_xboole_0))) ),
    inference(superposition,[],[f37,f821])).

fof(f821,plain,(
    ! [X9] : k1_xboole_0 = k3_xboole_0(X9,k5_xboole_0(X9,X9)) ),
    inference(superposition,[],[f58,f778])).

fof(f1513,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f32,f1300])).

fof(f1811,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f1797,f21])).

fof(f1797,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f1704,f1512])).

fof(f1512,plain,(
    ! [X2,X3] : k1_xboole_0 = k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,X3))) ),
    inference(superposition,[],[f1300,f32])).

fof(f4513,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f4512,f22])).

fof(f4512,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK1,sK0)) ),
    inference(backward_demodulation,[],[f46,f4270])).

fof(f4270,plain,(
    ! [X87,X85,X86] : k3_xboole_0(X87,X85) = k3_xboole_0(X85,k3_xboole_0(X87,k5_xboole_0(X85,k5_xboole_0(X86,k3_xboole_0(X85,X86))))) ),
    inference(superposition,[],[f2504,f726])).

fof(f726,plain,(
    ! [X2,X1] : k3_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))) = X2 ),
    inference(superposition,[],[f37,f22])).

fof(f2504,plain,(
    ! [X17,X15,X16] : k3_xboole_0(X15,k3_xboole_0(X16,X17)) = k3_xboole_0(X16,k3_xboole_0(X15,X17)) ),
    inference(superposition,[],[f175,f34])).

fof(f175,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X1,X0),X2) ),
    inference(superposition,[],[f34,f22])).

fof(f46,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))) ),
    inference(backward_demodulation,[],[f44,f34])).

fof(f44,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))) ),
    inference(forward_demodulation,[],[f43,f22])).

fof(f43,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))) ),
    inference(backward_demodulation,[],[f36,f22])).

fof(f36,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f20,f26,f35])).

fof(f20,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:34:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.45  % (16938)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (16945)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (16935)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (16937)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (16936)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (16939)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (16947)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (16946)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (16944)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (16940)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (16950)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % (16944)Refutation not found, incomplete strategy% (16944)------------------------------
% 0.21/0.50  % (16944)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (16944)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (16944)Memory used [KB]: 10618
% 0.21/0.50  % (16944)Time elapsed: 0.076 s
% 0.21/0.50  % (16944)------------------------------
% 0.21/0.50  % (16944)------------------------------
% 0.21/0.50  % (16943)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.51  % (16949)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.51  % (16933)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.52  % (16934)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.53  % (16942)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.53  % (16941)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.53  % (16948)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 2.18/0.64  % (16947)Refutation found. Thanks to Tanya!
% 2.18/0.64  % SZS status Theorem for theBenchmark
% 2.18/0.64  % SZS output start Proof for theBenchmark
% 2.18/0.64  fof(f4514,plain,(
% 2.18/0.64    $false),
% 2.18/0.64    inference(subsumption_resolution,[],[f4513,f1859])).
% 2.18/0.64  fof(f1859,plain,(
% 2.18/0.64    ( ! [X6,X8,X7] : (k5_xboole_0(X6,X7) = k5_xboole_0(k5_xboole_0(X6,k5_xboole_0(X7,X8)),X8)) )),
% 2.18/0.64    inference(superposition,[],[f1823,f32])).
% 2.18/0.64  fof(f32,plain,(
% 2.18/0.64    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.18/0.64    inference(cnf_transformation,[],[f11])).
% 2.18/0.64  fof(f11,axiom,(
% 2.18/0.64    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.18/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.18/0.64  fof(f1823,plain,(
% 2.18/0.64    ( ! [X2,X1] : (k5_xboole_0(k5_xboole_0(X1,X2),X2) = X1) )),
% 2.18/0.64    inference(superposition,[],[f1811,f1704])).
% 2.18/0.64  fof(f1704,plain,(
% 2.18/0.64    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.18/0.64    inference(backward_demodulation,[],[f1513,f1702])).
% 2.18/0.64  fof(f1702,plain,(
% 2.18/0.64    ( ! [X8] : (k5_xboole_0(k1_xboole_0,X8) = X8) )),
% 2.18/0.64    inference(forward_demodulation,[],[f1680,f21])).
% 2.18/0.64  fof(f21,plain,(
% 2.18/0.64    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.18/0.64    inference(cnf_transformation,[],[f8])).
% 2.18/0.64  fof(f8,axiom,(
% 2.18/0.64    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.18/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 2.18/0.64  fof(f1680,plain,(
% 2.18/0.64    ( ! [X8] : (k5_xboole_0(X8,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X8)) )),
% 2.18/0.64    inference(superposition,[],[f1513,f1300])).
% 2.18/0.64  fof(f1300,plain,(
% 2.18/0.64    ( ! [X4] : (k1_xboole_0 = k5_xboole_0(X4,X4)) )),
% 2.18/0.64    inference(backward_demodulation,[],[f991,f1249])).
% 2.18/0.64  fof(f1249,plain,(
% 2.18/0.64    ( ! [X7] : (k1_xboole_0 = k3_xboole_0(k5_xboole_0(X7,X7),k5_xboole_0(X7,k5_xboole_0(X7,X7)))) )),
% 2.18/0.64    inference(superposition,[],[f52,f816])).
% 2.18/0.64  fof(f816,plain,(
% 2.18/0.64    ( ! [X4] : (k3_xboole_0(X4,k5_xboole_0(X4,k5_xboole_0(X4,X4))) = X4) )),
% 2.18/0.64    inference(superposition,[],[f37,f778])).
% 2.18/0.64  fof(f778,plain,(
% 2.18/0.64    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.18/0.64    inference(forward_demodulation,[],[f777,f21])).
% 2.18/0.64  fof(f777,plain,(
% 2.18/0.64    ( ! [X0] : (k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0)) = X0) )),
% 2.18/0.64    inference(forward_demodulation,[],[f725,f154])).
% 2.18/0.64  fof(f154,plain,(
% 2.18/0.64    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1))) )),
% 2.18/0.64    inference(superposition,[],[f32,f21])).
% 2.18/0.64  fof(f725,plain,(
% 2.18/0.64    ( ! [X0] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0))) = X0) )),
% 2.18/0.64    inference(superposition,[],[f37,f231])).
% 2.18/0.64  fof(f231,plain,(
% 2.18/0.64    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)) )),
% 2.18/0.64    inference(resolution,[],[f216,f30])).
% 2.18/0.64  fof(f30,plain,(
% 2.18/0.64    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.18/0.64    inference(cnf_transformation,[],[f19])).
% 2.18/0.64  fof(f19,plain,(
% 2.18/0.64    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.18/0.64    inference(nnf_transformation,[],[f2])).
% 2.18/0.64  fof(f2,axiom,(
% 2.18/0.64    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.18/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.18/0.64  fof(f216,plain,(
% 2.18/0.64    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 2.18/0.64    inference(superposition,[],[f201,f58])).
% 2.18/0.64  fof(f58,plain,(
% 2.18/0.64    ( ! [X2,X3] : (k1_xboole_0 = k3_xboole_0(X3,k5_xboole_0(X2,k3_xboole_0(X2,X3)))) )),
% 2.18/0.64    inference(superposition,[],[f52,f22])).
% 2.18/0.64  fof(f22,plain,(
% 2.18/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.18/0.64    inference(cnf_transformation,[],[f1])).
% 2.18/0.64  fof(f1,axiom,(
% 2.18/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.18/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.18/0.64  fof(f201,plain,(
% 2.18/0.64    ( ! [X6,X8,X7] : (r1_xboole_0(k3_xboole_0(X6,k5_xboole_0(X7,k3_xboole_0(X7,X8))),X8)) )),
% 2.18/0.64    inference(forward_demodulation,[],[f188,f47])).
% 2.18/0.64  fof(f47,plain,(
% 2.18/0.64    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2)))) )),
% 2.18/0.64    inference(backward_demodulation,[],[f42,f34])).
% 2.18/0.64  fof(f34,plain,(
% 2.18/0.64    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 2.18/0.64    inference(cnf_transformation,[],[f4])).
% 2.18/0.64  fof(f4,axiom,(
% 2.18/0.64    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 2.18/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 2.18/0.64  fof(f42,plain,(
% 2.18/0.64    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 2.18/0.64    inference(definition_unfolding,[],[f33,f26,f26])).
% 2.18/0.64  fof(f26,plain,(
% 2.18/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.18/0.64    inference(cnf_transformation,[],[f3])).
% 2.18/0.64  fof(f3,axiom,(
% 2.18/0.64    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.18/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.18/0.64  fof(f33,plain,(
% 2.18/0.64    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 2.18/0.64    inference(cnf_transformation,[],[f7])).
% 2.18/0.64  fof(f7,axiom,(
% 2.18/0.64    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 2.18/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 2.18/0.64  fof(f188,plain,(
% 2.18/0.64    ( ! [X6,X8,X7] : (r1_xboole_0(k5_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,k3_xboole_0(X7,X8))),X8)) )),
% 2.18/0.64    inference(superposition,[],[f45,f34])).
% 2.18/0.64  fof(f45,plain,(
% 2.18/0.64    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 2.18/0.64    inference(backward_demodulation,[],[f38,f39])).
% 2.18/0.64  fof(f39,plain,(
% 2.18/0.64    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 2.18/0.64    inference(definition_unfolding,[],[f27,f26,f26])).
% 2.18/0.64  fof(f27,plain,(
% 2.18/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.18/0.64    inference(cnf_transformation,[],[f6])).
% 2.18/0.64  fof(f6,axiom,(
% 2.18/0.64    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.18/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.18/0.64  fof(f38,plain,(
% 2.18/0.64    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))),X1)) )),
% 2.18/0.64    inference(definition_unfolding,[],[f24,f26])).
% 2.18/0.64  fof(f24,plain,(
% 2.18/0.64    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 2.18/0.64    inference(cnf_transformation,[],[f10])).
% 2.18/0.64  fof(f10,axiom,(
% 2.18/0.64    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)),
% 2.18/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_xboole_1)).
% 2.18/0.64  fof(f37,plain,(
% 2.18/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 2.18/0.64    inference(definition_unfolding,[],[f23,f35])).
% 2.18/0.64  fof(f35,plain,(
% 2.18/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 2.18/0.64    inference(definition_unfolding,[],[f25,f26])).
% 2.18/0.64  fof(f25,plain,(
% 2.18/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.18/0.64    inference(cnf_transformation,[],[f12])).
% 2.18/0.64  fof(f12,axiom,(
% 2.18/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.18/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.18/0.64  fof(f23,plain,(
% 2.18/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 2.18/0.64    inference(cnf_transformation,[],[f5])).
% 2.18/0.64  fof(f5,axiom,(
% 2.18/0.64    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 2.18/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 2.18/0.64  fof(f52,plain,(
% 2.18/0.64    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 2.18/0.64    inference(resolution,[],[f30,f45])).
% 2.18/0.64  fof(f991,plain,(
% 2.18/0.64    ( ! [X4] : (k5_xboole_0(X4,X4) = k3_xboole_0(k5_xboole_0(X4,X4),k5_xboole_0(X4,k5_xboole_0(X4,X4)))) )),
% 2.18/0.64    inference(forward_demodulation,[],[f990,f21])).
% 2.18/0.64  fof(f990,plain,(
% 2.18/0.64    ( ! [X4] : (k5_xboole_0(X4,X4) = k3_xboole_0(k5_xboole_0(X4,X4),k5_xboole_0(X4,k5_xboole_0(X4,k5_xboole_0(X4,k1_xboole_0))))) )),
% 2.18/0.64    inference(forward_demodulation,[],[f950,f32])).
% 2.18/0.64  fof(f950,plain,(
% 2.18/0.64    ( ! [X4] : (k5_xboole_0(X4,X4) = k3_xboole_0(k5_xboole_0(X4,X4),k5_xboole_0(k5_xboole_0(X4,X4),k5_xboole_0(X4,k1_xboole_0)))) )),
% 2.18/0.64    inference(superposition,[],[f37,f821])).
% 2.18/0.64  fof(f821,plain,(
% 2.18/0.64    ( ! [X9] : (k1_xboole_0 = k3_xboole_0(X9,k5_xboole_0(X9,X9))) )),
% 2.18/0.64    inference(superposition,[],[f58,f778])).
% 2.18/0.64  fof(f1513,plain,(
% 2.18/0.64    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.18/0.64    inference(superposition,[],[f32,f1300])).
% 2.18/0.64  fof(f1811,plain,(
% 2.18/0.64    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1) )),
% 2.18/0.64    inference(forward_demodulation,[],[f1797,f21])).
% 2.18/0.64  fof(f1797,plain,(
% 2.18/0.64    ( ! [X2,X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2))) )),
% 2.18/0.64    inference(superposition,[],[f1704,f1512])).
% 2.18/0.64  fof(f1512,plain,(
% 2.18/0.64    ( ! [X2,X3] : (k1_xboole_0 = k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,X3)))) )),
% 2.18/0.64    inference(superposition,[],[f1300,f32])).
% 2.18/0.64  fof(f4513,plain,(
% 2.18/0.64    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1))),
% 2.18/0.64    inference(forward_demodulation,[],[f4512,f22])).
% 2.18/0.64  fof(f4512,plain,(
% 2.18/0.64    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK1,sK0))),
% 2.18/0.64    inference(backward_demodulation,[],[f46,f4270])).
% 2.18/0.64  fof(f4270,plain,(
% 2.18/0.64    ( ! [X87,X85,X86] : (k3_xboole_0(X87,X85) = k3_xboole_0(X85,k3_xboole_0(X87,k5_xboole_0(X85,k5_xboole_0(X86,k3_xboole_0(X85,X86)))))) )),
% 2.18/0.64    inference(superposition,[],[f2504,f726])).
% 2.18/0.64  fof(f726,plain,(
% 2.18/0.64    ( ! [X2,X1] : (k3_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))) = X2) )),
% 2.18/0.64    inference(superposition,[],[f37,f22])).
% 2.18/0.64  fof(f2504,plain,(
% 2.18/0.64    ( ! [X17,X15,X16] : (k3_xboole_0(X15,k3_xboole_0(X16,X17)) = k3_xboole_0(X16,k3_xboole_0(X15,X17))) )),
% 2.18/0.64    inference(superposition,[],[f175,f34])).
% 2.18/0.64  fof(f175,plain,(
% 2.18/0.64    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X1,X0),X2)) )),
% 2.18/0.64    inference(superposition,[],[f34,f22])).
% 2.18/0.64  fof(f46,plain,(
% 2.18/0.64    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))),
% 2.18/0.64    inference(backward_demodulation,[],[f44,f34])).
% 2.18/0.64  fof(f44,plain,(
% 2.18/0.64    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))),
% 2.18/0.64    inference(forward_demodulation,[],[f43,f22])).
% 2.18/0.64  fof(f43,plain,(
% 2.18/0.64    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))))),
% 2.18/0.64    inference(backward_demodulation,[],[f36,f22])).
% 2.18/0.64  fof(f36,plain,(
% 2.18/0.64    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1)))),
% 2.18/0.64    inference(definition_unfolding,[],[f20,f26,f35])).
% 2.18/0.64  fof(f20,plain,(
% 2.18/0.64    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 2.18/0.64    inference(cnf_transformation,[],[f17])).
% 2.18/0.64  fof(f17,plain,(
% 2.18/0.64    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 2.18/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).
% 2.18/0.64  fof(f16,plain,(
% 2.18/0.64    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 2.18/0.64    introduced(choice_axiom,[])).
% 2.18/0.64  fof(f15,plain,(
% 2.18/0.64    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.18/0.64    inference(ennf_transformation,[],[f14])).
% 2.18/0.64  fof(f14,negated_conjecture,(
% 2.18/0.64    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.18/0.64    inference(negated_conjecture,[],[f13])).
% 2.18/0.64  fof(f13,conjecture,(
% 2.18/0.64    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.18/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
% 2.18/0.64  % SZS output end Proof for theBenchmark
% 2.18/0.64  % (16947)------------------------------
% 2.18/0.64  % (16947)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.64  % (16947)Termination reason: Refutation
% 2.18/0.64  
% 2.18/0.64  % (16947)Memory used [KB]: 8955
% 2.18/0.64  % (16947)Time elapsed: 0.142 s
% 2.18/0.64  % (16947)------------------------------
% 2.18/0.64  % (16947)------------------------------
% 2.18/0.64  % (16929)Success in time 0.278 s
%------------------------------------------------------------------------------
