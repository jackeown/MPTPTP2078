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
% DateTime   : Thu Dec  3 12:34:40 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 120 expanded)
%              Number of leaves         :   10 (  40 expanded)
%              Depth                    :   21
%              Number of atoms          :   51 ( 121 expanded)
%              Number of equality atoms :   50 ( 120 expanded)
%              Maximal formula depth    :   12 (   7 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f756,plain,(
    $false ),
    inference(subsumption_resolution,[],[f19,f755])).

fof(f755,plain,(
    ! [X30,X28,X35,X33,X31,X29,X27,X34,X32] : k2_xboole_0(k4_enumset1(X33,X34,X35,X27,X28,X29),k1_enumset1(X30,X31,X32)) = k7_enumset1(X33,X34,X35,X27,X28,X29,X30,X31,X32) ),
    inference(forward_demodulation,[],[f739,f486])).

fof(f486,plain,(
    ! [X80,X78,X85,X83,X81,X79,X86,X84,X82] : k2_xboole_0(k1_enumset1(X83,X84,X85),k4_enumset1(X86,X78,X79,X80,X81,X82)) = k7_enumset1(X83,X84,X85,X86,X78,X79,X80,X81,X82) ),
    inference(forward_demodulation,[],[f485,f32])).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_enumset1)).

fof(f485,plain,(
    ! [X80,X78,X85,X83,X81,X79,X86,X84,X82] : k2_xboole_0(k3_enumset1(X83,X84,X85,X86,X78),k2_enumset1(X79,X80,X81,X82)) = k2_xboole_0(k1_enumset1(X83,X84,X85),k4_enumset1(X86,X78,X79,X80,X81,X82)) ),
    inference(forward_demodulation,[],[f471,f233])).

fof(f233,plain,(
    ! [X14,X21,X19,X17,X15,X13,X20,X18,X16] : k2_xboole_0(k2_enumset1(X19,X20,X21,X13),k3_enumset1(X14,X15,X16,X17,X18)) = k2_xboole_0(k1_enumset1(X19,X20,X21),k4_enumset1(X13,X14,X15,X16,X17,X18)) ),
    inference(superposition,[],[f109,f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

fof(f109,plain,(
    ! [X6,X4,X8,X7,X5] : k2_xboole_0(k2_enumset1(X4,X5,X6,X7),X8) = k2_xboole_0(k1_enumset1(X4,X5,X6),k2_xboole_0(k1_tarski(X7),X8)) ),
    inference(superposition,[],[f23,f107])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(forward_demodulation,[],[f105,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f105,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(superposition,[],[f104,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f104,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(forward_demodulation,[],[f102,f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f102,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(superposition,[],[f29,f24])).

fof(f29,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

fof(f23,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f471,plain,(
    ! [X80,X78,X85,X83,X81,X79,X86,X84,X82] : k2_xboole_0(k3_enumset1(X83,X84,X85,X86,X78),k2_enumset1(X79,X80,X81,X82)) = k2_xboole_0(k2_enumset1(X83,X84,X85,X86),k3_enumset1(X78,X79,X80,X81,X82)) ),
    inference(superposition,[],[f106,f332])).

fof(f332,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3)) = k3_enumset1(X4,X0,X1,X2,X3) ),
    inference(backward_demodulation,[],[f69,f331])).

fof(f331,plain,(
    ! [X10,X8,X7,X11,X9] : k4_enumset1(X7,X8,X8,X9,X10,X11) = k3_enumset1(X7,X8,X9,X10,X11) ),
    inference(forward_demodulation,[],[f329,f104])).

fof(f329,plain,(
    ! [X10,X8,X7,X11,X9] : k4_enumset1(X7,X8,X8,X9,X10,X11) = k2_xboole_0(k2_enumset1(X7,X8,X9,X10),k1_tarski(X11)) ),
    inference(superposition,[],[f29,f319])).

fof(f319,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X1,X1,X2,X3) ),
    inference(forward_demodulation,[],[f311,f24])).

fof(f311,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X1,X1,X2,X3) ),
    inference(superposition,[],[f298,f25])).

fof(f298,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X2,X3,X4) ),
    inference(superposition,[],[f294,f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

fof(f294,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X2,X3,X4)) ),
    inference(forward_demodulation,[],[f287,f25])).

fof(f287,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X2,X3,X4)) ),
    inference(superposition,[],[f244,f21])).

fof(f244,plain,(
    ! [X12,X10,X8,X7,X11,X9] : k2_xboole_0(k2_enumset1(X10,X11,X12,X7),k1_enumset1(X7,X8,X9)) = k4_enumset1(X10,X11,X12,X7,X8,X9) ),
    inference(forward_demodulation,[],[f232,f28])).

fof(f232,plain,(
    ! [X12,X10,X8,X7,X11,X9] : k2_xboole_0(k2_enumset1(X10,X11,X12,X7),k1_enumset1(X7,X8,X9)) = k2_xboole_0(k1_enumset1(X10,X11,X12),k1_enumset1(X7,X8,X9)) ),
    inference(superposition,[],[f109,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f75,f21])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X0,X1,X2,X3)) ),
    inference(forward_demodulation,[],[f71,f24])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X0,X1,X2,X3)) ),
    inference(superposition,[],[f69,f25])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X4,X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3)) ),
    inference(superposition,[],[f27,f24])).

fof(f106,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k1_tarski(X4),X5)) ),
    inference(superposition,[],[f23,f104])).

fof(f739,plain,(
    ! [X30,X28,X35,X33,X31,X29,X27,X34,X32] : k2_xboole_0(k4_enumset1(X33,X34,X35,X27,X28,X29),k1_enumset1(X30,X31,X32)) = k2_xboole_0(k1_enumset1(X33,X34,X35),k4_enumset1(X27,X28,X29,X30,X31,X32)) ),
    inference(superposition,[],[f101,f28])).

fof(f101,plain,(
    ! [X6,X12,X10,X8,X7,X11,X9] : k2_xboole_0(k1_enumset1(X6,X7,X8),k2_xboole_0(k1_enumset1(X9,X10,X11),X12)) = k2_xboole_0(k4_enumset1(X6,X7,X8,X9,X10,X11),X12) ),
    inference(superposition,[],[f23,f28])).

fof(f19,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))
   => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:18:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.43  % (26757)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.19/0.45  % (26746)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.19/0.45  % (26748)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.46  % (26741)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.19/0.46  % (26751)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.19/0.46  % (26757)Refutation found. Thanks to Tanya!
% 0.19/0.46  % SZS status Theorem for theBenchmark
% 0.19/0.46  % SZS output start Proof for theBenchmark
% 0.19/0.46  fof(f756,plain,(
% 0.19/0.46    $false),
% 0.19/0.46    inference(subsumption_resolution,[],[f19,f755])).
% 0.19/0.46  fof(f755,plain,(
% 0.19/0.46    ( ! [X30,X28,X35,X33,X31,X29,X27,X34,X32] : (k2_xboole_0(k4_enumset1(X33,X34,X35,X27,X28,X29),k1_enumset1(X30,X31,X32)) = k7_enumset1(X33,X34,X35,X27,X28,X29,X30,X31,X32)) )),
% 0.19/0.46    inference(forward_demodulation,[],[f739,f486])).
% 0.19/0.46  fof(f486,plain,(
% 0.19/0.46    ( ! [X80,X78,X85,X83,X81,X79,X86,X84,X82] : (k2_xboole_0(k1_enumset1(X83,X84,X85),k4_enumset1(X86,X78,X79,X80,X81,X82)) = k7_enumset1(X83,X84,X85,X86,X78,X79,X80,X81,X82)) )),
% 0.19/0.46    inference(forward_demodulation,[],[f485,f32])).
% 0.19/0.46  fof(f32,plain,(
% 0.19/0.46    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f6])).
% 0.19/0.46  fof(f6,axiom,(
% 0.19/0.46    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_enumset1)).
% 0.19/0.46  fof(f485,plain,(
% 0.19/0.46    ( ! [X80,X78,X85,X83,X81,X79,X86,X84,X82] : (k2_xboole_0(k3_enumset1(X83,X84,X85,X86,X78),k2_enumset1(X79,X80,X81,X82)) = k2_xboole_0(k1_enumset1(X83,X84,X85),k4_enumset1(X86,X78,X79,X80,X81,X82))) )),
% 0.19/0.46    inference(forward_demodulation,[],[f471,f233])).
% 0.19/0.46  fof(f233,plain,(
% 0.19/0.46    ( ! [X14,X21,X19,X17,X15,X13,X20,X18,X16] : (k2_xboole_0(k2_enumset1(X19,X20,X21,X13),k3_enumset1(X14,X15,X16,X17,X18)) = k2_xboole_0(k1_enumset1(X19,X20,X21),k4_enumset1(X13,X14,X15,X16,X17,X18))) )),
% 0.19/0.46    inference(superposition,[],[f109,f27])).
% 0.19/0.46  fof(f27,plain,(
% 0.19/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f7])).
% 0.19/0.46  fof(f7,axiom,(
% 0.19/0.46    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).
% 0.19/0.46  fof(f109,plain,(
% 0.19/0.46    ( ! [X6,X4,X8,X7,X5] : (k2_xboole_0(k2_enumset1(X4,X5,X6,X7),X8) = k2_xboole_0(k1_enumset1(X4,X5,X6),k2_xboole_0(k1_tarski(X7),X8))) )),
% 0.19/0.46    inference(superposition,[],[f23,f107])).
% 0.19/0.46  fof(f107,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.19/0.46    inference(forward_demodulation,[],[f105,f24])).
% 0.19/0.46  fof(f24,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f10])).
% 0.19/0.46  fof(f10,axiom,(
% 0.19/0.46    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.19/0.46  fof(f105,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.19/0.46    inference(superposition,[],[f104,f21])).
% 0.19/0.46  fof(f21,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f9])).
% 0.19/0.46  fof(f9,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.19/0.46  fof(f104,plain,(
% 0.19/0.46    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.19/0.46    inference(forward_demodulation,[],[f102,f25])).
% 0.19/0.46  fof(f25,plain,(
% 0.19/0.46    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f11])).
% 0.19/0.46  fof(f11,axiom,(
% 0.19/0.46    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.19/0.46  fof(f102,plain,(
% 0.19/0.46    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.19/0.46    inference(superposition,[],[f29,f24])).
% 0.19/0.46  fof(f29,plain,(
% 0.19/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f8])).
% 0.19/0.46  fof(f8,axiom,(
% 0.19/0.46    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).
% 0.19/0.46  fof(f23,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f1])).
% 0.19/0.46  fof(f1,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.19/0.46  fof(f471,plain,(
% 0.19/0.46    ( ! [X80,X78,X85,X83,X81,X79,X86,X84,X82] : (k2_xboole_0(k3_enumset1(X83,X84,X85,X86,X78),k2_enumset1(X79,X80,X81,X82)) = k2_xboole_0(k2_enumset1(X83,X84,X85,X86),k3_enumset1(X78,X79,X80,X81,X82))) )),
% 0.19/0.46    inference(superposition,[],[f106,f332])).
% 0.19/0.46  fof(f332,plain,(
% 0.19/0.46    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3)) = k3_enumset1(X4,X0,X1,X2,X3)) )),
% 0.19/0.46    inference(backward_demodulation,[],[f69,f331])).
% 0.19/0.46  fof(f331,plain,(
% 0.19/0.46    ( ! [X10,X8,X7,X11,X9] : (k4_enumset1(X7,X8,X8,X9,X10,X11) = k3_enumset1(X7,X8,X9,X10,X11)) )),
% 0.19/0.46    inference(forward_demodulation,[],[f329,f104])).
% 0.19/0.46  fof(f329,plain,(
% 0.19/0.46    ( ! [X10,X8,X7,X11,X9] : (k4_enumset1(X7,X8,X8,X9,X10,X11) = k2_xboole_0(k2_enumset1(X7,X8,X9,X10),k1_tarski(X11))) )),
% 0.19/0.46    inference(superposition,[],[f29,f319])).
% 0.19/0.46  fof(f319,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X1,X1,X2,X3)) )),
% 0.19/0.46    inference(forward_demodulation,[],[f311,f24])).
% 0.19/0.46  fof(f311,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X1,X1,X2,X3)) )),
% 0.19/0.46    inference(superposition,[],[f298,f25])).
% 0.19/0.46  fof(f298,plain,(
% 0.19/0.46    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X2,X3,X4)) )),
% 0.19/0.46    inference(superposition,[],[f294,f28])).
% 0.19/0.46  fof(f28,plain,(
% 0.19/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f4])).
% 0.19/0.46  fof(f4,axiom,(
% 0.19/0.46    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).
% 0.19/0.46  fof(f294,plain,(
% 0.19/0.46    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X2,X3,X4))) )),
% 0.19/0.46    inference(forward_demodulation,[],[f287,f25])).
% 0.19/0.46  fof(f287,plain,(
% 0.19/0.46    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X2,X3,X4))) )),
% 0.19/0.46    inference(superposition,[],[f244,f21])).
% 0.19/0.46  fof(f244,plain,(
% 0.19/0.46    ( ! [X12,X10,X8,X7,X11,X9] : (k2_xboole_0(k2_enumset1(X10,X11,X12,X7),k1_enumset1(X7,X8,X9)) = k4_enumset1(X10,X11,X12,X7,X8,X9)) )),
% 0.19/0.46    inference(forward_demodulation,[],[f232,f28])).
% 0.19/0.46  fof(f232,plain,(
% 0.19/0.46    ( ! [X12,X10,X8,X7,X11,X9] : (k2_xboole_0(k2_enumset1(X10,X11,X12,X7),k1_enumset1(X7,X8,X9)) = k2_xboole_0(k1_enumset1(X10,X11,X12),k1_enumset1(X7,X8,X9))) )),
% 0.19/0.46    inference(superposition,[],[f109,f77])).
% 0.19/0.46  fof(f77,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X0,X1,X2))) )),
% 0.19/0.46    inference(superposition,[],[f75,f21])).
% 0.19/0.46  fof(f75,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X0,X1,X2,X3))) )),
% 0.19/0.46    inference(forward_demodulation,[],[f71,f24])).
% 0.19/0.46  fof(f71,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X0,X1,X2,X3))) )),
% 0.19/0.46    inference(superposition,[],[f69,f25])).
% 0.19/0.46  fof(f69,plain,(
% 0.19/0.46    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X4,X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3))) )),
% 0.19/0.46    inference(superposition,[],[f27,f24])).
% 0.19/0.46  fof(f106,plain,(
% 0.19/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k1_tarski(X4),X5))) )),
% 0.19/0.46    inference(superposition,[],[f23,f104])).
% 0.19/0.46  fof(f739,plain,(
% 0.19/0.46    ( ! [X30,X28,X35,X33,X31,X29,X27,X34,X32] : (k2_xboole_0(k4_enumset1(X33,X34,X35,X27,X28,X29),k1_enumset1(X30,X31,X32)) = k2_xboole_0(k1_enumset1(X33,X34,X35),k4_enumset1(X27,X28,X29,X30,X31,X32))) )),
% 0.19/0.46    inference(superposition,[],[f101,f28])).
% 0.19/0.46  fof(f101,plain,(
% 0.19/0.46    ( ! [X6,X12,X10,X8,X7,X11,X9] : (k2_xboole_0(k1_enumset1(X6,X7,X8),k2_xboole_0(k1_enumset1(X9,X10,X11),X12)) = k2_xboole_0(k4_enumset1(X6,X7,X8,X9,X10,X11),X12)) )),
% 0.19/0.46    inference(superposition,[],[f23,f28])).
% 0.19/0.46  fof(f19,plain,(
% 0.19/0.46    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8))),
% 0.19/0.46    inference(cnf_transformation,[],[f18])).
% 0.19/0.46  fof(f18,plain,(
% 0.19/0.46    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8))),
% 0.19/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f16,f17])).
% 0.19/0.46  fof(f17,plain,(
% 0.19/0.46    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f16,plain,(
% 0.19/0.46    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))),
% 0.19/0.46    inference(ennf_transformation,[],[f15])).
% 0.19/0.46  fof(f15,negated_conjecture,(
% 0.19/0.46    ~! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))),
% 0.19/0.46    inference(negated_conjecture,[],[f14])).
% 0.19/0.46  fof(f14,conjecture,(
% 0.19/0.46    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_enumset1)).
% 0.19/0.46  % SZS output end Proof for theBenchmark
% 0.19/0.46  % (26757)------------------------------
% 0.19/0.46  % (26757)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (26757)Termination reason: Refutation
% 0.19/0.46  
% 0.19/0.46  % (26757)Memory used [KB]: 7036
% 0.19/0.46  % (26757)Time elapsed: 0.061 s
% 0.19/0.46  % (26757)------------------------------
% 0.19/0.46  % (26757)------------------------------
% 0.19/0.46  % (26753)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.19/0.47  % (26740)Success in time 0.119 s
%------------------------------------------------------------------------------
