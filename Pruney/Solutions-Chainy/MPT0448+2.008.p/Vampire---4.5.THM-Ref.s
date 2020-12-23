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
% DateTime   : Thu Dec  3 12:47:17 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 136 expanded)
%              Number of leaves         :   14 (  43 expanded)
%              Depth                    :   18
%              Number of atoms          :   85 ( 164 expanded)
%              Number of equality atoms :   71 ( 143 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f150,plain,(
    $false ),
    inference(subsumption_resolution,[],[f53,f149])).

fof(f149,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(forward_demodulation,[],[f148,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f148,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(superposition,[],[f147,f23])).

fof(f23,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f147,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(forward_demodulation,[],[f146,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f146,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(superposition,[],[f145,f25])).

fof(f145,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(forward_demodulation,[],[f144,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f144,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(superposition,[],[f141,f27])).

fof(f141,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(forward_demodulation,[],[f139,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(superposition,[],[f67,f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X5,X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X5),k3_enumset1(X0,X1,X2,X3,X4)) ),
    inference(superposition,[],[f59,f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    inference(forward_demodulation,[],[f57,f34])).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    inference(superposition,[],[f35,f23])).

fof(f35,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X0,X1,X2,X3,X4)) ),
    inference(forward_demodulation,[],[f63,f30])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X0,X1,X2,X3,X4)) ),
    inference(superposition,[],[f60,f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f139,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(superposition,[],[f104,f34])).

fof(f104,plain,(
    ! [X12,X10,X8,X11,X9] : k6_enumset1(X8,X8,X8,X8,X9,X10,X11,X12) = k2_xboole_0(k2_enumset1(X8,X9,X10,X11),k1_tarski(X12)) ),
    inference(superposition,[],[f36,f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(superposition,[],[f64,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X0,X1,X2,X3)) ),
    inference(superposition,[],[f67,f29])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X4,X0,X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3)) ),
    inference(superposition,[],[f60,f29])).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

fof(f53,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(superposition,[],[f22,f52])).

fof(f52,plain,(
    ! [X4,X5] : k3_relat_1(k1_tarski(k4_tarski(X4,X5))) = k2_xboole_0(k1_tarski(X4),k1_tarski(X5)) ),
    inference(backward_demodulation,[],[f49,f51])).

fof(f51,plain,(
    ! [X0,X1] : k1_tarski(X0) = k1_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(forward_demodulation,[],[f50,f23])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X0) = k1_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(superposition,[],[f40,f23])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_tarski(X0,X2) = k1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(subsumption_resolution,[],[f38,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relat_1)).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tarski(X0,X2) = k1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))
      | ~ v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_relat_1(X4) = k2_tarski(X0,X2)
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_relat_1(X4) = k2_tarski(X1,X3)
        & k1_relat_1(X4) = k2_tarski(X0,X2) )
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_relat_1(X4) = k2_tarski(X1,X3)
        & k1_relat_1(X4) = k2_tarski(X0,X2) )
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( v1_relat_1(X4)
     => ( k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) = X4
       => ( k2_relat_1(X4) = k2_tarski(X1,X3)
          & k1_relat_1(X4) = k2_tarski(X0,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relat_1)).

fof(f49,plain,(
    ! [X4,X5] : k3_relat_1(k1_tarski(k4_tarski(X4,X5))) = k2_xboole_0(k1_relat_1(k1_tarski(k4_tarski(X4,X5))),k1_tarski(X5)) ),
    inference(backward_demodulation,[],[f44,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_relat_1(k1_tarski(k4_tarski(X0,X1))) = k1_tarski(X1) ),
    inference(forward_demodulation,[],[f47,f23])).

fof(f47,plain,(
    ! [X0,X1] : k2_relat_1(k1_tarski(k4_tarski(X0,X1))) = k2_tarski(X1,X1) ),
    inference(superposition,[],[f39,f23])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k2_tarski(X1,X3) = k2_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(subsumption_resolution,[],[f37,f28])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tarski(X1,X3) = k2_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))
      | ~ v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relat_1(X4) = k2_tarski(X1,X3)
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f44,plain,(
    ! [X4,X5] : k3_relat_1(k1_tarski(k4_tarski(X4,X5))) = k2_xboole_0(k1_relat_1(k1_tarski(k4_tarski(X4,X5))),k2_relat_1(k1_tarski(k4_tarski(X4,X5)))) ),
    inference(resolution,[],[f24,f42])).

fof(f42,plain,(
    ! [X0,X1] : v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(superposition,[],[f28,f23])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f22,plain,(
    k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f20])).

fof(f20,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k3_relat_1(k1_tarski(k4_tarski(X0,X1)))
   => k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:08:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (13449)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (13458)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (13458)Refutation not found, incomplete strategy% (13458)------------------------------
% 0.21/0.53  % (13458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (13458)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (13458)Memory used [KB]: 10618
% 0.21/0.53  % (13458)Time elapsed: 0.109 s
% 0.21/0.53  % (13458)------------------------------
% 0.21/0.53  % (13458)------------------------------
% 0.21/0.53  % (13470)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (13475)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (13470)Refutation not found, incomplete strategy% (13470)------------------------------
% 0.21/0.54  % (13470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (13470)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (13470)Memory used [KB]: 1663
% 0.21/0.54  % (13470)Time elapsed: 0.128 s
% 0.21/0.54  % (13470)------------------------------
% 0.21/0.54  % (13470)------------------------------
% 0.21/0.54  % (13448)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (13448)Refutation not found, incomplete strategy% (13448)------------------------------
% 0.21/0.54  % (13448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (13448)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (13448)Memory used [KB]: 10746
% 0.21/0.54  % (13448)Time elapsed: 0.123 s
% 0.21/0.54  % (13448)------------------------------
% 0.21/0.54  % (13448)------------------------------
% 0.21/0.54  % (13463)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (13453)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (13454)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (13454)Refutation not found, incomplete strategy% (13454)------------------------------
% 0.21/0.55  % (13454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (13459)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (13471)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.56  % (13447)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.56/0.56  % (13474)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.56/0.56  % (13454)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.56  
% 1.56/0.56  % (13454)Memory used [KB]: 10746
% 1.56/0.56  % (13454)Time elapsed: 0.140 s
% 1.56/0.56  % (13454)------------------------------
% 1.56/0.56  % (13454)------------------------------
% 1.56/0.57  % (13456)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.56/0.57  % (13453)Refutation found. Thanks to Tanya!
% 1.56/0.57  % SZS status Theorem for theBenchmark
% 1.56/0.57  % SZS output start Proof for theBenchmark
% 1.56/0.57  fof(f150,plain,(
% 1.56/0.57    $false),
% 1.56/0.57    inference(subsumption_resolution,[],[f53,f149])).
% 1.56/0.57  fof(f149,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.56/0.57    inference(forward_demodulation,[],[f148,f25])).
% 1.56/0.57  fof(f25,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f4])).
% 1.56/0.57  fof(f4,axiom,(
% 1.56/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.56/0.57  fof(f148,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.56/0.57    inference(superposition,[],[f147,f23])).
% 1.56/0.57  fof(f23,plain,(
% 1.56/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f3])).
% 1.56/0.57  fof(f3,axiom,(
% 1.56/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.56/0.57  fof(f147,plain,(
% 1.56/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 1.56/0.57    inference(forward_demodulation,[],[f146,f27])).
% 1.56/0.57  fof(f27,plain,(
% 1.56/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f5])).
% 1.56/0.57  fof(f5,axiom,(
% 1.56/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.56/0.57  fof(f146,plain,(
% 1.56/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 1.56/0.57    inference(superposition,[],[f145,f25])).
% 1.56/0.57  fof(f145,plain,(
% 1.56/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 1.56/0.57    inference(forward_demodulation,[],[f144,f29])).
% 1.56/0.57  fof(f29,plain,(
% 1.56/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f6])).
% 1.56/0.57  fof(f6,axiom,(
% 1.56/0.57    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.56/0.57  fof(f144,plain,(
% 1.56/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 1.56/0.57    inference(superposition,[],[f141,f27])).
% 1.56/0.57  fof(f141,plain,(
% 1.56/0.57    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 1.56/0.57    inference(forward_demodulation,[],[f139,f70])).
% 1.56/0.57  fof(f70,plain,(
% 1.56/0.57    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 1.56/0.57    inference(superposition,[],[f67,f60])).
% 1.56/0.57  fof(f60,plain,(
% 1.56/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X5,X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X5),k3_enumset1(X0,X1,X2,X3,X4))) )),
% 1.56/0.57    inference(superposition,[],[f59,f30])).
% 1.56/0.57  fof(f30,plain,(
% 1.56/0.57    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f7])).
% 1.56/0.57  fof(f7,axiom,(
% 1.56/0.57    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.56/0.57  fof(f59,plain,(
% 1.56/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))) )),
% 1.56/0.57    inference(forward_demodulation,[],[f57,f34])).
% 1.56/0.57  fof(f34,plain,(
% 1.56/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f9])).
% 1.56/0.57  fof(f9,axiom,(
% 1.56/0.57    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.56/0.57  fof(f57,plain,(
% 1.56/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))) )),
% 1.56/0.57    inference(superposition,[],[f35,f23])).
% 1.56/0.57  fof(f35,plain,(
% 1.56/0.57    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))) )),
% 1.56/0.57    inference(cnf_transformation,[],[f1])).
% 1.56/0.57  fof(f1,axiom,(
% 1.56/0.57    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).
% 1.56/0.57  fof(f67,plain,(
% 1.56/0.57    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X0,X1,X2,X3,X4))) )),
% 1.56/0.57    inference(forward_demodulation,[],[f63,f30])).
% 1.56/0.57  fof(f63,plain,(
% 1.56/0.57    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X0,X1,X2,X3,X4))) )),
% 1.56/0.57    inference(superposition,[],[f60,f33])).
% 1.56/0.57  fof(f33,plain,(
% 1.56/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f8])).
% 1.56/0.57  fof(f8,axiom,(
% 1.56/0.57    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.56/0.57  fof(f139,plain,(
% 1.56/0.57    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 1.56/0.57    inference(superposition,[],[f104,f34])).
% 1.56/0.57  fof(f104,plain,(
% 1.56/0.57    ( ! [X12,X10,X8,X11,X9] : (k6_enumset1(X8,X8,X8,X8,X9,X10,X11,X12) = k2_xboole_0(k2_enumset1(X8,X9,X10,X11),k1_tarski(X12))) )),
% 1.56/0.57    inference(superposition,[],[f36,f86])).
% 1.56/0.57  fof(f86,plain,(
% 1.56/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 1.56/0.57    inference(superposition,[],[f64,f69])).
% 1.56/0.57  fof(f69,plain,(
% 1.56/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X0,X1,X2,X3))) )),
% 1.56/0.57    inference(superposition,[],[f67,f29])).
% 1.56/0.57  fof(f64,plain,(
% 1.56/0.57    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X4,X0,X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3))) )),
% 1.56/0.57    inference(superposition,[],[f60,f29])).
% 1.56/0.57  fof(f36,plain,(
% 1.56/0.57    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))) )),
% 1.56/0.57    inference(cnf_transformation,[],[f2])).
% 1.56/0.57  fof(f2,axiom,(
% 1.56/0.57    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).
% 1.56/0.57  fof(f53,plain,(
% 1.56/0.57    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.56/0.57    inference(superposition,[],[f22,f52])).
% 1.56/0.57  fof(f52,plain,(
% 1.56/0.57    ( ! [X4,X5] : (k3_relat_1(k1_tarski(k4_tarski(X4,X5))) = k2_xboole_0(k1_tarski(X4),k1_tarski(X5))) )),
% 1.56/0.57    inference(backward_demodulation,[],[f49,f51])).
% 1.56/0.57  fof(f51,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k1_tarski(X0) = k1_relat_1(k1_tarski(k4_tarski(X0,X1)))) )),
% 1.56/0.57    inference(forward_demodulation,[],[f50,f23])).
% 1.56/0.57  fof(f50,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k2_tarski(X0,X0) = k1_relat_1(k1_tarski(k4_tarski(X0,X1)))) )),
% 1.56/0.57    inference(superposition,[],[f40,f23])).
% 1.56/0.57  fof(f40,plain,(
% 1.56/0.57    ( ! [X2,X0,X3,X1] : (k2_tarski(X0,X2) = k1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 1.56/0.57    inference(subsumption_resolution,[],[f38,f28])).
% 1.56/0.57  fof(f28,plain,(
% 1.56/0.57    ( ! [X2,X0,X3,X1] : (v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 1.56/0.57    inference(cnf_transformation,[],[f12])).
% 1.56/0.57  fof(f12,axiom,(
% 1.56/0.57    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relat_1)).
% 1.56/0.57  fof(f38,plain,(
% 1.56/0.57    ( ! [X2,X0,X3,X1] : (k2_tarski(X0,X2) = k1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) | ~v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 1.56/0.57    inference(equality_resolution,[],[f31])).
% 1.56/0.57  fof(f31,plain,(
% 1.56/0.57    ( ! [X4,X2,X0,X3,X1] : (k1_relat_1(X4) = k2_tarski(X0,X2) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4 | ~v1_relat_1(X4)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f19])).
% 1.56/0.57  fof(f19,plain,(
% 1.56/0.57    ! [X0,X1,X2,X3,X4] : ((k2_relat_1(X4) = k2_tarski(X1,X3) & k1_relat_1(X4) = k2_tarski(X0,X2)) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4 | ~v1_relat_1(X4))),
% 1.56/0.57    inference(flattening,[],[f18])).
% 1.56/0.57  fof(f18,plain,(
% 1.56/0.57    ! [X0,X1,X2,X3,X4] : (((k2_relat_1(X4) = k2_tarski(X1,X3) & k1_relat_1(X4) = k2_tarski(X0,X2)) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4) | ~v1_relat_1(X4))),
% 1.56/0.57    inference(ennf_transformation,[],[f13])).
% 1.56/0.57  fof(f13,axiom,(
% 1.56/0.57    ! [X0,X1,X2,X3,X4] : (v1_relat_1(X4) => (k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) = X4 => (k2_relat_1(X4) = k2_tarski(X1,X3) & k1_relat_1(X4) = k2_tarski(X0,X2))))),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relat_1)).
% 1.56/0.57  fof(f49,plain,(
% 1.56/0.57    ( ! [X4,X5] : (k3_relat_1(k1_tarski(k4_tarski(X4,X5))) = k2_xboole_0(k1_relat_1(k1_tarski(k4_tarski(X4,X5))),k1_tarski(X5))) )),
% 1.56/0.57    inference(backward_demodulation,[],[f44,f48])).
% 1.56/0.57  fof(f48,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k2_relat_1(k1_tarski(k4_tarski(X0,X1))) = k1_tarski(X1)) )),
% 1.56/0.57    inference(forward_demodulation,[],[f47,f23])).
% 1.56/0.57  fof(f47,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k2_relat_1(k1_tarski(k4_tarski(X0,X1))) = k2_tarski(X1,X1)) )),
% 1.56/0.57    inference(superposition,[],[f39,f23])).
% 1.56/0.57  fof(f39,plain,(
% 1.56/0.57    ( ! [X2,X0,X3,X1] : (k2_tarski(X1,X3) = k2_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 1.56/0.57    inference(subsumption_resolution,[],[f37,f28])).
% 1.56/0.57  fof(f37,plain,(
% 1.56/0.57    ( ! [X2,X0,X3,X1] : (k2_tarski(X1,X3) = k2_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) | ~v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 1.56/0.57    inference(equality_resolution,[],[f32])).
% 1.56/0.57  fof(f32,plain,(
% 1.56/0.57    ( ! [X4,X2,X0,X3,X1] : (k2_relat_1(X4) = k2_tarski(X1,X3) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4 | ~v1_relat_1(X4)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f19])).
% 1.56/0.57  fof(f44,plain,(
% 1.56/0.57    ( ! [X4,X5] : (k3_relat_1(k1_tarski(k4_tarski(X4,X5))) = k2_xboole_0(k1_relat_1(k1_tarski(k4_tarski(X4,X5))),k2_relat_1(k1_tarski(k4_tarski(X4,X5))))) )),
% 1.56/0.57    inference(resolution,[],[f24,f42])).
% 1.56/0.57  fof(f42,plain,(
% 1.56/0.57    ( ! [X0,X1] : (v1_relat_1(k1_tarski(k4_tarski(X0,X1)))) )),
% 1.56/0.57    inference(superposition,[],[f28,f23])).
% 1.56/0.57  fof(f24,plain,(
% 1.56/0.57    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 1.56/0.57    inference(cnf_transformation,[],[f17])).
% 1.56/0.57  fof(f17,plain,(
% 1.56/0.57    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.56/0.57    inference(ennf_transformation,[],[f11])).
% 1.56/0.57  fof(f11,axiom,(
% 1.56/0.57    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 1.56/0.57  fof(f22,plain,(
% 1.56/0.57    k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1)))),
% 1.56/0.57    inference(cnf_transformation,[],[f21])).
% 1.56/0.57  fof(f21,plain,(
% 1.56/0.57    k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1)))),
% 1.56/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f20])).
% 1.56/0.57  fof(f20,plain,(
% 1.56/0.57    ? [X0,X1] : k2_tarski(X0,X1) != k3_relat_1(k1_tarski(k4_tarski(X0,X1))) => k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1)))),
% 1.56/0.57    introduced(choice_axiom,[])).
% 1.56/0.57  fof(f16,plain,(
% 1.56/0.57    ? [X0,X1] : k2_tarski(X0,X1) != k3_relat_1(k1_tarski(k4_tarski(X0,X1)))),
% 1.56/0.57    inference(ennf_transformation,[],[f15])).
% 1.56/0.57  fof(f15,negated_conjecture,(
% 1.56/0.57    ~! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1)))),
% 1.56/0.57    inference(negated_conjecture,[],[f14])).
% 1.56/0.57  fof(f14,conjecture,(
% 1.56/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1)))),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relat_1)).
% 1.56/0.57  % SZS output end Proof for theBenchmark
% 1.56/0.57  % (13453)------------------------------
% 1.56/0.57  % (13453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (13453)Termination reason: Refutation
% 1.56/0.57  
% 1.56/0.57  % (13453)Memory used [KB]: 6396
% 1.56/0.57  % (13453)Time elapsed: 0.142 s
% 1.56/0.57  % (13453)------------------------------
% 1.56/0.57  % (13453)------------------------------
% 1.56/0.57  % (13466)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.56/0.57  % (13464)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.56/0.57  % (13450)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.56/0.57  % (13450)Refutation not found, incomplete strategy% (13450)------------------------------
% 1.56/0.57  % (13450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (13450)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.57  
% 1.56/0.57  % (13450)Memory used [KB]: 6140
% 1.56/0.57  % (13450)Time elapsed: 0.141 s
% 1.56/0.57  % (13450)------------------------------
% 1.56/0.57  % (13450)------------------------------
% 1.56/0.57  % (13462)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.56/0.57  % (13462)Refutation not found, incomplete strategy% (13462)------------------------------
% 1.56/0.57  % (13462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (13462)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.57  
% 1.56/0.57  % (13462)Memory used [KB]: 6140
% 1.56/0.57  % (13462)Time elapsed: 0.002 s
% 1.56/0.57  % (13462)------------------------------
% 1.56/0.57  % (13462)------------------------------
% 1.56/0.58  % (13477)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.70/0.58  % (13474)Refutation not found, incomplete strategy% (13474)------------------------------
% 1.70/0.58  % (13474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.58  % (13469)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.70/0.58  % (13444)Success in time 0.221 s
%------------------------------------------------------------------------------
