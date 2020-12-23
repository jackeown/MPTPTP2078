%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 231 expanded)
%              Number of leaves         :   11 (  67 expanded)
%              Depth                    :   17
%              Number of atoms          :   93 ( 355 expanded)
%              Number of equality atoms :   46 ( 150 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f547,plain,(
    $false ),
    inference(subsumption_resolution,[],[f530,f21])).

fof(f21,plain,(
    ! [X0] : ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] : ~ r2_xboole_0(X0,X0) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : ~ r2_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

fof(f530,plain,(
    r2_xboole_0(sK0,sK0) ),
    inference(backward_demodulation,[],[f17,f529])).

fof(f529,plain,(
    sK0 = sK1 ),
    inference(backward_demodulation,[],[f71,f514])).

fof(f514,plain,(
    sK0 = k2_xboole_0(sK1,sK0) ),
    inference(backward_demodulation,[],[f36,f511])).

fof(f511,plain,(
    sK0 = sK2 ),
    inference(subsumption_resolution,[],[f508,f19])).

fof(f19,plain,(
    ~ r2_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r1_tarski(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r1_tarski(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X1,X2)
          & r2_xboole_0(X0,X1) )
       => r2_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r2_xboole_0(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_xboole_1)).

fof(f508,plain,
    ( sK0 = sK2
    | r2_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f507,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f507,plain,(
    r1_tarski(sK0,sK2) ),
    inference(superposition,[],[f470,f53])).

fof(f53,plain,(
    sK2 = k2_xboole_0(sK2,sK1) ),
    inference(backward_demodulation,[],[f46,f52])).

fof(f52,plain,(
    sK2 = k2_xboole_0(k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f48,f36])).

fof(f48,plain,(
    k2_xboole_0(sK1,sK2) = k2_xboole_0(k1_xboole_0,sK2) ),
    inference(superposition,[],[f46,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f46,plain,(
    k2_xboole_0(sK2,sK1) = k2_xboole_0(k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f44,f22])).

fof(f44,plain,(
    k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f24,f38])).

fof(f38,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f30,f18])).

fof(f18,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f470,plain,(
    ! [X3] : r1_tarski(sK0,k2_xboole_0(X3,sK1)) ),
    inference(backward_demodulation,[],[f147,f463])).

fof(f463,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f454,f199])).

fof(f199,plain,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(backward_demodulation,[],[f103,f196])).

fof(f196,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(resolution,[],[f173,f30])).

fof(f173,plain,(
    ! [X7] : r1_tarski(X7,X7) ),
    inference(superposition,[],[f149,f108])).

fof(f108,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[],[f103,f24])).

fof(f149,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f148,f24])).

fof(f148,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f119,f22])).

fof(f119,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) ),
    inference(superposition,[],[f34,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f25,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f34,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))),k2_xboole_0(X1,X2)) ),
    inference(definition_unfolding,[],[f32,f23,f23])).

fof(f32,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f103,plain,(
    ! [X1] : k2_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(superposition,[],[f85,f22])).

fof(f85,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(X0,X0),X0) = X0 ),
    inference(superposition,[],[f33,f20])).

fof(f20,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f454,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f24,f288])).

fof(f288,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),X2) ),
    inference(resolution,[],[f174,f30])).

fof(f174,plain,(
    ! [X8,X9] : r1_tarski(k4_xboole_0(X8,X9),X8) ),
    inference(superposition,[],[f149,f33])).

fof(f147,plain,(
    ! [X3] : r1_tarski(k2_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X3))),k2_xboole_0(X3,sK1)) ),
    inference(forward_demodulation,[],[f146,f20])).

fof(f146,plain,(
    ! [X3] : r1_tarski(k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k4_xboole_0(sK0,X3))),k2_xboole_0(X3,sK1)) ),
    inference(forward_demodulation,[],[f118,f22])).

fof(f118,plain,(
    ! [X3] : r1_tarski(k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X3)),k4_xboole_0(sK0,k1_xboole_0)),k2_xboole_0(X3,sK1)) ),
    inference(superposition,[],[f34,f43])).

% (6889)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f43,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f39,f17])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f30,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f36,plain,(
    sK2 = k2_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f26,f18])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f71,plain,(
    sK1 = k2_xboole_0(sK1,sK0) ),
    inference(backward_demodulation,[],[f47,f70])).

fof(f70,plain,(
    sK1 = k2_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f66,f42])).

fof(f42,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f37,f17])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(resolution,[],[f26,f27])).

fof(f66,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,sK1) ),
    inference(superposition,[],[f47,f22])).

fof(f47,plain,(
    k2_xboole_0(sK1,sK0) = k2_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f45,f22])).

fof(f45,plain,(
    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f24,f43])).

fof(f17,plain,(
    r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 16:20:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.21/0.50  % (6872)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (6872)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (6888)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (6869)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (6888)Refutation not found, incomplete strategy% (6888)------------------------------
% 0.21/0.53  % (6888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (6880)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (6888)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (6888)Memory used [KB]: 10618
% 0.21/0.53  % (6888)Time elapsed: 0.108 s
% 0.21/0.53  % (6888)------------------------------
% 0.21/0.53  % (6888)------------------------------
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f547,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f530,f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_xboole_0(X0,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0] : ~r2_xboole_0(X0,X0)),
% 0.21/0.53    inference(rectify,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : ~r2_xboole_0(X0,X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).
% 0.21/0.53  fof(f530,plain,(
% 0.21/0.53    r2_xboole_0(sK0,sK0)),
% 0.21/0.53    inference(backward_demodulation,[],[f17,f529])).
% 0.21/0.53  fof(f529,plain,(
% 0.21/0.53    sK0 = sK1),
% 0.21/0.53    inference(backward_demodulation,[],[f71,f514])).
% 0.21/0.53  fof(f514,plain,(
% 0.21/0.53    sK0 = k2_xboole_0(sK1,sK0)),
% 0.21/0.53    inference(backward_demodulation,[],[f36,f511])).
% 0.21/0.53  fof(f511,plain,(
% 0.21/0.53    sK0 = sK2),
% 0.21/0.53    inference(subsumption_resolution,[],[f508,f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ~r2_xboole_0(sK0,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r1_tarski(X1,X2) & r2_xboole_0(X0,X1))),
% 0.21/0.53    inference(flattening,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & (r1_tarski(X1,X2) & r2_xboole_0(X0,X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2] : ((r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.21/0.53    inference(negated_conjecture,[],[f11])).
% 0.21/0.53  fof(f11,conjecture,(
% 0.21/0.53    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_xboole_1)).
% 0.21/0.53  fof(f508,plain,(
% 0.21/0.53    sK0 = sK2 | r2_xboole_0(sK0,sK2)),
% 0.21/0.53    inference(resolution,[],[f507,f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.53  fof(f507,plain,(
% 0.21/0.53    r1_tarski(sK0,sK2)),
% 0.21/0.53    inference(superposition,[],[f470,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    sK2 = k2_xboole_0(sK2,sK1)),
% 0.21/0.53    inference(backward_demodulation,[],[f46,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    sK2 = k2_xboole_0(k1_xboole_0,sK2)),
% 0.21/0.53    inference(forward_demodulation,[],[f48,f36])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    k2_xboole_0(sK1,sK2) = k2_xboole_0(k1_xboole_0,sK2)),
% 0.21/0.53    inference(superposition,[],[f46,f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    k2_xboole_0(sK2,sK1) = k2_xboole_0(k1_xboole_0,sK2)),
% 0.21/0.53    inference(forward_demodulation,[],[f44,f22])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k1_xboole_0)),
% 0.21/0.53    inference(superposition,[],[f24,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 0.21/0.53    inference(resolution,[],[f30,f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    r1_tarski(sK1,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.53  fof(f470,plain,(
% 0.21/0.53    ( ! [X3] : (r1_tarski(sK0,k2_xboole_0(X3,sK1))) )),
% 0.21/0.53    inference(backward_demodulation,[],[f147,f463])).
% 0.21/0.53  fof(f463,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.53    inference(forward_demodulation,[],[f454,f199])).
% 0.21/0.53  fof(f199,plain,(
% 0.21/0.53    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) )),
% 0.21/0.53    inference(backward_demodulation,[],[f103,f196])).
% 0.21/0.53  fof(f196,plain,(
% 0.21/0.53    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 0.21/0.53    inference(resolution,[],[f173,f30])).
% 0.21/0.53  fof(f173,plain,(
% 0.21/0.53    ( ! [X7] : (r1_tarski(X7,X7)) )),
% 0.21/0.53    inference(superposition,[],[f149,f108])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.53    inference(superposition,[],[f103,f24])).
% 0.21/0.53  fof(f149,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f148,f24])).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1)))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f119,f22])).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1))) )),
% 0.21/0.53    inference(superposition,[],[f34,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.53    inference(definition_unfolding,[],[f25,f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))),k2_xboole_0(X1,X2))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f32,f23,f23])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    ( ! [X1] : (k2_xboole_0(X1,k4_xboole_0(X1,X1)) = X1) )),
% 0.21/0.53    inference(superposition,[],[f85,f22])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,X0),X0) = X0) )),
% 0.21/0.53    inference(superposition,[],[f33,f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.53  fof(f454,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(superposition,[],[f24,f288])).
% 0.21/0.53  fof(f288,plain,(
% 0.21/0.53    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),X2)) )),
% 0.21/0.53    inference(resolution,[],[f174,f30])).
% 0.21/0.53  fof(f174,plain,(
% 0.21/0.53    ( ! [X8,X9] : (r1_tarski(k4_xboole_0(X8,X9),X8)) )),
% 0.21/0.53    inference(superposition,[],[f149,f33])).
% 0.21/0.53  fof(f147,plain,(
% 0.21/0.53    ( ! [X3] : (r1_tarski(k2_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X3))),k2_xboole_0(X3,sK1))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f146,f20])).
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    ( ! [X3] : (r1_tarski(k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k4_xboole_0(sK0,X3))),k2_xboole_0(X3,sK1))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f118,f22])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    ( ! [X3] : (r1_tarski(k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X3)),k4_xboole_0(sK0,k1_xboole_0)),k2_xboole_0(X3,sK1))) )),
% 0.21/0.53    inference(superposition,[],[f34,f43])).
% 0.21/0.53  % (6889)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.21/0.53    inference(resolution,[],[f39,f17])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.53    inference(resolution,[],[f30,f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    sK2 = k2_xboole_0(sK1,sK2)),
% 0.21/0.53    inference(resolution,[],[f26,f18])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    sK1 = k2_xboole_0(sK1,sK0)),
% 0.21/0.53    inference(backward_demodulation,[],[f47,f70])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    sK1 = k2_xboole_0(k1_xboole_0,sK1)),
% 0.21/0.53    inference(forward_demodulation,[],[f66,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    sK1 = k2_xboole_0(sK0,sK1)),
% 0.21/0.53    inference(resolution,[],[f37,f17])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.53    inference(resolution,[],[f26,f27])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    k2_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,sK1)),
% 0.21/0.53    inference(superposition,[],[f47,f22])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    k2_xboole_0(sK1,sK0) = k2_xboole_0(k1_xboole_0,sK1)),
% 0.21/0.53    inference(forward_demodulation,[],[f45,f22])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0)),
% 0.21/0.53    inference(superposition,[],[f24,f43])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    r2_xboole_0(sK0,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (6872)------------------------------
% 0.21/0.53  % (6872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (6872)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (6872)Memory used [KB]: 6396
% 0.21/0.53  % (6872)Time elapsed: 0.103 s
% 0.21/0.53  % (6872)------------------------------
% 0.21/0.53  % (6872)------------------------------
% 0.21/0.53  % (6865)Success in time 0.16 s
%------------------------------------------------------------------------------
