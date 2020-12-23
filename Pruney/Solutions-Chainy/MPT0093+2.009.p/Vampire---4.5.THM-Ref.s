%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:44 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   28 (  39 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :   11
%              Number of atoms          :   42 (  70 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f129,plain,(
    $false ),
    inference(subsumption_resolution,[],[f124,f12])).

fof(f12,plain,(
    ~ r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) )
       => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f124,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(trivial_inequality_removal,[],[f123])).

fof(f123,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f18,f115])).

fof(f115,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f112,f28])).

fof(f28,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f25,f13])).

fof(f13,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f25,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f14,f13])).

fof(f14,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f112,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f34,f20])).

fof(f20,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f16,f11])).

fof(f11,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f34,plain,(
    ! [X5] : k4_xboole_0(sK0,k4_xboole_0(sK1,X5)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X5)) ),
    inference(superposition,[],[f19,f21])).

fof(f21,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f17,f10])).

fof(f10,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f19,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:00:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.43  % (2636)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.23/0.43  % (2636)Refutation found. Thanks to Tanya!
% 0.23/0.43  % SZS status Theorem for theBenchmark
% 0.23/0.44  % SZS output start Proof for theBenchmark
% 0.23/0.44  fof(f129,plain,(
% 0.23/0.44    $false),
% 0.23/0.44    inference(subsumption_resolution,[],[f124,f12])).
% 0.23/0.44  fof(f12,plain,(
% 0.23/0.44    ~r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.23/0.44    inference(cnf_transformation,[],[f9])).
% 0.23/0.44  fof(f9,plain,(
% 0.23/0.44    ? [X0,X1,X2] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X2) & r1_tarski(X0,X1))),
% 0.23/0.44    inference(flattening,[],[f8])).
% 0.23/0.44  fof(f8,plain,(
% 0.23/0.44    ? [X0,X1,X2] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) & (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.23/0.44    inference(ennf_transformation,[],[f7])).
% 0.23/0.44  fof(f7,negated_conjecture,(
% 0.23/0.44    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.23/0.44    inference(negated_conjecture,[],[f6])).
% 0.23/0.44  fof(f6,conjecture,(
% 0.23/0.44    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.23/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).
% 0.23/0.44  fof(f124,plain,(
% 0.23/0.44    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.23/0.44    inference(trivial_inequality_removal,[],[f123])).
% 0.23/0.44  fof(f123,plain,(
% 0.23/0.44    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.23/0.44    inference(superposition,[],[f18,f115])).
% 0.23/0.44  fof(f115,plain,(
% 0.23/0.44    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.23/0.44    inference(forward_demodulation,[],[f112,f28])).
% 0.23/0.44  fof(f28,plain,(
% 0.23/0.44    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 0.23/0.44    inference(forward_demodulation,[],[f25,f13])).
% 0.23/0.44  fof(f13,plain,(
% 0.23/0.44    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.23/0.44    inference(cnf_transformation,[],[f3])).
% 0.23/0.44  fof(f3,axiom,(
% 0.23/0.44    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.23/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.23/0.44  fof(f25,plain,(
% 0.23/0.44    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0)) )),
% 0.23/0.44    inference(superposition,[],[f14,f13])).
% 0.23/0.44  fof(f14,plain,(
% 0.23/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.23/0.44    inference(cnf_transformation,[],[f4])).
% 0.23/0.44  fof(f4,axiom,(
% 0.23/0.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.23/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.23/0.44  fof(f112,plain,(
% 0.23/0.44    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.23/0.44    inference(superposition,[],[f34,f20])).
% 0.23/0.44  fof(f20,plain,(
% 0.23/0.44    k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 0.23/0.44    inference(resolution,[],[f16,f11])).
% 0.23/0.44  fof(f11,plain,(
% 0.23/0.44    r1_xboole_0(sK0,sK2)),
% 0.23/0.44    inference(cnf_transformation,[],[f9])).
% 0.23/0.44  fof(f16,plain,(
% 0.23/0.44    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.23/0.44    inference(cnf_transformation,[],[f1])).
% 0.23/0.44  fof(f1,axiom,(
% 0.23/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.23/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.23/0.44  fof(f34,plain,(
% 0.23/0.44    ( ! [X5] : (k4_xboole_0(sK0,k4_xboole_0(sK1,X5)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X5))) )),
% 0.23/0.44    inference(superposition,[],[f19,f21])).
% 0.23/0.44  fof(f21,plain,(
% 0.23/0.44    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.23/0.44    inference(resolution,[],[f17,f10])).
% 0.23/0.44  fof(f10,plain,(
% 0.23/0.44    r1_tarski(sK0,sK1)),
% 0.23/0.44    inference(cnf_transformation,[],[f9])).
% 0.23/0.44  fof(f17,plain,(
% 0.23/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.23/0.44    inference(cnf_transformation,[],[f2])).
% 0.23/0.44  fof(f2,axiom,(
% 0.23/0.44    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.23/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.23/0.44  fof(f19,plain,(
% 0.23/0.44    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.23/0.44    inference(cnf_transformation,[],[f5])).
% 0.23/0.44  fof(f5,axiom,(
% 0.23/0.44    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.23/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 0.23/0.44  fof(f18,plain,(
% 0.23/0.44    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 0.23/0.44    inference(cnf_transformation,[],[f2])).
% 0.23/0.44  % SZS output end Proof for theBenchmark
% 0.23/0.44  % (2636)------------------------------
% 0.23/0.44  % (2636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.44  % (2636)Termination reason: Refutation
% 0.23/0.44  
% 0.23/0.44  % (2636)Memory used [KB]: 10618
% 0.23/0.44  % (2636)Time elapsed: 0.042 s
% 0.23/0.44  % (2636)------------------------------
% 0.23/0.44  % (2636)------------------------------
% 0.23/0.45  % (2632)Success in time 0.079 s
%------------------------------------------------------------------------------
