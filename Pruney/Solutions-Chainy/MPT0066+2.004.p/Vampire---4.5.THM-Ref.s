%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   33 (  92 expanded)
%              Number of leaves         :    5 (  20 expanded)
%              Depth                    :   15
%              Number of atoms          :   60 ( 207 expanded)
%              Number of equality atoms :   11 (  24 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f55,plain,(
    $false ),
    inference(subsumption_resolution,[],[f53,f21])).

fof(f21,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f53,plain,(
    r2_xboole_0(sK0,sK0) ),
    inference(backward_demodulation,[],[f40,f47])).

fof(f47,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f45,f22])).

fof(f22,plain,
    ( r2_xboole_0(sK0,sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f12,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f12,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r2_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r2_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_xboole_0(X1,X2)
          & r1_tarski(X0,X1) )
       => r2_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_xboole_1)).

fof(f45,plain,(
    ~ r2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f40,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | ~ r2_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ~ r2_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

fof(f40,plain,(
    r2_xboole_0(sK1,sK0) ),
    inference(backward_demodulation,[],[f13,f38])).

fof(f38,plain,(
    sK0 = sK2 ),
    inference(subsumption_resolution,[],[f36,f14])).

fof(f14,plain,(
    ~ r2_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f36,plain,
    ( sK0 = sK2
    | r2_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f34,f19])).

fof(f34,plain,(
    r1_tarski(sK0,sK2) ),
    inference(resolution,[],[f33,f13])).

fof(f33,plain,(
    ! [X2] :
      ( ~ r2_xboole_0(sK1,X2)
      | r1_tarski(sK0,X2) ) ),
    inference(resolution,[],[f28,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | r1_tarski(sK0,X0) ) ),
    inference(superposition,[],[f20,f23])).

fof(f23,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f12,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f13,plain,(
    r2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:11:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (29058)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.41  % (29058)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.41  % SZS output start Proof for theBenchmark
% 0.20/0.41  fof(f55,plain,(
% 0.20/0.41    $false),
% 0.20/0.41    inference(subsumption_resolution,[],[f53,f21])).
% 0.20/0.41  fof(f21,plain,(
% 0.20/0.41    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 0.20/0.41    inference(equality_resolution,[],[f18])).
% 0.20/0.41  fof(f18,plain,(
% 0.20/0.41    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f2])).
% 0.20/0.41  fof(f2,axiom,(
% 0.20/0.41    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.20/0.41  fof(f53,plain,(
% 0.20/0.41    r2_xboole_0(sK0,sK0)),
% 0.20/0.41    inference(backward_demodulation,[],[f40,f47])).
% 0.20/0.41  fof(f47,plain,(
% 0.20/0.41    sK0 = sK1),
% 0.20/0.41    inference(resolution,[],[f45,f22])).
% 0.20/0.41  fof(f22,plain,(
% 0.20/0.41    r2_xboole_0(sK0,sK1) | sK0 = sK1),
% 0.20/0.41    inference(resolution,[],[f12,f19])).
% 0.20/0.41  fof(f19,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f2])).
% 0.20/0.41  fof(f12,plain,(
% 0.20/0.41    r1_tarski(sK0,sK1)),
% 0.20/0.41    inference(cnf_transformation,[],[f8])).
% 0.20/0.41  fof(f8,plain,(
% 0.20/0.41    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r2_xboole_0(X1,X2) & r1_tarski(X0,X1))),
% 0.20/0.41    inference(flattening,[],[f7])).
% 0.20/0.41  fof(f7,plain,(
% 0.20/0.41    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & (r2_xboole_0(X1,X2) & r1_tarski(X0,X1)))),
% 0.20/0.41    inference(ennf_transformation,[],[f6])).
% 0.20/0.41  fof(f6,negated_conjecture,(
% 0.20/0.41    ~! [X0,X1,X2] : ((r2_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.20/0.41    inference(negated_conjecture,[],[f5])).
% 0.20/0.41  fof(f5,conjecture,(
% 0.20/0.41    ! [X0,X1,X2] : ((r2_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_xboole_1)).
% 0.20/0.41  fof(f45,plain,(
% 0.20/0.41    ~r2_xboole_0(sK0,sK1)),
% 0.20/0.41    inference(resolution,[],[f40,f15])).
% 0.20/0.41  fof(f15,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | ~r2_xboole_0(X1,X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f9])).
% 0.20/0.41  fof(f9,plain,(
% 0.20/0.41    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1))),
% 0.20/0.41    inference(ennf_transformation,[],[f1])).
% 0.20/0.41  fof(f1,axiom,(
% 0.20/0.41    ! [X0,X1] : (r2_xboole_0(X0,X1) => ~r2_xboole_0(X1,X0))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).
% 0.20/0.41  fof(f40,plain,(
% 0.20/0.41    r2_xboole_0(sK1,sK0)),
% 0.20/0.41    inference(backward_demodulation,[],[f13,f38])).
% 0.20/0.41  fof(f38,plain,(
% 0.20/0.41    sK0 = sK2),
% 0.20/0.41    inference(subsumption_resolution,[],[f36,f14])).
% 0.20/0.41  fof(f14,plain,(
% 0.20/0.41    ~r2_xboole_0(sK0,sK2)),
% 0.20/0.41    inference(cnf_transformation,[],[f8])).
% 0.20/0.41  fof(f36,plain,(
% 0.20/0.41    sK0 = sK2 | r2_xboole_0(sK0,sK2)),
% 0.20/0.41    inference(resolution,[],[f34,f19])).
% 0.20/0.41  fof(f34,plain,(
% 0.20/0.41    r1_tarski(sK0,sK2)),
% 0.20/0.41    inference(resolution,[],[f33,f13])).
% 0.20/0.41  fof(f33,plain,(
% 0.20/0.41    ( ! [X2] : (~r2_xboole_0(sK1,X2) | r1_tarski(sK0,X2)) )),
% 0.20/0.41    inference(resolution,[],[f28,f17])).
% 0.20/0.41  fof(f17,plain,(
% 0.20/0.41    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f2])).
% 0.20/0.41  fof(f28,plain,(
% 0.20/0.41    ( ! [X0] : (~r1_tarski(sK1,X0) | r1_tarski(sK0,X0)) )),
% 0.20/0.41    inference(superposition,[],[f20,f23])).
% 0.20/0.41  fof(f23,plain,(
% 0.20/0.41    sK1 = k2_xboole_0(sK0,sK1)),
% 0.20/0.41    inference(resolution,[],[f12,f16])).
% 0.20/0.41  fof(f16,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.20/0.41    inference(cnf_transformation,[],[f10])).
% 0.20/0.41  fof(f10,plain,(
% 0.20/0.41    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.41    inference(ennf_transformation,[],[f4])).
% 0.20/0.41  fof(f4,axiom,(
% 0.20/0.41    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.41  fof(f20,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f11])).
% 0.20/0.41  fof(f11,plain,(
% 0.20/0.41    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.20/0.41    inference(ennf_transformation,[],[f3])).
% 0.20/0.41  fof(f3,axiom,(
% 0.20/0.41    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.20/0.41  fof(f13,plain,(
% 0.20/0.41    r2_xboole_0(sK1,sK2)),
% 0.20/0.41    inference(cnf_transformation,[],[f8])).
% 0.20/0.41  % SZS output end Proof for theBenchmark
% 0.20/0.41  % (29058)------------------------------
% 0.20/0.41  % (29058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (29058)Termination reason: Refutation
% 0.20/0.41  
% 0.20/0.41  % (29058)Memory used [KB]: 1663
% 0.20/0.41  % (29058)Time elapsed: 0.004 s
% 0.20/0.41  % (29058)------------------------------
% 0.20/0.41  % (29058)------------------------------
% 0.20/0.41  % (29044)Success in time 0.056 s
%------------------------------------------------------------------------------
