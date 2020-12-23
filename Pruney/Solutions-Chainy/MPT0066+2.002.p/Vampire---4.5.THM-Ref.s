%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  92 expanded)
%              Number of leaves         :    5 (  20 expanded)
%              Depth                    :   15
%              Number of atoms          :   60 ( 207 expanded)
%              Number of equality atoms :   11 (  24 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f58,plain,(
    $false ),
    inference(subsumption_resolution,[],[f56,f24])).

fof(f24,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f56,plain,(
    r2_xboole_0(sK0,sK0) ),
    inference(backward_demodulation,[],[f43,f50])).

fof(f50,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f48,f25])).

fof(f25,plain,
    ( r2_xboole_0(sK0,sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f14,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f14,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r2_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r2_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_xboole_0(X1,X2)
          & r1_tarski(X0,X1) )
       => r2_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_xboole_1)).

fof(f48,plain,(
    ~ r2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f43,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | ~ r2_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ~ r2_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

fof(f43,plain,(
    r2_xboole_0(sK1,sK0) ),
    inference(backward_demodulation,[],[f15,f41])).

fof(f41,plain,(
    sK0 = sK2 ),
    inference(subsumption_resolution,[],[f39,f16])).

fof(f16,plain,(
    ~ r2_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f39,plain,
    ( sK0 = sK2
    | r2_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f37,f22])).

fof(f37,plain,(
    r1_tarski(sK0,sK2) ),
    inference(resolution,[],[f36,f15])).

fof(f36,plain,(
    ! [X2] :
      ( ~ r2_xboole_0(sK1,X2)
      | r1_tarski(sK0,X2) ) ),
    inference(resolution,[],[f34,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | r1_tarski(sK0,X0) ) ),
    inference(superposition,[],[f23,f26])).

fof(f26,plain,(
    sK1 = k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(resolution,[],[f14,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f15,plain,(
    r2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:33:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (24779)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.46  % (24779)Refutation not found, incomplete strategy% (24779)------------------------------
% 0.21/0.46  % (24779)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (24779)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (24779)Memory used [KB]: 10618
% 0.21/0.46  % (24779)Time elapsed: 0.051 s
% 0.21/0.46  % (24779)------------------------------
% 0.21/0.46  % (24779)------------------------------
% 0.21/0.47  % (24791)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (24791)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(subsumption_resolution,[],[f56,f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 0.21/0.47    inference(equality_resolution,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    r2_xboole_0(sK0,sK0)),
% 0.21/0.47    inference(backward_demodulation,[],[f43,f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    sK0 = sK1),
% 0.21/0.47    inference(resolution,[],[f48,f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    r2_xboole_0(sK0,sK1) | sK0 = sK1),
% 0.21/0.47    inference(resolution,[],[f14,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    r1_tarski(sK0,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r2_xboole_0(X1,X2) & r1_tarski(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & (r2_xboole_0(X1,X2) & r1_tarski(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : ((r2_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.21/0.47    inference(negated_conjecture,[],[f6])).
% 0.21/0.47  fof(f6,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : ((r2_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_xboole_1)).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ~r2_xboole_0(sK0,sK1)),
% 0.21/0.47    inference(resolution,[],[f43,f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | ~r2_xboole_0(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (r2_xboole_0(X0,X1) => ~r2_xboole_0(X1,X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    r2_xboole_0(sK1,sK0)),
% 0.21/0.47    inference(backward_demodulation,[],[f15,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    sK0 = sK2),
% 0.21/0.47    inference(subsumption_resolution,[],[f39,f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ~r2_xboole_0(sK0,sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    sK0 = sK2 | r2_xboole_0(sK0,sK2)),
% 0.21/0.47    inference(resolution,[],[f37,f22])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    r1_tarski(sK0,sK2)),
% 0.21/0.47    inference(resolution,[],[f36,f15])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X2] : (~r2_xboole_0(sK1,X2) | r1_tarski(sK0,X2)) )),
% 0.21/0.47    inference(resolution,[],[f34,f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X0] : (~r1_tarski(sK1,X0) | r1_tarski(sK0,X0)) )),
% 0.21/0.47    inference(superposition,[],[f23,f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    sK1 = k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 0.21/0.47    inference(resolution,[],[f14,f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    r2_xboole_0(sK1,sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (24791)------------------------------
% 0.21/0.47  % (24791)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (24791)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (24791)Memory used [KB]: 1663
% 0.21/0.47  % (24791)Time elapsed: 0.062 s
% 0.21/0.47  % (24791)------------------------------
% 0.21/0.47  % (24791)------------------------------
% 0.21/0.47  % (24777)Success in time 0.117 s
%------------------------------------------------------------------------------
