%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:50 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 134 expanded)
%              Number of leaves         :   11 (  40 expanded)
%              Depth                    :   13
%              Number of atoms          :   99 ( 247 expanded)
%              Number of equality atoms :   41 ( 131 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f153,plain,(
    $false ),
    inference(global_subsumption,[],[f112,f139])).

fof(f139,plain,(
    r2_hidden(sK1,sK0) ),
    inference(backward_demodulation,[],[f55,f129])).

fof(f129,plain,(
    sK1 = sK2(sK0) ),
    inference(unit_resulting_resolution,[],[f106,f52])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_enumset1(X0,X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f30,f39])).

fof(f39,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f19,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f21,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f21,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f19,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f106,plain,(
    r2_hidden(sK2(sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f50,f50,f50,f50,f86,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK2(sK0),X4)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(sK0,X0)
      | ~ r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f73,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK2(sK0),X3)
      | ~ r1_tarski(sK0,X0)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f69,f26])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(sK0),X2)
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(sK0,X0)
      | ~ r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f67,f26])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(sK0),X1)
      | ~ r1_tarski(sK0,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f63,f26])).

fof(f63,plain,(
    ! [X2] :
      ( r2_hidden(sK2(sK0),X2)
      | ~ r1_tarski(sK0,X2) ) ),
    inference(resolution,[],[f26,f55])).

fof(f86,plain,(
    r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f41,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f22])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f41,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f16,f22,f39])).

fof(f16,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

fof(f50,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f55,plain,(
    r2_hidden(sK2(sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f17,f20])).

fof(f20,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f17,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f13])).

fof(f112,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f95,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f39])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f95,plain,(
    ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f40,f86,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f40,plain,(
    sK0 != k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f18,f39])).

fof(f18,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:44:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (1460)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.47  % (1444)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.47  % (1444)Refutation not found, incomplete strategy% (1444)------------------------------
% 0.20/0.47  % (1444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (1444)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (1444)Memory used [KB]: 10618
% 0.20/0.47  % (1444)Time elapsed: 0.060 s
% 0.20/0.47  % (1444)------------------------------
% 0.20/0.47  % (1444)------------------------------
% 0.20/0.48  % (1460)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f153,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(global_subsumption,[],[f112,f139])).
% 0.20/0.48  fof(f139,plain,(
% 0.20/0.48    r2_hidden(sK1,sK0)),
% 0.20/0.48    inference(backward_demodulation,[],[f55,f129])).
% 0.20/0.48  fof(f129,plain,(
% 0.20/0.48    sK1 = sK2(sK0)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f106,f52])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ( ! [X2,X0] : (~r2_hidden(X2,k2_enumset1(X0,X0,X0,X0)) | X0 = X2) )),
% 0.20/0.48    inference(equality_resolution,[],[f44])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 0.20/0.48    inference(definition_unfolding,[],[f30,f39])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f19,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f21,f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    r2_hidden(sK2(sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f50,f50,f50,f50,f86,f75])).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(sK2(sK0),X4) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~r1_tarski(sK0,X0) | ~r1_tarski(X3,X4)) )),
% 0.20/0.48    inference(resolution,[],[f73,f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.48  fof(f73,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (r2_hidden(sK2(sK0),X3) | ~r1_tarski(sK0,X0) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3)) )),
% 0.20/0.48    inference(resolution,[],[f69,f26])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r2_hidden(sK2(sK0),X2) | ~r1_tarski(X0,X1) | ~r1_tarski(sK0,X0) | ~r1_tarski(X1,X2)) )),
% 0.20/0.48    inference(resolution,[],[f67,f26])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(sK2(sK0),X1) | ~r1_tarski(sK0,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(resolution,[],[f63,f26])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    ( ! [X2] : (r2_hidden(sK2(sK0),X2) | ~r1_tarski(sK0,X2)) )),
% 0.20/0.48    inference(resolution,[],[f26,f55])).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f41,f48])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f36,f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 0.20/0.48    inference(definition_unfolding,[],[f16,f22,f39])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.20/0.48    inference(negated_conjecture,[],[f11])).
% 0.20/0.48  fof(f11,conjecture,(
% 0.20/0.48    ! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.48    inference(equality_resolution,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    r2_hidden(sK2(sK0),sK0)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f17,f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    k1_xboole_0 != sK0),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    ~r2_hidden(sK1,sK0)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f95,f47])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f33,f39])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,axiom,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.20/0.48  fof(f95,plain,(
% 0.20/0.48    ~r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f40,f86,f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f3])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    sK0 != k2_enumset1(sK1,sK1,sK1,sK1)),
% 0.20/0.48    inference(definition_unfolding,[],[f18,f39])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    sK0 != k1_tarski(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (1460)------------------------------
% 0.20/0.48  % (1460)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (1460)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (1460)Memory used [KB]: 6268
% 0.20/0.48  % (1460)Time elapsed: 0.066 s
% 0.20/0.48  % (1460)------------------------------
% 0.20/0.48  % (1460)------------------------------
% 0.20/0.48  % (1435)Success in time 0.122 s
%------------------------------------------------------------------------------
