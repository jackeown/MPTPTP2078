%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   28 (  49 expanded)
%              Number of leaves         :    6 (  14 expanded)
%              Depth                    :   11
%              Number of atoms          :   46 ( 100 expanded)
%              Number of equality atoms :   12 (  21 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f561,plain,(
    $false ),
    inference(subsumption_resolution,[],[f560,f14])).

fof(f14,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK3))
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK3))
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).

fof(f560,plain,(
    r1_tarski(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f551,f16])).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f551,plain,(
    r1_tarski(k2_xboole_0(sK2,sK0),k2_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f219,f124])).

fof(f124,plain,(
    ! [X0] : k2_xboole_0(X0,sK3) = k2_xboole_0(sK2,k2_xboole_0(X0,sK3)) ),
    inference(superposition,[],[f58,f16])).

fof(f58,plain,(
    ! [X15] : k2_xboole_0(sK3,X15) = k2_xboole_0(sK2,k2_xboole_0(sK3,X15)) ),
    inference(superposition,[],[f18,f24])).

fof(f24,plain,(
    sK3 = k2_xboole_0(sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f13,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f13,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f18,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f219,plain,(
    ! [X14,X15] : r1_tarski(k2_xboole_0(X15,sK0),k2_xboole_0(X15,k2_xboole_0(sK1,X14))) ),
    inference(superposition,[],[f67,f56])).

fof(f56,plain,(
    ! [X13] : k2_xboole_0(sK1,X13) = k2_xboole_0(sK0,k2_xboole_0(sK1,X13)) ),
    inference(superposition,[],[f18,f23])).

fof(f23,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f12,f17])).

fof(f12,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f67,plain,(
    ! [X14,X12,X13] : r1_tarski(k2_xboole_0(X12,X13),k2_xboole_0(X12,k2_xboole_0(X13,X14))) ),
    inference(superposition,[],[f15,f18])).

fof(f15,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:46:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.43  % (24688)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.44  % (24684)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.45  % (24685)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.46  % (24681)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.46  % (24682)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.47  % (24683)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.47  % (24681)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f561,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(subsumption_resolution,[],[f560,f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ~r1_tarski(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK3))),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ~r1_tarski(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK3)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3] : (~r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => (~r1_tarski(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK3)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3] : (~r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3] : (~r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) & (r1_tarski(X2,X3) & r1_tarski(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)))),
% 0.21/0.47    inference(negated_conjecture,[],[f5])).
% 0.21/0.47  fof(f5,conjecture,(
% 0.21/0.47    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).
% 0.21/0.47  fof(f560,plain,(
% 0.21/0.47    r1_tarski(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK3))),
% 0.21/0.47    inference(forward_demodulation,[],[f551,f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.47  fof(f551,plain,(
% 0.21/0.47    r1_tarski(k2_xboole_0(sK2,sK0),k2_xboole_0(sK1,sK3))),
% 0.21/0.47    inference(superposition,[],[f219,f124])).
% 0.21/0.47  fof(f124,plain,(
% 0.21/0.47    ( ! [X0] : (k2_xboole_0(X0,sK3) = k2_xboole_0(sK2,k2_xboole_0(X0,sK3))) )),
% 0.21/0.47    inference(superposition,[],[f58,f16])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    ( ! [X15] : (k2_xboole_0(sK3,X15) = k2_xboole_0(sK2,k2_xboole_0(sK3,X15))) )),
% 0.21/0.47    inference(superposition,[],[f18,f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    sK3 = k2_xboole_0(sK2,sK3)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f13,f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    r1_tarski(sK2,sK3)),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.21/0.47  fof(f219,plain,(
% 0.21/0.47    ( ! [X14,X15] : (r1_tarski(k2_xboole_0(X15,sK0),k2_xboole_0(X15,k2_xboole_0(sK1,X14)))) )),
% 0.21/0.47    inference(superposition,[],[f67,f56])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ( ! [X13] : (k2_xboole_0(sK1,X13) = k2_xboole_0(sK0,k2_xboole_0(sK1,X13))) )),
% 0.21/0.47    inference(superposition,[],[f18,f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    sK1 = k2_xboole_0(sK0,sK1)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f12,f17])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    r1_tarski(sK0,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    ( ! [X14,X12,X13] : (r1_tarski(k2_xboole_0(X12,X13),k2_xboole_0(X12,k2_xboole_0(X13,X14)))) )),
% 0.21/0.47    inference(superposition,[],[f15,f18])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (24681)------------------------------
% 0.21/0.47  % (24681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (24681)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (24681)Memory used [KB]: 6524
% 0.21/0.47  % (24681)Time elapsed: 0.036 s
% 0.21/0.47  % (24681)------------------------------
% 0.21/0.47  % (24681)------------------------------
% 0.21/0.47  % (24678)Success in time 0.117 s
%------------------------------------------------------------------------------
