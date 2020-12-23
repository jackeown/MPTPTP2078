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
% DateTime   : Thu Dec  3 12:33:53 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :   15 (  19 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    6
%              Number of atoms          :   15 (  19 expanded)
%              Number of equality atoms :   14 (  18 expanded)
%              Maximal formula depth    :    9 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f19])).

fof(f19,plain,(
    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5)) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5)) ),
    inference(forward_demodulation,[],[f18,f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_tarski(X2,X3)) ),
    inference(definition_unfolding,[],[f15,f14])).

fof(f14,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).

fof(f15,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_enumset1)).

fof(f18,plain,(
    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5)) != k2_xboole_0(k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)) ),
    inference(definition_unfolding,[],[f12,f14,f16])).

fof(f16,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)),k2_tarski(X6,X7)) ),
    inference(definition_unfolding,[],[f13,f14])).

fof(f13,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

fof(f12,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k6_enumset1(sK0,sK0,sK0,sK1,sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:51:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.36  ipcrm: permission denied for id (733872128)
% 0.14/0.36  ipcrm: permission denied for id (733904898)
% 0.21/0.37  ipcrm: permission denied for id (733937668)
% 0.21/0.37  ipcrm: permission denied for id (734101512)
% 0.21/0.37  ipcrm: permission denied for id (734199819)
% 0.21/0.38  ipcrm: permission denied for id (734363663)
% 0.21/0.38  ipcrm: permission denied for id (734429201)
% 0.21/0.38  ipcrm: permission denied for id (734461970)
% 0.21/0.38  ipcrm: permission denied for id (734494739)
% 0.21/0.39  ipcrm: permission denied for id (734560277)
% 0.21/0.39  ipcrm: permission denied for id (734593047)
% 0.21/0.39  ipcrm: permission denied for id (734625816)
% 0.21/0.39  ipcrm: permission denied for id (734691356)
% 0.21/0.40  ipcrm: permission denied for id (734855205)
% 0.21/0.41  ipcrm: permission denied for id (734920744)
% 0.21/0.41  ipcrm: permission denied for id (734986282)
% 0.21/0.41  ipcrm: permission denied for id (735051821)
% 0.21/0.41  ipcrm: permission denied for id (735084590)
% 0.21/0.42  ipcrm: permission denied for id (735117359)
% 0.21/0.42  ipcrm: permission denied for id (735182898)
% 0.21/0.42  ipcrm: permission denied for id (735248436)
% 0.21/0.42  ipcrm: permission denied for id (735313974)
% 0.21/0.43  ipcrm: permission denied for id (735445050)
% 0.21/0.43  ipcrm: permission denied for id (735510588)
% 0.21/0.43  ipcrm: permission denied for id (735543358)
% 0.21/0.43  ipcrm: permission denied for id (735608896)
% 0.21/0.44  ipcrm: permission denied for id (735739973)
% 0.21/0.44  ipcrm: permission denied for id (735772742)
% 0.21/0.44  ipcrm: permission denied for id (735805511)
% 0.21/0.45  ipcrm: permission denied for id (735871049)
% 0.21/0.45  ipcrm: permission denied for id (735936587)
% 0.21/0.45  ipcrm: permission denied for id (735969356)
% 0.21/0.45  ipcrm: permission denied for id (736002125)
% 0.21/0.45  ipcrm: permission denied for id (736034894)
% 0.21/0.45  ipcrm: permission denied for id (736067664)
% 0.21/0.45  ipcrm: permission denied for id (736133201)
% 0.21/0.46  ipcrm: permission denied for id (736165970)
% 0.21/0.46  ipcrm: permission denied for id (736231509)
% 0.21/0.46  ipcrm: permission denied for id (736264278)
% 0.21/0.46  ipcrm: permission denied for id (736362584)
% 0.21/0.47  ipcrm: permission denied for id (736460891)
% 0.21/0.47  ipcrm: permission denied for id (736493660)
% 0.21/0.47  ipcrm: permission denied for id (736526430)
% 0.21/0.48  ipcrm: permission denied for id (736723049)
% 0.21/0.49  ipcrm: permission denied for id (736821357)
% 0.21/0.49  ipcrm: permission denied for id (736854126)
% 0.21/0.49  ipcrm: permission denied for id (736919664)
% 0.21/0.49  ipcrm: permission denied for id (736952433)
% 0.21/0.49  ipcrm: permission denied for id (736985204)
% 0.21/0.50  ipcrm: permission denied for id (737017974)
% 0.67/0.63  % (13421)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.67/0.63  % (13428)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.67/0.63  % (13429)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.67/0.64  % (13444)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.67/0.64  % (13428)Refutation found. Thanks to Tanya!
% 0.67/0.64  % SZS status Theorem for theBenchmark
% 0.67/0.64  % SZS output start Proof for theBenchmark
% 0.67/0.64  fof(f20,plain,(
% 0.67/0.64    $false),
% 0.67/0.64    inference(trivial_inequality_removal,[],[f19])).
% 0.67/0.64  fof(f19,plain,(
% 0.67/0.64    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5)) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5))),
% 0.67/0.64    inference(forward_demodulation,[],[f18,f17])).
% 0.67/0.64  fof(f17,plain,(
% 0.67/0.64    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_tarski(X2,X3))) )),
% 0.67/0.64    inference(definition_unfolding,[],[f15,f14])).
% 0.67/0.64  fof(f14,plain,(
% 0.67/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 0.67/0.64    inference(cnf_transformation,[],[f4])).
% 0.67/0.64  fof(f4,axiom,(
% 0.67/0.64    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))),
% 0.67/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).
% 0.67/0.64  fof(f15,plain,(
% 0.67/0.64    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.67/0.64    inference(cnf_transformation,[],[f8])).
% 0.67/0.64  fof(f8,axiom,(
% 0.67/0.64    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)),
% 0.67/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_enumset1)).
% 0.67/0.64  fof(f18,plain,(
% 0.67/0.64    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5)) != k2_xboole_0(k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5))),
% 0.67/0.64    inference(definition_unfolding,[],[f12,f14,f16])).
% 0.67/0.64  fof(f16,plain,(
% 0.67/0.64    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)),k2_tarski(X6,X7))) )),
% 0.67/0.64    inference(definition_unfolding,[],[f13,f14])).
% 0.67/0.64  fof(f13,plain,(
% 0.67/0.64    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) )),
% 0.67/0.64    inference(cnf_transformation,[],[f6])).
% 0.67/0.64  fof(f6,axiom,(
% 0.67/0.64    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 0.67/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).
% 0.67/0.64  fof(f12,plain,(
% 0.67/0.64    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k6_enumset1(sK0,sK0,sK0,sK1,sK2,sK3,sK4,sK5)),
% 0.67/0.64    inference(cnf_transformation,[],[f11])).
% 0.67/0.64  fof(f11,plain,(
% 0.67/0.64    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)),
% 0.67/0.64    inference(ennf_transformation,[],[f10])).
% 0.67/0.64  fof(f10,negated_conjecture,(
% 0.67/0.64    ~! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)),
% 0.67/0.64    inference(negated_conjecture,[],[f9])).
% 0.67/0.64  fof(f9,conjecture,(
% 0.67/0.64    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)),
% 0.67/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_enumset1)).
% 0.67/0.64  % SZS output end Proof for theBenchmark
% 0.67/0.64  % (13428)------------------------------
% 0.67/0.64  % (13428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.67/0.64  % (13428)Termination reason: Refutation
% 0.67/0.64  
% 0.67/0.64  % (13428)Memory used [KB]: 10618
% 0.67/0.64  % (13428)Time elapsed: 0.002 s
% 0.67/0.64  % (13428)------------------------------
% 0.67/0.64  % (13428)------------------------------
% 0.67/0.64  % (13285)Success in time 0.283 s
%------------------------------------------------------------------------------
