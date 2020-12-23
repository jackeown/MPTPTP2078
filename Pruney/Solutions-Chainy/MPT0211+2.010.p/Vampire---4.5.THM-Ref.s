%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:44 EST 2020

% Result     : Theorem 4.23s
% Output     : Refutation 4.23s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 139 expanded)
%              Number of leaves         :   12 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :   53 ( 140 expanded)
%              Number of equality atoms :   52 ( 139 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8336,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f8312])).

fof(f8312,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) ),
    inference(superposition,[],[f8282,f2465])).

fof(f2465,plain,(
    ! [X87,X85,X86] : k1_enumset1(X85,X87,X86) = k2_enumset1(X87,X85,X86,X85) ),
    inference(superposition,[],[f2413,f1880])).

fof(f1880,plain,(
    ! [X4,X5,X3] : k1_enumset1(X3,X5,X4) = k2_enumset1(X3,X4,X3,X5) ),
    inference(superposition,[],[f1847,f1728])).

fof(f1728,plain,(
    ! [X4,X5,X3] : k1_enumset1(X3,X4,X5) = k2_enumset1(X3,X3,X5,X4) ),
    inference(superposition,[],[f1697,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f1697,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X4,X5,X7,X6) ),
    inference(superposition,[],[f1238,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f1238,plain,(
    ! [X6,X8,X7,X9] : k2_enumset1(X9,X6,X7,X8) = k2_xboole_0(k1_tarski(X9),k1_enumset1(X6,X8,X7)) ),
    inference(superposition,[],[f33,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).

fof(f1847,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X7,X6) = k2_enumset1(X4,X7,X5,X6) ),
    inference(superposition,[],[f1240,f1238])).

fof(f1240,plain,(
    ! [X14,X17,X15,X16] : k2_enumset1(X17,X14,X15,X16) = k2_xboole_0(k1_tarski(X17),k1_enumset1(X15,X16,X14)) ),
    inference(superposition,[],[f33,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

fof(f2413,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X7,X4,X5,X6) ),
    inference(superposition,[],[f1250,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f1250,plain,(
    ! [X6,X4,X7,X5] : k2_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X4)) = k2_enumset1(X4,X5,X6,X7) ),
    inference(superposition,[],[f33,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f8282,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK0,sK2,sK0) ),
    inference(superposition,[],[f138,f6510])).

fof(f6510,plain,(
    ! [X54,X52,X55,X53] : k2_enumset1(X55,X53,X54,X52) = k2_xboole_0(k2_tarski(X52,X55),k2_tarski(X53,X54)) ),
    inference(forward_demodulation,[],[f6449,f33])).

fof(f6449,plain,(
    ! [X54,X52,X55,X53] : k2_xboole_0(k2_tarski(X52,X55),k2_tarski(X53,X54)) = k2_xboole_0(k1_tarski(X55),k1_enumset1(X53,X54,X52)) ),
    inference(superposition,[],[f151,f1372])).

fof(f1372,plain,(
    ! [X19,X20,X18] : k1_enumset1(X18,X19,X20) = k2_xboole_0(k1_tarski(X20),k2_tarski(X18,X19)) ),
    inference(superposition,[],[f1327,f22])).

fof(f1327,plain,(
    ! [X4,X5,X3] : k1_enumset1(X3,X4,X5) = k2_xboole_0(k2_tarski(X3,X4),k1_tarski(X5)) ),
    inference(forward_demodulation,[],[f1295,f28])).

fof(f1295,plain,(
    ! [X4,X5,X3] : k2_xboole_0(k2_tarski(X3,X4),k1_tarski(X5)) = k2_enumset1(X3,X3,X4,X5) ),
    inference(superposition,[],[f34,f23])).

fof(f23,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f151,plain,(
    ! [X14,X15,X13] : k2_xboole_0(k1_tarski(X13),k2_xboole_0(k1_tarski(X14),X15)) = k2_xboole_0(k2_tarski(X14,X13),X15) ),
    inference(superposition,[],[f31,f126])).

fof(f126,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0)) ),
    inference(forward_demodulation,[],[f121,f47])).

fof(f47,plain,(
    ! [X14,X15] : k2_tarski(X14,X15) = k1_enumset1(X15,X14,X14) ),
    inference(superposition,[],[f26,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0) ),
    inference(superposition,[],[f25,f23])).

fof(f121,plain,(
    ! [X0,X1] : k1_enumset1(X1,X0,X0) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0)) ),
    inference(superposition,[],[f29,f21])).

fof(f21,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f29,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f138,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK2)) ),
    inference(forward_demodulation,[],[f137,f131])).

fof(f131,plain,(
    ! [X2,X3] : k2_tarski(X3,X2) = k2_tarski(X2,X3) ),
    inference(superposition,[],[f127,f126])).

fof(f127,plain,(
    ! [X2,X3] : k2_xboole_0(k1_tarski(X3),k1_tarski(X2)) = k2_tarski(X3,X2) ),
    inference(superposition,[],[f126,f22])).

fof(f137,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK0,sK2)) ),
    inference(backward_demodulation,[],[f20,f131])).

fof(f20,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))
   => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:08:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (817430528)
% 0.14/0.37  ipcrm: permission denied for id (817463298)
% 0.14/0.37  ipcrm: permission denied for id (817496067)
% 0.14/0.37  ipcrm: permission denied for id (817561606)
% 0.14/0.38  ipcrm: permission denied for id (817659912)
% 0.14/0.38  ipcrm: permission denied for id (817692681)
% 0.14/0.38  ipcrm: permission denied for id (817790988)
% 0.14/0.38  ipcrm: permission denied for id (817823757)
% 0.14/0.39  ipcrm: permission denied for id (817922065)
% 0.14/0.39  ipcrm: permission denied for id (817954834)
% 0.14/0.40  ipcrm: permission denied for id (818151447)
% 0.14/0.40  ipcrm: permission denied for id (818184216)
% 0.14/0.40  ipcrm: permission denied for id (818249754)
% 0.22/0.41  ipcrm: permission denied for id (818348062)
% 0.22/0.41  ipcrm: permission denied for id (818413600)
% 0.22/0.41  ipcrm: permission denied for id (818479139)
% 0.22/0.41  ipcrm: permission denied for id (818544677)
% 0.22/0.42  ipcrm: permission denied for id (818577446)
% 0.22/0.42  ipcrm: permission denied for id (818610216)
% 0.22/0.42  ipcrm: permission denied for id (818675755)
% 0.22/0.42  ipcrm: permission denied for id (818708524)
% 0.22/0.43  ipcrm: permission denied for id (818839600)
% 0.22/0.43  ipcrm: permission denied for id (818970676)
% 0.22/0.44  ipcrm: permission denied for id (819036215)
% 0.22/0.44  ipcrm: permission denied for id (819068984)
% 0.22/0.44  ipcrm: permission denied for id (819101753)
% 0.22/0.44  ipcrm: permission denied for id (819232829)
% 0.22/0.45  ipcrm: permission denied for id (819298367)
% 0.22/0.45  ipcrm: permission denied for id (819363905)
% 0.22/0.45  ipcrm: permission denied for id (819396674)
% 0.22/0.45  ipcrm: permission denied for id (819429443)
% 0.22/0.45  ipcrm: permission denied for id (819494980)
% 0.22/0.46  ipcrm: permission denied for id (819593290)
% 0.22/0.46  ipcrm: permission denied for id (819626060)
% 0.22/0.47  ipcrm: permission denied for id (819757136)
% 0.22/0.47  ipcrm: permission denied for id (819822674)
% 0.22/0.47  ipcrm: permission denied for id (819855443)
% 0.22/0.47  ipcrm: permission denied for id (819920981)
% 0.22/0.48  ipcrm: permission denied for id (819953750)
% 0.22/0.48  ipcrm: permission denied for id (819986519)
% 0.22/0.48  ipcrm: permission denied for id (820052056)
% 0.22/0.48  ipcrm: permission denied for id (820117594)
% 0.22/0.49  ipcrm: permission denied for id (820248671)
% 0.22/0.49  ipcrm: permission denied for id (820314210)
% 0.22/0.49  ipcrm: permission denied for id (820346979)
% 0.22/0.49  ipcrm: permission denied for id (820379748)
% 0.22/0.50  ipcrm: permission denied for id (820412518)
% 0.22/0.50  ipcrm: permission denied for id (820445288)
% 0.22/0.50  ipcrm: permission denied for id (820478057)
% 0.22/0.50  ipcrm: permission denied for id (820510826)
% 0.22/0.50  ipcrm: permission denied for id (820543595)
% 0.22/0.50  ipcrm: permission denied for id (820576364)
% 0.22/0.50  ipcrm: permission denied for id (820609133)
% 0.22/0.51  ipcrm: permission denied for id (820674671)
% 0.22/0.51  ipcrm: permission denied for id (820740209)
% 0.22/0.51  ipcrm: permission denied for id (820772978)
% 0.22/0.51  ipcrm: permission denied for id (820838516)
% 0.22/0.52  ipcrm: permission denied for id (820969592)
% 0.22/0.52  ipcrm: permission denied for id (821035130)
% 0.22/0.52  ipcrm: permission denied for id (821067900)
% 0.22/0.59  % (4866)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.61  % (4859)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.96/0.64  % (4861)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.96/0.64  % (4862)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.96/0.64  % (4860)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.96/0.65  % (4870)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.96/0.65  % (4869)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 1.25/0.66  % (4868)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 1.25/0.66  % (4868)Refutation not found, incomplete strategy% (4868)------------------------------
% 1.25/0.66  % (4868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.66  % (4868)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.66  
% 1.25/0.66  % (4868)Memory used [KB]: 10618
% 1.25/0.66  % (4868)Time elapsed: 0.086 s
% 1.25/0.66  % (4868)------------------------------
% 1.25/0.66  % (4868)------------------------------
% 1.25/0.66  % (4867)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 1.25/0.67  % (4858)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 1.25/0.67  % (4871)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 1.25/0.67  % (4874)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.25/0.67  % (4864)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 1.25/0.68  % (4865)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.25/0.68  % (4857)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 1.25/0.68  % (4872)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.25/0.69  % (4863)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 1.25/0.70  % (4873)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 4.23/1.09  % (4873)Refutation found. Thanks to Tanya!
% 4.23/1.09  % SZS status Theorem for theBenchmark
% 4.23/1.09  % SZS output start Proof for theBenchmark
% 4.23/1.09  fof(f8336,plain,(
% 4.23/1.09    $false),
% 4.23/1.09    inference(trivial_inequality_removal,[],[f8312])).
% 4.23/1.09  fof(f8312,plain,(
% 4.23/1.09    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)),
% 4.23/1.09    inference(superposition,[],[f8282,f2465])).
% 4.23/1.09  fof(f2465,plain,(
% 4.23/1.09    ( ! [X87,X85,X86] : (k1_enumset1(X85,X87,X86) = k2_enumset1(X87,X85,X86,X85)) )),
% 4.23/1.09    inference(superposition,[],[f2413,f1880])).
% 4.23/1.09  fof(f1880,plain,(
% 4.23/1.09    ( ! [X4,X5,X3] : (k1_enumset1(X3,X5,X4) = k2_enumset1(X3,X4,X3,X5)) )),
% 4.23/1.09    inference(superposition,[],[f1847,f1728])).
% 4.23/1.10  fof(f1728,plain,(
% 4.23/1.10    ( ! [X4,X5,X3] : (k1_enumset1(X3,X4,X5) = k2_enumset1(X3,X3,X5,X4)) )),
% 4.23/1.10    inference(superposition,[],[f1697,f28])).
% 4.23/1.10  fof(f28,plain,(
% 4.23/1.10    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 4.23/1.10    inference(cnf_transformation,[],[f12])).
% 4.23/1.10  fof(f12,axiom,(
% 4.23/1.10    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 4.23/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 4.23/1.10  fof(f1697,plain,(
% 4.23/1.10    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X4,X5,X7,X6)) )),
% 4.23/1.10    inference(superposition,[],[f1238,f33])).
% 4.23/1.10  fof(f33,plain,(
% 4.23/1.10    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 4.23/1.10    inference(cnf_transformation,[],[f8])).
% 4.23/1.10  fof(f8,axiom,(
% 4.23/1.10    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 4.23/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 4.23/1.10  fof(f1238,plain,(
% 4.23/1.10    ( ! [X6,X8,X7,X9] : (k2_enumset1(X9,X6,X7,X8) = k2_xboole_0(k1_tarski(X9),k1_enumset1(X6,X8,X7))) )),
% 4.23/1.10    inference(superposition,[],[f33,f25])).
% 4.23/1.10  fof(f25,plain,(
% 4.23/1.10    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)) )),
% 4.23/1.10    inference(cnf_transformation,[],[f14])).
% 4.23/1.10  fof(f14,axiom,(
% 4.23/1.10    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)),
% 4.23/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).
% 4.23/1.10  fof(f1847,plain,(
% 4.23/1.10    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X7,X6) = k2_enumset1(X4,X7,X5,X6)) )),
% 4.23/1.10    inference(superposition,[],[f1240,f1238])).
% 4.23/1.10  fof(f1240,plain,(
% 4.23/1.10    ( ! [X14,X17,X15,X16] : (k2_enumset1(X17,X14,X15,X16) = k2_xboole_0(k1_tarski(X17),k1_enumset1(X15,X16,X14))) )),
% 4.23/1.10    inference(superposition,[],[f33,f26])).
% 4.23/1.10  fof(f26,plain,(
% 4.23/1.10    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 4.23/1.10    inference(cnf_transformation,[],[f5])).
% 4.23/1.10  fof(f5,axiom,(
% 4.23/1.10    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 4.23/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).
% 4.23/1.10  fof(f2413,plain,(
% 4.23/1.10    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X7,X4,X5,X6)) )),
% 4.23/1.10    inference(superposition,[],[f1250,f34])).
% 4.23/1.10  fof(f34,plain,(
% 4.23/1.10    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 4.23/1.10    inference(cnf_transformation,[],[f9])).
% 4.23/1.10  fof(f9,axiom,(
% 4.23/1.10    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 4.23/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 4.23/1.10  fof(f1250,plain,(
% 4.23/1.10    ( ! [X6,X4,X7,X5] : (k2_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X4)) = k2_enumset1(X4,X5,X6,X7)) )),
% 4.23/1.10    inference(superposition,[],[f33,f22])).
% 4.23/1.10  fof(f22,plain,(
% 4.23/1.10    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 4.23/1.10    inference(cnf_transformation,[],[f1])).
% 4.23/1.10  fof(f1,axiom,(
% 4.23/1.10    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 4.23/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 4.23/1.10  fof(f8282,plain,(
% 4.23/1.10    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK0,sK2,sK0)),
% 4.23/1.10    inference(superposition,[],[f138,f6510])).
% 4.23/1.10  fof(f6510,plain,(
% 4.23/1.10    ( ! [X54,X52,X55,X53] : (k2_enumset1(X55,X53,X54,X52) = k2_xboole_0(k2_tarski(X52,X55),k2_tarski(X53,X54))) )),
% 4.23/1.10    inference(forward_demodulation,[],[f6449,f33])).
% 4.23/1.10  fof(f6449,plain,(
% 4.23/1.10    ( ! [X54,X52,X55,X53] : (k2_xboole_0(k2_tarski(X52,X55),k2_tarski(X53,X54)) = k2_xboole_0(k1_tarski(X55),k1_enumset1(X53,X54,X52))) )),
% 4.23/1.10    inference(superposition,[],[f151,f1372])).
% 4.23/1.10  fof(f1372,plain,(
% 4.23/1.10    ( ! [X19,X20,X18] : (k1_enumset1(X18,X19,X20) = k2_xboole_0(k1_tarski(X20),k2_tarski(X18,X19))) )),
% 4.23/1.10    inference(superposition,[],[f1327,f22])).
% 4.23/1.10  fof(f1327,plain,(
% 4.23/1.10    ( ! [X4,X5,X3] : (k1_enumset1(X3,X4,X5) = k2_xboole_0(k2_tarski(X3,X4),k1_tarski(X5))) )),
% 4.23/1.10    inference(forward_demodulation,[],[f1295,f28])).
% 4.23/1.10  fof(f1295,plain,(
% 4.23/1.10    ( ! [X4,X5,X3] : (k2_xboole_0(k2_tarski(X3,X4),k1_tarski(X5)) = k2_enumset1(X3,X3,X4,X5)) )),
% 4.23/1.10    inference(superposition,[],[f34,f23])).
% 4.23/1.10  fof(f23,plain,(
% 4.23/1.10    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 4.23/1.10    inference(cnf_transformation,[],[f11])).
% 4.23/1.10  fof(f11,axiom,(
% 4.23/1.10    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 4.23/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 4.23/1.10  fof(f151,plain,(
% 4.23/1.10    ( ! [X14,X15,X13] : (k2_xboole_0(k1_tarski(X13),k2_xboole_0(k1_tarski(X14),X15)) = k2_xboole_0(k2_tarski(X14,X13),X15)) )),
% 4.23/1.10    inference(superposition,[],[f31,f126])).
% 4.23/1.10  fof(f126,plain,(
% 4.23/1.10    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0))) )),
% 4.23/1.10    inference(forward_demodulation,[],[f121,f47])).
% 4.23/1.10  fof(f47,plain,(
% 4.23/1.10    ( ! [X14,X15] : (k2_tarski(X14,X15) = k1_enumset1(X15,X14,X14)) )),
% 4.23/1.10    inference(superposition,[],[f26,f35])).
% 4.23/1.10  fof(f35,plain,(
% 4.23/1.10    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0)) )),
% 4.23/1.10    inference(superposition,[],[f25,f23])).
% 4.23/1.10  fof(f121,plain,(
% 4.23/1.10    ( ! [X0,X1] : (k1_enumset1(X1,X0,X0) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0))) )),
% 4.23/1.10    inference(superposition,[],[f29,f21])).
% 4.23/1.10  fof(f21,plain,(
% 4.23/1.10    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 4.23/1.10    inference(cnf_transformation,[],[f10])).
% 4.23/1.10  fof(f10,axiom,(
% 4.23/1.10    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 4.23/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 4.23/1.10  fof(f29,plain,(
% 4.23/1.10    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 4.23/1.10    inference(cnf_transformation,[],[f7])).
% 4.23/1.10  fof(f7,axiom,(
% 4.23/1.10    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 4.23/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 4.23/1.10  fof(f31,plain,(
% 4.23/1.10    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 4.23/1.10    inference(cnf_transformation,[],[f2])).
% 4.23/1.10  fof(f2,axiom,(
% 4.23/1.10    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 4.23/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 4.23/1.10  fof(f138,plain,(
% 4.23/1.10    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK2))),
% 4.23/1.10    inference(forward_demodulation,[],[f137,f131])).
% 4.23/1.10  fof(f131,plain,(
% 4.23/1.10    ( ! [X2,X3] : (k2_tarski(X3,X2) = k2_tarski(X2,X3)) )),
% 4.23/1.10    inference(superposition,[],[f127,f126])).
% 4.23/1.10  fof(f127,plain,(
% 4.23/1.10    ( ! [X2,X3] : (k2_xboole_0(k1_tarski(X3),k1_tarski(X2)) = k2_tarski(X3,X2)) )),
% 4.23/1.10    inference(superposition,[],[f126,f22])).
% 4.23/1.10  fof(f137,plain,(
% 4.23/1.10    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK0,sK2))),
% 4.23/1.10    inference(backward_demodulation,[],[f20,f131])).
% 4.23/1.10  fof(f20,plain,(
% 4.23/1.10    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 4.23/1.10    inference(cnf_transformation,[],[f19])).
% 4.23/1.10  fof(f19,plain,(
% 4.23/1.10    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 4.23/1.10    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f18])).
% 4.23/1.10  fof(f18,plain,(
% 4.23/1.10    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 4.23/1.10    introduced(choice_axiom,[])).
% 4.23/1.10  fof(f17,plain,(
% 4.23/1.10    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 4.23/1.10    inference(ennf_transformation,[],[f16])).
% 4.23/1.10  fof(f16,negated_conjecture,(
% 4.23/1.10    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 4.23/1.10    inference(negated_conjecture,[],[f15])).
% 4.23/1.10  fof(f15,conjecture,(
% 4.23/1.10    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 4.23/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
% 4.23/1.10  % SZS output end Proof for theBenchmark
% 4.23/1.10  % (4873)------------------------------
% 4.23/1.10  % (4873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.23/1.10  % (4873)Termination reason: Refutation
% 4.23/1.10  
% 4.23/1.10  % (4873)Memory used [KB]: 11641
% 4.23/1.10  % (4873)Time elapsed: 0.511 s
% 4.23/1.10  % (4873)------------------------------
% 4.23/1.10  % (4873)------------------------------
% 4.23/1.11  % (4704)Success in time 0.744 s
%------------------------------------------------------------------------------
