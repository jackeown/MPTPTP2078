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
% DateTime   : Thu Dec  3 12:29:40 EST 2020

% Result     : Theorem 5.89s
% Output     : Refutation 5.89s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 193 expanded)
%              Number of leaves         :    7 (  64 expanded)
%              Depth                    :   18
%              Number of atoms          :   52 ( 194 expanded)
%              Number of equality atoms :   51 ( 193 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23465,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f23464])).

fof(f23464,plain,(
    k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f20750,f12])).

fof(f12,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f20750,plain,(
    k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k2_xboole_0(k3_xboole_0(sK1,sK2),sK0) ),
    inference(superposition,[],[f11,f19812])).

fof(f19812,plain,(
    ! [X6,X8,X7] : k3_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X6,X8)) = k2_xboole_0(k3_xboole_0(X7,X8),X6) ),
    inference(backward_demodulation,[],[f2527,f19806])).

fof(f19806,plain,(
    ! [X30,X28,X29] : k2_xboole_0(X28,k3_xboole_0(X29,k2_xboole_0(X28,X30))) = k2_xboole_0(k3_xboole_0(X29,X30),X28) ),
    inference(backward_demodulation,[],[f3756,f19788])).

fof(f19788,plain,(
    ! [X12,X13,X11] : k3_xboole_0(k2_xboole_0(X12,X11),k2_xboole_0(X11,X13)) = k2_xboole_0(k3_xboole_0(X13,X12),X11) ),
    inference(backward_demodulation,[],[f1180,f19787])).

fof(f19787,plain,(
    ! [X76,X77,X75] : k2_xboole_0(k3_xboole_0(X75,X76),X77) = k2_xboole_0(X77,k3_xboole_0(X75,k2_xboole_0(X76,X77))) ),
    inference(forward_demodulation,[],[f19536,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X2,X1)) = k2_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f16,f13])).

fof(f13,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f16,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f19536,plain,(
    ! [X76,X77,X75] : k2_xboole_0(k3_xboole_0(X75,X76),X77) = k2_xboole_0(X77,k2_xboole_0(k3_xboole_0(X75,X76),k3_xboole_0(X77,X75))) ),
    inference(superposition,[],[f4799,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
    inference(forward_demodulation,[],[f40,f17])).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[],[f14,f12])).

fof(f14,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f16,f22])).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[],[f14,f15])).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f4799,plain,(
    ! [X6,X4,X5] : k2_xboole_0(X5,X4) = k2_xboole_0(X4,k2_xboole_0(X5,k3_xboole_0(X4,k2_xboole_0(X5,X6)))) ),
    inference(forward_demodulation,[],[f4798,f1257])).

fof(f1257,plain,(
    ! [X10,X8,X9] : k2_xboole_0(X8,k3_xboole_0(X10,k2_xboole_0(X8,X9))) = k3_xboole_0(k2_xboole_0(X8,X9),k2_xboole_0(X10,X8)) ),
    inference(forward_demodulation,[],[f1200,f12])).

fof(f1200,plain,(
    ! [X10,X8,X9] : k3_xboole_0(k2_xboole_0(X8,X9),k2_xboole_0(X10,X8)) = k2_xboole_0(k3_xboole_0(X10,k2_xboole_0(X8,X9)),X8) ),
    inference(superposition,[],[f106,f14])).

fof(f106,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X2,X1)) = k2_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f23,f13])).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X0,X2)) ),
    inference(superposition,[],[f16,f13])).

fof(f4798,plain,(
    ! [X6,X4,X5] : k2_xboole_0(X5,X4) = k2_xboole_0(X4,k3_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X4,X5))) ),
    inference(forward_demodulation,[],[f4797,f14])).

fof(f4797,plain,(
    ! [X6,X4,X5] : k2_xboole_0(X4,k3_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X4,X5))) = k2_xboole_0(X5,k3_xboole_0(X4,k2_xboole_0(X4,k2_xboole_0(X5,X6)))) ),
    inference(forward_demodulation,[],[f4683,f13])).

fof(f4683,plain,(
    ! [X6,X4,X5] : k2_xboole_0(X4,k3_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X4,X5))) = k2_xboole_0(X5,k3_xboole_0(k2_xboole_0(X4,k2_xboole_0(X5,X6)),X4)) ),
    inference(superposition,[],[f103,f2526])).

fof(f2526,plain,(
    ! [X6,X8,X7] : k3_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X8,X6)) = k2_xboole_0(X6,k3_xboole_0(X7,k2_xboole_0(X6,X8))) ),
    inference(backward_demodulation,[],[f193,f2525])).

fof(f2525,plain,(
    ! [X30,X31,X29] : k2_xboole_0(X29,k3_xboole_0(k2_xboole_0(X29,X30),X31)) = k2_xboole_0(X29,k3_xboole_0(X30,k2_xboole_0(X29,X31))) ),
    inference(forward_demodulation,[],[f2438,f1179])).

fof(f1179,plain,(
    ! [X10,X8,X9] : k3_xboole_0(k2_xboole_0(X8,X9),k2_xboole_0(X8,X10)) = k2_xboole_0(X8,k3_xboole_0(X10,k2_xboole_0(X8,X9))) ),
    inference(superposition,[],[f106,f14])).

fof(f2438,plain,(
    ! [X30,X31,X29] : k2_xboole_0(X29,k3_xboole_0(k2_xboole_0(X29,X30),X31)) = k3_xboole_0(k2_xboole_0(X29,X31),k2_xboole_0(X29,X30)) ),
    inference(superposition,[],[f101,f13])).

fof(f101,plain,(
    ! [X6,X8,X7] : k3_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X6,X8)) = k2_xboole_0(X6,k3_xboole_0(k2_xboole_0(X6,X7),X8)) ),
    inference(superposition,[],[f23,f14])).

fof(f193,plain,(
    ! [X6,X8,X7] : k2_xboole_0(X6,k3_xboole_0(k2_xboole_0(X6,X7),X8)) = k3_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X8,X6)) ),
    inference(forward_demodulation,[],[f169,f12])).

fof(f169,plain,(
    ! [X6,X8,X7] : k2_xboole_0(k3_xboole_0(k2_xboole_0(X6,X7),X8),X6) = k3_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X8,X6)) ),
    inference(superposition,[],[f26,f14])).

fof(f103,plain,(
    ! [X14,X12,X15,X13] : k3_xboole_0(k2_xboole_0(X13,k2_xboole_0(X12,X14)),k2_xboole_0(X12,X15)) = k2_xboole_0(X12,k3_xboole_0(k2_xboole_0(X13,k2_xboole_0(X12,X14)),X15)) ),
    inference(superposition,[],[f23,f36])).

fof(f36,plain,(
    ! [X6,X8,X7] : k3_xboole_0(X6,k2_xboole_0(X8,k2_xboole_0(X6,X7))) = X6 ),
    inference(forward_demodulation,[],[f35,f15])).

fof(f35,plain,(
    ! [X6,X8,X7] : k2_xboole_0(X6,k3_xboole_0(X6,X8)) = k3_xboole_0(X6,k2_xboole_0(X8,k2_xboole_0(X6,X7))) ),
    inference(forward_demodulation,[],[f28,f12])).

fof(f28,plain,(
    ! [X6,X8,X7] : k3_xboole_0(X6,k2_xboole_0(X8,k2_xboole_0(X6,X7))) = k2_xboole_0(k3_xboole_0(X6,X8),X6) ),
    inference(superposition,[],[f16,f14])).

fof(f1180,plain,(
    ! [X12,X13,X11] : k3_xboole_0(k2_xboole_0(X12,X11),k2_xboole_0(X11,X13)) = k2_xboole_0(X11,k3_xboole_0(X13,k2_xboole_0(X12,X11))) ),
    inference(superposition,[],[f106,f17])).

fof(f3756,plain,(
    ! [X30,X28,X29] : k3_xboole_0(k2_xboole_0(X30,X28),k2_xboole_0(X28,X29)) = k2_xboole_0(X28,k3_xboole_0(X29,k2_xboole_0(X28,X30))) ),
    inference(superposition,[],[f2526,f13])).

fof(f2527,plain,(
    ! [X6,X8,X7] : k3_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X6,X8)) = k2_xboole_0(X6,k3_xboole_0(X7,k2_xboole_0(X6,X8))) ),
    inference(backward_demodulation,[],[f101,f2525])).

fof(f11,plain,(
    k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))
   => k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:10:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.41  % (29457)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.42  % (29466)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.20/0.42  % (29465)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.20/0.42  % (29467)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.20/0.43  % (29459)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.20/0.44  % (29462)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.45  % (29463)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.45  % (29461)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.45  % (29458)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.20/0.46  % (29464)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.46  % (29460)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.47  % (29456)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 4.97/1.02  % (29457)Time limit reached!
% 4.97/1.02  % (29457)------------------------------
% 4.97/1.02  % (29457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.97/1.02  % (29457)Termination reason: Time limit
% 4.97/1.02  % (29457)Termination phase: Saturation
% 4.97/1.02  
% 4.97/1.02  % (29457)Memory used [KB]: 28656
% 4.97/1.02  % (29457)Time elapsed: 0.600 s
% 4.97/1.02  % (29457)------------------------------
% 4.97/1.02  % (29457)------------------------------
% 5.89/1.12  % (29467)Refutation found. Thanks to Tanya!
% 5.89/1.12  % SZS status Theorem for theBenchmark
% 5.89/1.12  % SZS output start Proof for theBenchmark
% 5.89/1.12  fof(f23465,plain,(
% 5.89/1.12    $false),
% 5.89/1.12    inference(trivial_inequality_removal,[],[f23464])).
% 5.89/1.12  fof(f23464,plain,(
% 5.89/1.12    k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 5.89/1.12    inference(superposition,[],[f20750,f12])).
% 5.89/1.12  fof(f12,plain,(
% 5.89/1.12    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 5.89/1.12    inference(cnf_transformation,[],[f1])).
% 5.89/1.12  fof(f1,axiom,(
% 5.89/1.12    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 5.89/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 5.89/1.12  fof(f20750,plain,(
% 5.89/1.12    k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k2_xboole_0(k3_xboole_0(sK1,sK2),sK0)),
% 5.89/1.12    inference(superposition,[],[f11,f19812])).
% 5.89/1.12  fof(f19812,plain,(
% 5.89/1.12    ( ! [X6,X8,X7] : (k3_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X6,X8)) = k2_xboole_0(k3_xboole_0(X7,X8),X6)) )),
% 5.89/1.12    inference(backward_demodulation,[],[f2527,f19806])).
% 5.89/1.12  fof(f19806,plain,(
% 5.89/1.12    ( ! [X30,X28,X29] : (k2_xboole_0(X28,k3_xboole_0(X29,k2_xboole_0(X28,X30))) = k2_xboole_0(k3_xboole_0(X29,X30),X28)) )),
% 5.89/1.12    inference(backward_demodulation,[],[f3756,f19788])).
% 5.89/1.12  fof(f19788,plain,(
% 5.89/1.12    ( ! [X12,X13,X11] : (k3_xboole_0(k2_xboole_0(X12,X11),k2_xboole_0(X11,X13)) = k2_xboole_0(k3_xboole_0(X13,X12),X11)) )),
% 5.89/1.12    inference(backward_demodulation,[],[f1180,f19787])).
% 5.89/1.12  fof(f19787,plain,(
% 5.89/1.12    ( ! [X76,X77,X75] : (k2_xboole_0(k3_xboole_0(X75,X76),X77) = k2_xboole_0(X77,k3_xboole_0(X75,k2_xboole_0(X76,X77)))) )),
% 5.89/1.12    inference(forward_demodulation,[],[f19536,f26])).
% 5.89/1.12  fof(f26,plain,(
% 5.89/1.12    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X2,X1)) = k2_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(X1,X0))) )),
% 5.89/1.12    inference(superposition,[],[f16,f13])).
% 5.89/1.12  fof(f13,plain,(
% 5.89/1.12    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 5.89/1.12    inference(cnf_transformation,[],[f2])).
% 5.89/1.12  fof(f2,axiom,(
% 5.89/1.12    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 5.89/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 5.89/1.12  fof(f16,plain,(
% 5.89/1.12    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 5.89/1.12    inference(cnf_transformation,[],[f5])).
% 5.89/1.12  fof(f5,axiom,(
% 5.89/1.12    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 5.89/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).
% 5.89/1.12  fof(f19536,plain,(
% 5.89/1.12    ( ! [X76,X77,X75] : (k2_xboole_0(k3_xboole_0(X75,X76),X77) = k2_xboole_0(X77,k2_xboole_0(k3_xboole_0(X75,X76),k3_xboole_0(X77,X75)))) )),
% 5.89/1.12    inference(superposition,[],[f4799,f43])).
% 5.89/1.12  fof(f43,plain,(
% 5.89/1.12    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0) )),
% 5.89/1.12    inference(forward_demodulation,[],[f40,f17])).
% 5.89/1.12  fof(f17,plain,(
% 5.89/1.12    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0) )),
% 5.89/1.12    inference(superposition,[],[f14,f12])).
% 5.89/1.12  fof(f14,plain,(
% 5.89/1.12    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 5.89/1.12    inference(cnf_transformation,[],[f3])).
% 5.89/1.12  fof(f3,axiom,(
% 5.89/1.12    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 5.89/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 5.89/1.12  fof(f40,plain,(
% 5.89/1.12    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 5.89/1.12    inference(superposition,[],[f16,f22])).
% 5.89/1.12  fof(f22,plain,(
% 5.89/1.12    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 5.89/1.12    inference(superposition,[],[f14,f15])).
% 5.89/1.12  fof(f15,plain,(
% 5.89/1.12    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 5.89/1.12    inference(cnf_transformation,[],[f4])).
% 5.89/1.12  fof(f4,axiom,(
% 5.89/1.12    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 5.89/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 5.89/1.12  fof(f4799,plain,(
% 5.89/1.12    ( ! [X6,X4,X5] : (k2_xboole_0(X5,X4) = k2_xboole_0(X4,k2_xboole_0(X5,k3_xboole_0(X4,k2_xboole_0(X5,X6))))) )),
% 5.89/1.12    inference(forward_demodulation,[],[f4798,f1257])).
% 5.89/1.12  fof(f1257,plain,(
% 5.89/1.12    ( ! [X10,X8,X9] : (k2_xboole_0(X8,k3_xboole_0(X10,k2_xboole_0(X8,X9))) = k3_xboole_0(k2_xboole_0(X8,X9),k2_xboole_0(X10,X8))) )),
% 5.89/1.12    inference(forward_demodulation,[],[f1200,f12])).
% 5.89/1.12  fof(f1200,plain,(
% 5.89/1.12    ( ! [X10,X8,X9] : (k3_xboole_0(k2_xboole_0(X8,X9),k2_xboole_0(X10,X8)) = k2_xboole_0(k3_xboole_0(X10,k2_xboole_0(X8,X9)),X8)) )),
% 5.89/1.12    inference(superposition,[],[f106,f14])).
% 5.89/1.12  fof(f106,plain,(
% 5.89/1.12    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X2,X1)) = k2_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X1,X0))) )),
% 5.89/1.12    inference(superposition,[],[f23,f13])).
% 5.89/1.12  fof(f23,plain,(
% 5.89/1.12    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X0,X2))) )),
% 5.89/1.12    inference(superposition,[],[f16,f13])).
% 5.89/1.12  fof(f4798,plain,(
% 5.89/1.12    ( ! [X6,X4,X5] : (k2_xboole_0(X5,X4) = k2_xboole_0(X4,k3_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X4,X5)))) )),
% 5.89/1.12    inference(forward_demodulation,[],[f4797,f14])).
% 5.89/1.12  fof(f4797,plain,(
% 5.89/1.12    ( ! [X6,X4,X5] : (k2_xboole_0(X4,k3_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X4,X5))) = k2_xboole_0(X5,k3_xboole_0(X4,k2_xboole_0(X4,k2_xboole_0(X5,X6))))) )),
% 5.89/1.12    inference(forward_demodulation,[],[f4683,f13])).
% 5.89/1.12  fof(f4683,plain,(
% 5.89/1.12    ( ! [X6,X4,X5] : (k2_xboole_0(X4,k3_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X4,X5))) = k2_xboole_0(X5,k3_xboole_0(k2_xboole_0(X4,k2_xboole_0(X5,X6)),X4))) )),
% 5.89/1.12    inference(superposition,[],[f103,f2526])).
% 5.89/1.12  fof(f2526,plain,(
% 5.89/1.12    ( ! [X6,X8,X7] : (k3_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X8,X6)) = k2_xboole_0(X6,k3_xboole_0(X7,k2_xboole_0(X6,X8)))) )),
% 5.89/1.12    inference(backward_demodulation,[],[f193,f2525])).
% 5.89/1.12  fof(f2525,plain,(
% 5.89/1.12    ( ! [X30,X31,X29] : (k2_xboole_0(X29,k3_xboole_0(k2_xboole_0(X29,X30),X31)) = k2_xboole_0(X29,k3_xboole_0(X30,k2_xboole_0(X29,X31)))) )),
% 5.89/1.12    inference(forward_demodulation,[],[f2438,f1179])).
% 5.89/1.12  fof(f1179,plain,(
% 5.89/1.12    ( ! [X10,X8,X9] : (k3_xboole_0(k2_xboole_0(X8,X9),k2_xboole_0(X8,X10)) = k2_xboole_0(X8,k3_xboole_0(X10,k2_xboole_0(X8,X9)))) )),
% 5.89/1.12    inference(superposition,[],[f106,f14])).
% 5.89/1.12  fof(f2438,plain,(
% 5.89/1.12    ( ! [X30,X31,X29] : (k2_xboole_0(X29,k3_xboole_0(k2_xboole_0(X29,X30),X31)) = k3_xboole_0(k2_xboole_0(X29,X31),k2_xboole_0(X29,X30))) )),
% 5.89/1.12    inference(superposition,[],[f101,f13])).
% 5.89/1.12  fof(f101,plain,(
% 5.89/1.12    ( ! [X6,X8,X7] : (k3_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X6,X8)) = k2_xboole_0(X6,k3_xboole_0(k2_xboole_0(X6,X7),X8))) )),
% 5.89/1.12    inference(superposition,[],[f23,f14])).
% 5.89/1.12  fof(f193,plain,(
% 5.89/1.12    ( ! [X6,X8,X7] : (k2_xboole_0(X6,k3_xboole_0(k2_xboole_0(X6,X7),X8)) = k3_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X8,X6))) )),
% 5.89/1.12    inference(forward_demodulation,[],[f169,f12])).
% 5.89/1.12  fof(f169,plain,(
% 5.89/1.12    ( ! [X6,X8,X7] : (k2_xboole_0(k3_xboole_0(k2_xboole_0(X6,X7),X8),X6) = k3_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X8,X6))) )),
% 5.89/1.12    inference(superposition,[],[f26,f14])).
% 5.89/1.12  fof(f103,plain,(
% 5.89/1.12    ( ! [X14,X12,X15,X13] : (k3_xboole_0(k2_xboole_0(X13,k2_xboole_0(X12,X14)),k2_xboole_0(X12,X15)) = k2_xboole_0(X12,k3_xboole_0(k2_xboole_0(X13,k2_xboole_0(X12,X14)),X15))) )),
% 5.89/1.12    inference(superposition,[],[f23,f36])).
% 5.89/1.12  fof(f36,plain,(
% 5.89/1.12    ( ! [X6,X8,X7] : (k3_xboole_0(X6,k2_xboole_0(X8,k2_xboole_0(X6,X7))) = X6) )),
% 5.89/1.12    inference(forward_demodulation,[],[f35,f15])).
% 5.89/1.12  fof(f35,plain,(
% 5.89/1.12    ( ! [X6,X8,X7] : (k2_xboole_0(X6,k3_xboole_0(X6,X8)) = k3_xboole_0(X6,k2_xboole_0(X8,k2_xboole_0(X6,X7)))) )),
% 5.89/1.12    inference(forward_demodulation,[],[f28,f12])).
% 5.89/1.12  fof(f28,plain,(
% 5.89/1.12    ( ! [X6,X8,X7] : (k3_xboole_0(X6,k2_xboole_0(X8,k2_xboole_0(X6,X7))) = k2_xboole_0(k3_xboole_0(X6,X8),X6)) )),
% 5.89/1.12    inference(superposition,[],[f16,f14])).
% 5.89/1.12  fof(f1180,plain,(
% 5.89/1.12    ( ! [X12,X13,X11] : (k3_xboole_0(k2_xboole_0(X12,X11),k2_xboole_0(X11,X13)) = k2_xboole_0(X11,k3_xboole_0(X13,k2_xboole_0(X12,X11)))) )),
% 5.89/1.12    inference(superposition,[],[f106,f17])).
% 5.89/1.12  fof(f3756,plain,(
% 5.89/1.12    ( ! [X30,X28,X29] : (k3_xboole_0(k2_xboole_0(X30,X28),k2_xboole_0(X28,X29)) = k2_xboole_0(X28,k3_xboole_0(X29,k2_xboole_0(X28,X30)))) )),
% 5.89/1.12    inference(superposition,[],[f2526,f13])).
% 5.89/1.12  fof(f2527,plain,(
% 5.89/1.12    ( ! [X6,X8,X7] : (k3_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X6,X8)) = k2_xboole_0(X6,k3_xboole_0(X7,k2_xboole_0(X6,X8)))) )),
% 5.89/1.12    inference(backward_demodulation,[],[f101,f2525])).
% 5.89/1.12  fof(f11,plain,(
% 5.89/1.12    k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),
% 5.89/1.12    inference(cnf_transformation,[],[f10])).
% 5.89/1.12  fof(f10,plain,(
% 5.89/1.12    k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),
% 5.89/1.12    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f9])).
% 5.89/1.12  fof(f9,plain,(
% 5.89/1.12    ? [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) => k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),
% 5.89/1.12    introduced(choice_axiom,[])).
% 5.89/1.12  fof(f8,plain,(
% 5.89/1.12    ? [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 5.89/1.12    inference(ennf_transformation,[],[f7])).
% 5.89/1.12  fof(f7,negated_conjecture,(
% 5.89/1.12    ~! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 5.89/1.12    inference(negated_conjecture,[],[f6])).
% 5.89/1.12  fof(f6,conjecture,(
% 5.89/1.12    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 5.89/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).
% 5.89/1.12  % SZS output end Proof for theBenchmark
% 5.89/1.12  % (29467)------------------------------
% 5.89/1.12  % (29467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.89/1.12  % (29467)Termination reason: Refutation
% 5.89/1.12  
% 5.89/1.12  % (29467)Memory used [KB]: 32877
% 5.89/1.12  % (29467)Time elapsed: 0.712 s
% 5.89/1.12  % (29467)------------------------------
% 5.89/1.12  % (29467)------------------------------
% 5.89/1.13  % (29455)Success in time 0.777 s
%------------------------------------------------------------------------------
