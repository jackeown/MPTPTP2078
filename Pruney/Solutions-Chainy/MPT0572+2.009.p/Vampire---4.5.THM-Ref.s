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
% DateTime   : Thu Dec  3 12:50:40 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 130 expanded)
%              Number of leaves         :   12 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :   72 ( 166 expanded)
%              Number of equality atoms :   29 (  90 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4494,plain,(
    $false ),
    inference(resolution,[],[f4483,f4242])).

fof(f4242,plain,(
    ! [X4,X5] : r1_tarski(k10_relat_1(sK2,k3_xboole_0(X5,X4)),k10_relat_1(sK2,X5)) ),
    inference(superposition,[],[f3080,f3963])).

fof(f3963,plain,(
    ! [X0,X1] : k3_xboole_0(k2_xboole_0(X1,X0),X0) = X0 ),
    inference(forward_demodulation,[],[f3962,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f3962,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f3961,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).

fof(f3961,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_xboole_0(X1,X0),k3_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f3841,f400])).

fof(f400,plain,(
    ! [X10,X8,X9] : k2_xboole_0(X8,X9) = k2_xboole_0(k2_xboole_0(X8,X9),k3_xboole_0(X10,X8)) ),
    inference(superposition,[],[f271,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f271,plain,(
    ! [X4,X5,X3] : k2_xboole_0(X3,k3_xboole_0(X5,k3_xboole_0(X4,X3))) = X3 ),
    inference(forward_demodulation,[],[f270,f26])).

fof(f270,plain,(
    ! [X4,X5,X3] : k3_xboole_0(X3,k2_xboole_0(X3,X5)) = k2_xboole_0(X3,k3_xboole_0(X5,k3_xboole_0(X4,X3))) ),
    inference(forward_demodulation,[],[f235,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f235,plain,(
    ! [X4,X5,X3] : k2_xboole_0(X3,k3_xboole_0(X5,k3_xboole_0(X4,X3))) = k3_xboole_0(k2_xboole_0(X3,X5),X3) ),
    inference(superposition,[],[f29,f36])).

fof(f36,plain,(
    ! [X2,X1] : k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1 ),
    inference(superposition,[],[f25,f24])).

fof(f3841,plain,(
    ! [X0,X1] : k3_xboole_0(k2_xboole_0(X1,X0),k3_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f34,f23])).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f34,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k2_xboole_0(X2,X0),k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2))) ),
    inference(forward_demodulation,[],[f31,f24])).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_xboole_1)).

fof(f3080,plain,(
    ! [X12,X13,X11] : r1_tarski(k10_relat_1(sK2,k3_xboole_0(X11,X12)),k10_relat_1(sK2,k3_xboole_0(k2_xboole_0(X12,X13),X11))) ),
    inference(superposition,[],[f2675,f24])).

fof(f2675,plain,(
    ! [X50,X51,X49] : r1_tarski(k10_relat_1(sK2,k3_xboole_0(X49,X50)),k10_relat_1(sK2,k3_xboole_0(X49,k2_xboole_0(X50,X51)))) ),
    inference(superposition,[],[f2610,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f2610,plain,(
    ! [X15,X16] : r1_tarski(k10_relat_1(sK2,X15),k10_relat_1(sK2,k2_xboole_0(X15,X16))) ),
    inference(superposition,[],[f41,f2602])).

fof(f2602,plain,(
    ! [X0,X1] : k10_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) ),
    inference(resolution,[],[f32,f21])).

fof(f21,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_relat_1)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f27,f23])).

fof(f27,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).

fof(f4483,plain,(
    ~ r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k10_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f4241,f141])).

fof(f141,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k10_relat_1(sK2,sK1))
    | ~ r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k10_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f33,f22])).

fof(f22,plain,(
    ~ r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f4241,plain,(
    ! [X2,X3] : r1_tarski(k10_relat_1(sK2,k3_xboole_0(X2,X3)),k10_relat_1(sK2,X3)) ),
    inference(superposition,[],[f3278,f3963])).

fof(f3278,plain,(
    ! [X12,X13,X11] : r1_tarski(k10_relat_1(sK2,k3_xboole_0(X12,X11)),k10_relat_1(sK2,k3_xboole_0(k2_xboole_0(X12,X13),X11))) ),
    inference(superposition,[],[f3047,f24])).

fof(f3047,plain,(
    ! [X4,X2,X3] : r1_tarski(k10_relat_1(sK2,k3_xboole_0(X3,X2)),k10_relat_1(sK2,k3_xboole_0(X2,k2_xboole_0(X3,X4)))) ),
    inference(superposition,[],[f2675,f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:46:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.44  % (7668)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.44  % (7667)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.44  % (7669)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.44  % (7666)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.49  % (7662)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.22/0.49  % (7664)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.22/0.49  % (7665)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.22/0.50  % (7670)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.22/0.50  % (7673)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.22/0.50  % (7672)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.22/0.50  % (7671)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.22/0.50  % (7663)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 1.35/0.55  % (7666)Refutation found. Thanks to Tanya!
% 1.35/0.55  % SZS status Theorem for theBenchmark
% 1.35/0.55  % SZS output start Proof for theBenchmark
% 1.35/0.55  fof(f4494,plain,(
% 1.35/0.55    $false),
% 1.35/0.55    inference(resolution,[],[f4483,f4242])).
% 1.35/0.55  fof(f4242,plain,(
% 1.35/0.55    ( ! [X4,X5] : (r1_tarski(k10_relat_1(sK2,k3_xboole_0(X5,X4)),k10_relat_1(sK2,X5))) )),
% 1.35/0.55    inference(superposition,[],[f3080,f3963])).
% 1.35/0.55  fof(f3963,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k3_xboole_0(k2_xboole_0(X1,X0),X0) = X0) )),
% 1.35/0.55    inference(forward_demodulation,[],[f3962,f25])).
% 1.35/0.55  fof(f25,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.35/0.55    inference(cnf_transformation,[],[f5])).
% 1.35/0.55  fof(f5,axiom,(
% 1.35/0.55    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 1.35/0.55  fof(f3962,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 1.35/0.55    inference(forward_demodulation,[],[f3961,f29])).
% 1.35/0.55  fof(f29,plain,(
% 1.35/0.55    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 1.35/0.55    inference(cnf_transformation,[],[f7])).
% 1.35/0.55  fof(f7,axiom,(
% 1.35/0.55    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).
% 1.35/0.55  fof(f3961,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_xboole_0(X1,X0),k3_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,X1)))) )),
% 1.35/0.55    inference(forward_demodulation,[],[f3841,f400])).
% 1.35/0.55  fof(f400,plain,(
% 1.35/0.55    ( ! [X10,X8,X9] : (k2_xboole_0(X8,X9) = k2_xboole_0(k2_xboole_0(X8,X9),k3_xboole_0(X10,X8))) )),
% 1.35/0.55    inference(superposition,[],[f271,f26])).
% 1.35/0.55  fof(f26,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 1.35/0.55    inference(cnf_transformation,[],[f4])).
% 1.35/0.55  fof(f4,axiom,(
% 1.35/0.55    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 1.35/0.55  fof(f271,plain,(
% 1.35/0.55    ( ! [X4,X5,X3] : (k2_xboole_0(X3,k3_xboole_0(X5,k3_xboole_0(X4,X3))) = X3) )),
% 1.35/0.55    inference(forward_demodulation,[],[f270,f26])).
% 1.35/0.55  fof(f270,plain,(
% 1.35/0.55    ( ! [X4,X5,X3] : (k3_xboole_0(X3,k2_xboole_0(X3,X5)) = k2_xboole_0(X3,k3_xboole_0(X5,k3_xboole_0(X4,X3)))) )),
% 1.35/0.55    inference(forward_demodulation,[],[f235,f24])).
% 1.35/0.55  fof(f24,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f1])).
% 1.35/0.55  fof(f1,axiom,(
% 1.35/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.35/0.55  fof(f235,plain,(
% 1.35/0.55    ( ! [X4,X5,X3] : (k2_xboole_0(X3,k3_xboole_0(X5,k3_xboole_0(X4,X3))) = k3_xboole_0(k2_xboole_0(X3,X5),X3)) )),
% 1.35/0.55    inference(superposition,[],[f29,f36])).
% 1.35/0.55  fof(f36,plain,(
% 1.35/0.55    ( ! [X2,X1] : (k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1) )),
% 1.35/0.55    inference(superposition,[],[f25,f24])).
% 1.35/0.55  fof(f3841,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k3_xboole_0(k2_xboole_0(X1,X0),k3_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X1,X0))) )),
% 1.35/0.55    inference(superposition,[],[f34,f23])).
% 1.35/0.55  fof(f23,plain,(
% 1.35/0.55    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.35/0.55    inference(cnf_transformation,[],[f14])).
% 1.35/0.55  fof(f14,plain,(
% 1.35/0.55    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.35/0.55    inference(rectify,[],[f2])).
% 1.35/0.55  fof(f2,axiom,(
% 1.35/0.55    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.35/0.55  fof(f34,plain,(
% 1.35/0.55    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k2_xboole_0(X2,X0),k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)))) )),
% 1.35/0.55    inference(forward_demodulation,[],[f31,f24])).
% 1.35/0.55  fof(f31,plain,(
% 1.35/0.55    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0))) )),
% 1.35/0.55    inference(cnf_transformation,[],[f8])).
% 1.35/0.55  fof(f8,axiom,(
% 1.35/0.55    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_xboole_1)).
% 1.35/0.55  fof(f3080,plain,(
% 1.35/0.55    ( ! [X12,X13,X11] : (r1_tarski(k10_relat_1(sK2,k3_xboole_0(X11,X12)),k10_relat_1(sK2,k3_xboole_0(k2_xboole_0(X12,X13),X11)))) )),
% 1.35/0.55    inference(superposition,[],[f2675,f24])).
% 1.35/0.55  fof(f2675,plain,(
% 1.35/0.55    ( ! [X50,X51,X49] : (r1_tarski(k10_relat_1(sK2,k3_xboole_0(X49,X50)),k10_relat_1(sK2,k3_xboole_0(X49,k2_xboole_0(X50,X51))))) )),
% 1.35/0.55    inference(superposition,[],[f2610,f30])).
% 1.35/0.55  fof(f30,plain,(
% 1.35/0.55    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 1.35/0.55    inference(cnf_transformation,[],[f6])).
% 1.35/0.55  fof(f6,axiom,(
% 1.35/0.55    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).
% 1.35/0.55  fof(f2610,plain,(
% 1.35/0.55    ( ! [X15,X16] : (r1_tarski(k10_relat_1(sK2,X15),k10_relat_1(sK2,k2_xboole_0(X15,X16)))) )),
% 1.35/0.55    inference(superposition,[],[f41,f2602])).
% 1.35/0.55  fof(f2602,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k10_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) )),
% 1.35/0.55    inference(resolution,[],[f32,f21])).
% 1.35/0.55  fof(f21,plain,(
% 1.35/0.55    v1_relat_1(sK2)),
% 1.35/0.55    inference(cnf_transformation,[],[f20])).
% 1.35/0.55  fof(f20,plain,(
% 1.35/0.55    ~r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) & v1_relat_1(sK2)),
% 1.35/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f19])).
% 1.35/0.55  fof(f19,plain,(
% 1.35/0.55    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) & v1_relat_1(X2)) => (~r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) & v1_relat_1(sK2))),
% 1.35/0.55    introduced(choice_axiom,[])).
% 1.35/0.55  fof(f15,plain,(
% 1.35/0.55    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) & v1_relat_1(X2))),
% 1.35/0.55    inference(ennf_transformation,[],[f13])).
% 1.35/0.55  fof(f13,negated_conjecture,(
% 1.35/0.55    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 1.35/0.55    inference(negated_conjecture,[],[f12])).
% 1.35/0.55  fof(f12,conjecture,(
% 1.35/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_relat_1)).
% 1.35/0.55  fof(f32,plain,(
% 1.35/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 1.35/0.55    inference(cnf_transformation,[],[f16])).
% 1.35/0.55  fof(f16,plain,(
% 1.35/0.55    ! [X0,X1,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.35/0.55    inference(ennf_transformation,[],[f11])).
% 1.35/0.55  fof(f11,axiom,(
% 1.35/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).
% 1.35/0.55  fof(f41,plain,(
% 1.35/0.55    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.35/0.55    inference(superposition,[],[f27,f23])).
% 1.35/0.55  fof(f27,plain,(
% 1.35/0.55    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 1.35/0.55    inference(cnf_transformation,[],[f9])).
% 1.35/0.55  fof(f9,axiom,(
% 1.35/0.55    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).
% 1.35/0.55  fof(f4483,plain,(
% 1.35/0.55    ~r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k10_relat_1(sK2,sK0))),
% 1.35/0.55    inference(resolution,[],[f4241,f141])).
% 1.35/0.55  fof(f141,plain,(
% 1.35/0.55    ~r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k10_relat_1(sK2,sK1)) | ~r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k10_relat_1(sK2,sK0))),
% 1.35/0.55    inference(resolution,[],[f33,f22])).
% 1.35/0.55  fof(f22,plain,(
% 1.35/0.55    ~r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),
% 1.35/0.55    inference(cnf_transformation,[],[f20])).
% 1.35/0.55  fof(f33,plain,(
% 1.35/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f18])).
% 1.35/0.55  fof(f18,plain,(
% 1.35/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.35/0.55    inference(flattening,[],[f17])).
% 1.35/0.55  fof(f17,plain,(
% 1.35/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.35/0.55    inference(ennf_transformation,[],[f3])).
% 1.35/0.55  fof(f3,axiom,(
% 1.35/0.55    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.35/0.55  fof(f4241,plain,(
% 1.35/0.55    ( ! [X2,X3] : (r1_tarski(k10_relat_1(sK2,k3_xboole_0(X2,X3)),k10_relat_1(sK2,X3))) )),
% 1.35/0.55    inference(superposition,[],[f3278,f3963])).
% 1.35/0.55  fof(f3278,plain,(
% 1.35/0.55    ( ! [X12,X13,X11] : (r1_tarski(k10_relat_1(sK2,k3_xboole_0(X12,X11)),k10_relat_1(sK2,k3_xboole_0(k2_xboole_0(X12,X13),X11)))) )),
% 1.35/0.55    inference(superposition,[],[f3047,f24])).
% 1.35/0.55  fof(f3047,plain,(
% 1.35/0.55    ( ! [X4,X2,X3] : (r1_tarski(k10_relat_1(sK2,k3_xboole_0(X3,X2)),k10_relat_1(sK2,k3_xboole_0(X2,k2_xboole_0(X3,X4))))) )),
% 1.35/0.55    inference(superposition,[],[f2675,f24])).
% 1.35/0.55  % SZS output end Proof for theBenchmark
% 1.35/0.55  % (7666)------------------------------
% 1.35/0.55  % (7666)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (7666)Termination reason: Refutation
% 1.35/0.55  
% 1.35/0.55  % (7666)Memory used [KB]: 9466
% 1.35/0.55  % (7666)Time elapsed: 0.106 s
% 1.35/0.55  % (7666)------------------------------
% 1.35/0.55  % (7666)------------------------------
% 1.35/0.55  % (7661)Success in time 0.179 s
%------------------------------------------------------------------------------
